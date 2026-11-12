/*
 * umasim.js — 1人走行のレース計算エンジン（獲得バ身の試算用）
 *
 * 他のウマ娘がいない状態で1人だけ走らせ、スキルあり／なしのゴール到達時間の差をバ身（1バ身=2.5m）に換算する。
 * 計算式はコミュニティで解析・公開されているレース仕様をもとにした近似で、次の要素は扱わない：
 *   位置取り・ポジションキープ・掛かり・ブロック・追い比べ・賢さによる速度の揺らぎ・コースの補正ステータス。
 * 順位や他のウマ娘との距離が条件のスキルは「条件を満たした」とみなして計算する。
 *
 * ブラウザでは window.UmaSim、Node では module.exports で使う。
 */
(function (root, factory) {
  if (typeof module === "object" && module.exports) module.exports = factory();
  else root.UmaSim = factory();
})(typeof self !== "undefined" ? self : this, function () {
  "use strict";

  const STYLE_IDX = { 逃げ: 0, 先行: 1, 差し: 2, 追込: 3 };
  const STRAT_SPEED = [[1.0, 0.98, 0.962], [0.978, 0.991, 0.975], [0.938, 0.998, 0.994], [0.931, 1.0, 1.0]];
  const STRAT_ACCEL = [[1.0, 1.0, 0.996], [0.985, 1.0, 0.996], [0.975, 1.0, 1.0], [0.945, 1.0, 0.997]];
  const STRAT_HP = [0.95, 0.89, 1.0, 0.995];
  const DIST_SPEED = { S: 1.05, A: 1.0, B: 0.9, C: 0.8, D: 0.6, E: 0.4, F: 0.2, G: 0.1 };
  const DIST_ACCEL = { S: 1.0, A: 1.0, B: 1.0, C: 1.0, D: 1.0, E: 0.6, F: 0.5, G: 0.4 };
  const SURF_ACCEL = { S: 1.05, A: 1.0, B: 0.9, C: 0.8, D: 0.7, E: 0.5, F: 0.3, G: 0.1 };
  const MOOD = { 絶好調: 1.04, 好調: 1.02, 普通: 1.0, 不調: 0.98, 絶不調: 0.96 };
  // バ場状態によるステータス補正 [スピード, パワー] と、スタミナ消費の係数
  const GROUND_MOD = {
    芝: { 良: [0, 0, 1.0], 稍重: [0, -50, 1.0], 重: [0, -50, 1.02], 不良: [-50, -50, 1.02] },
    ダート: { 良: [0, -100, 1.0], 稍重: [0, -50, 1.0], 重: [0, -100, 1.01], 不良: [-50, -100, 1.02] },
  };
  const DECEL = [-1.2, -0.8, -1.0, -1.0];
  const DT = 1 / 15;
  const BASHIN_M = 2.5;

  const DIST_CODE = { 短: 1, マイル: 2, 中: 3, 長: 4 };
  const SURF_CODE = { 芝: 1, ダート: 2 };
  const ROT_CODE = { 右: 1, 左: 2 };
  const GROUND_CODE = { 良: 1, 稍重: 2, 重: 3, 不良: 4 };
  const WEATHER_CODE = { 晴: 1, 曇: 2, 雨: 3, 雪: 4 };
  const SEASON_CODE = { 春: 1, 夏: 2, 秋: 3, 冬: 4 };
  const MOTIVATION = { 絶不調: 1, 不調: 2, 普通: 3, 好調: 4, 絶好調: 5 };
  const STYLE_NAMES = ["逃げ", "先行", "差し", "追込"];
  // 掛かり：発動率（賢さ）と、3秒ごと55%で解除・最大12秒の持続の期待値
  // 位置取りの目安：脚質の並び（逃げ→先行→差し→追込）で、自分が何番手あたりにいるかを幅で持つ
  const DEFAULT_OTHERS = { 逃げ: 2, 先行: 3, 差し: 2, 追込: 1 };
  // リード確保（区間11〜15）：KuromiAK「Race Mechanics」記載の係数。1回あたりの消費の基準値は式が非公開のため設定値（secureLeadBase）
  const SL_STYLE_HP = [1.0, 0.8, 0.8, 0];
  const slDistCoef = (D) => (D < 1401 ? 0.3 : D < 1801 ? 0.3 : D < 2101 ? 0.5 : D < 2201 ? 0.8 : D < 2401 ? 1.0 : D < 2601 ? 1.1 : 1.2);
  // 2秒ごとに20%で発動、発動後は2秒＋待ち1秒のあいだ判定なし → 判定1回あたりの期待発動数
  const SL_PER_CHECK = 0.2 / (1 + 0.2 * 1.5);
  // 持久力温存：完走に要る体力の1.035〜1.04倍を残そうとする（同資料）。中央値を使う
  const CONSERVE_TARGET = 1.0375;
  function positionModel(style, field) {
    const others = (field && (field.counts || field.defaultCounts)) || DEFAULT_OTHERS;
    const order = ["逃げ", "先行", "差し", "追込"];
    const me = order[style];
    let ahead = 0;
    for (let i = 0; i < style; i++) ahead += others[order[i]] || 0;
    const same = others[me] || 0;
    const N = 1 + order.reduce((a, k) => a + (others[k] || 0), 0);
    return { N, lo: ahead + 1, hi: ahead + 1 + same, assumed: !(field && field.counts) };
  }
  // 順位や前後の状況が条件のものの成立確率（目安）。分からないものは null
  const OVERTAKE_P = [0.2, 0.5, 0.8, 0.8], DOWN_P = [0.5, 0.4, 0.2, 0.1];
  const GAP_TOP = [[0, 3], [3, 10], [8, 20], [15, 30]];
  function positionProb(ctx, key, sign, v) {
    const { N, lo, hi } = ctx.pos;
    const share = (test) => { let n = 0; for (let o = lo; o <= hi; o++) if (test(o)) n++; return n / (hi - lo + 1); };
    const st = ctx.style;
    switch (key) {
      case "order": return share((o) => cmp(o, sign, v));
      case "order_rate": return share((o) => cmp((o / N) * 100, sign, v));
      case "order_rate_in20_continue": return share((o) => (o / N) * 100 <= 20);
      case "order_rate_in40_continue": return share((o) => (o / N) * 100 <= 40);
      case "order_rate_in50_continue": return share((o) => (o / N) * 100 <= 50);
      case "order_rate_in80_continue": return share((o) => (o / N) * 100 <= 80);
      case "order_rate_out40_continue": return share((o) => (o / N) * 100 > 40);
      case "distance_diff_top": case "distance_diff_top_float": {
        const [a, b] = GAP_TOP[st]; let n = 0; for (let g = a; g <= b; g++) if (cmp(g, sign, v)) n++; return n / (b - a + 1);
      }
      case "is_overtake": case "overtake_target_time": case "changeOrderUp":
      case "change_order_up_end_after": case "change_order_up_middle": case "change_order_up_finalcorner_after":
        return OVERTAKE_P[st];
      case "changeOrderDown": return DOWN_P[st];
      case "bashin_diff_infront": case "bashin_diff_behind": return 0.7;
      case "near_count": return v <= 1 ? 0.7 : v === 2 ? 0.5 : 0.3;
      case "blocked_front": case "blocked_side_continuetime": case "blocked_front_continuetime": case "is_surrounded": return 0.3;
      case "infront_near_lane_time": case "behind_near_lane_time": case "is_behind_in": case "visiblehorse": case "near_infront_count": return 0.5;
      default: return null;
    }
  }
  // 順位・先頭との差の条件は、脚質どおりに走って届く範囲にあれば「狙って満たせる」として成立扱いにする（options.posMode = "style"）。
  // 届かない条件（差しで1番手など）は不成立のまま。追い抜き・ブロックなど相手次第の条件は成立率のまま
  const STYLE_KEYS = /^(order|order_rate|distance_diff_top)/;
  function styleFit(ctx, key, pp) {
    if (pp == null || ctx.opts.posMode !== "style" || !STYLE_KEYS.test(key)) return pp;
    return pp > 0 ? 1 : 0;
  }
  const rushedChance = (wit) => Math.min(1, Math.pow(6.5 / Math.log10(0.1 * wit + 1), 2) / 100);
  const RUSHED_EXPECTED_SEC = 3 * 0.55 + 6 * 0.45 * 0.55 + 9 * 0.45 * 0.45 * 0.55 + 12 * 0.45 * 0.45 * 0.45;

  const distCat = (d) => (d <= 1400 ? "短" : d <= 1800 ? "マイル" : d <= 2400 ? "中" : "長");
  const cmp = (a, sign, b) => {
    switch (sign) {
      case "==": return a == b;
      case "!=": return a != b;
      case ">=": return a >= b;
      case "<=": return a <= b;
      case ">": return a > b;
      case "<": return a < b;
      default: return true;
    }
  };

  /* ---------- 区間（[開始m, 終了m] の配列）の操作 ---------- */
  const norm = (ivs) => ivs.filter(([a, b]) => b > a).sort((x, y) => x[0] - y[0]);
  function intersect(A, B) {
    const out = [];
    for (const [a1, b1] of A) for (const [a2, b2] of B) {
      const a = Math.max(a1, a2), b = Math.min(b1, b2);
      if (b > a) out.push([a, b]);
    }
    return norm(out);
  }
  function complement(A, D) {
    const out = []; let cur = 0;
    for (const [a, b] of norm(A)) { if (a > cur) out.push([cur, a]); cur = Math.max(cur, b); }
    if (cur < D) out.push([cur, D]);
    return out;
  }
  const totalLen = (A) => A.reduce((s, [a, b]) => s + (b - a), 0);
  function pointAt(A, frac) {
    let r = totalLen(A) * frac;
    for (const [a, b] of A) { if (r <= b - a) return a + r; r -= b - a; }
    return A.length ? A[A.length - 1][1] : 0;
  }

  /* ---------- レース条件の準備 ---------- */
  function buildContext(input) {
    const { course, cond = {}, uma } = input;
    const D = course.dist;
    const style = STYLE_IDX[uma.style] ?? 2;
    const mood = MOOD[uma.mood] ?? 1;
    const gm = (GROUND_MOD[course.surface] || GROUND_MOD["芝"])[cond.ground || "良"] || [0, 0, 1];
    const raw = Object.assign({ spd: 1200, sta: 1000, pow: 1000, gut: 600, wit: 1000 }, uma.stats || {});
    const fix = (v) => { v = v * mood; return v > 1200 ? 1200 + (v - 1200) / 2 : v; };
    const base = { spd: fix(raw.spd), sta: fix(raw.sta), pow: fix(raw.pow), gut: fix(raw.gut), wit: fix(raw.wit) };
    // コースの補正ステータス：指定ステータスの値に応じた倍率（複数ある場合は平均）をスピードに掛ける
    const STAT_KEY = { スピード: "spd", スタミナ: "sta", パワー: "pow", 根性: "gut", 賢さ: "wit" };
    const bonusStats = (course.statBonus || []).map((n) => STAT_KEY[n]).filter(Boolean);
    const step = (v) => (v <= 300 ? 0.05 : v <= 600 ? 0.1 : v <= 900 ? 0.15 : 0.2);
    const courseMod = bonusStats.length ? 1 + bonusStats.reduce((a, k) => a + step(base[k]), 0) / bonusStats.length : 1;
    const stats = {
      spd: Math.max(1, base.spd * courseMod + gm[0]), sta: base.sta, pow: Math.max(1, base.pow + gm[1]),
      gut: base.gut, wit: base.wit,
    };
    const sections = (course.sections || []).map((s) => ({ ...s }));
    const corners = sections.filter((s) => s.kind === "corner").map((s) => [s.start, s.end, s.no]);
    const straights = sections.filter((s) => s.kind === "straight").map((s) => [s.start, s.end]);
    const lastStraight = straights.length ? straights[straights.length - 1] : [D - 300, D];
    const finalCorner = corners.length ? corners[corners.length - 1] : null;
    const phaseIv = [[0, D / 6], [D / 6, (D * 2) / 3], [(D * 2) / 3, (D * 5) / 6], [(D * 5) / 6, D]];
    const ups = (course.slopes || []).filter((s) => s.grade > 0).map((s) => [s.start, s.end, s.grade]);
    const downs = (course.slopes || []).filter((s) => s.grade < 0).map((s) => [s.start, s.end, s.grade]);
    const trackId = course.trackId || (course.id ? 10000 + Math.floor((Number(course.id) % 10000) / 100) : 0);
    return {
      D, style, stats, courseMod, apt: Object.assign({ dist: "A", surf: "A", style: "A" }, uma.apt || {}),
      field: input.field || null, mood: uma.mood || "絶好調",
      pos: positionModel(style, input.field),
      // 掛かり・下り坂加速は「期待値」で織り込む（options.rushed: "expected" | "none" | "always"）
      opts: Object.assign({ rushed: "expected", downhill: true, witNoise: true, conserveMargin: 0, secureLeadBase: 0, posExtra: null }, input.options || {}),
      // 位置取り争い（逃げのみ）：ほかに逃げがいれば起きる扱い。リード確保：後ろにいるべき脚質がいれば起きうる
      comp: (() => {
        const others = (input.field && (input.field.counts || input.field.defaultCounts)) || DEFAULT_OTHERS;
        const behind = STYLE_NAMES.slice(style + 1).reduce((a, k) => a + (others[k] || 0), 0);
        return { spot: style === 0 && (others["逃げ"] || 0) >= 1, lead: style <= 2 && behind > 0 };
      })(),
      // 全開スパート（仮モデル）：スピードの基礎値（やる気込み・半減前）が2001以上で、オプションを有効にしたときだけ使う
      ft: (() => {
        const o = (input.options && input.options.fullThrottle) || {};
        const on = !!o.enabled && (o.maxGain || 0) > 0 && raw.spd * mood >= 2001;
        return { on, maxGain: o.maxGain || 0, coef: o.coef ?? 0.1 };
      })(),
      hpCoef: gm[2], V0: 20 - (D - 2000) / 1000,
      course, cond, trackId, corners, straights, lastStraight, finalCorner, phaseIv, ups, downs,
      race: {
        distance_type: DIST_CODE[distCat(D)], ground_type: SURF_CODE[course.surface] || 1,
        rotation: ROT_CODE[course.dir] || 0, ground_condition: GROUND_CODE[cond.ground || "良"],
        weather: WEATHER_CODE[cond.weather || "晴"], season: SEASON_CODE[cond.season || "春"],
        running_style: style + 1, track_id: trackId, course_distance: D, is_basis_distance: D % 400 === 0 ? 1 : 0,
      },
    };
  }

  /* ---------- スキルの発動位置 ---------- */
  // 1つの条件グループから、発動しうる区間と「ランダム位置か」を求める。発動不可なら null。
  function groupRegion(ctx, group) {
    const { D, phaseIv } = ctx;
    let region = [[0, D]];
    let random = false;
    let unknown = [];
    let prob = 1;
    let ft = false, dep = false;
    const posKeys = [];
    const lim = (ivs) => { region = intersect(region, norm(ivs)); };
    for (const [key, list] of Object.entries(group)) {
      // 値を持たない補助キー
      if (Array.isArray(list) && !list.length) {
        if (key === "notCorner") lim(complement(ctx.corners.map(([a, b]) => [a, b]), D));
        else if (key === "finalCornerOver" && ctx.finalCorner) lim([[ctx.finalCorner[1], D]]);
        else if (key === "notFinalCorner" && ctx.finalCorner) lim(complement([[ctx.finalCorner[0], ctx.finalCorner[1]]], D));
        else if (key === "finalStraight") lim([ctx.lastStraight]);
        else if (key === "changeOrderUp" || key === "changeOrderDown") { const pp = positionProb(ctx, key, "==", 1); prob *= pp; posKeys.push(key); }
        else if (key === "nobodySameRunningStyle") {
          const f = ctx.field && ctx.field.counts;
          if (f) { if ((f[STYLE_NAMES[ctx.style]] || 0) > 0) return null; } else unknown.push(key);
        }
        else if (key === "finalCorner" && ctx.finalCorner) lim([[ctx.finalCorner[0], D]]);
        else unknown.push(key);
        if (!region.length) return null;
        continue;
      }
      // 順位の条件が上限・下限の2つで書かれている場合は、両方を同時に満たす割合で見る（別々に掛けると低く出る）
      if ((key === "order" || key === "order_rate") && list.length > 1) {
        const { N, lo, hi } = ctx.pos;
        let n = 0;
        for (let o = lo; o <= hi; o++) if (list.every(({ sign, value }) => cmp(key === "order" ? o : (o / N) * 100, sign, Number(value)))) n++;
        const pp = styleFit(ctx, key, n / (hi - lo + 1));
        if (pp <= 0) return null;
        prob *= pp; posKeys.push(key);
        continue;
      }
      for (const { sign, value } of list) {
        const v = Number(value);
        if (key in ctx.race) { if (!cmp(ctx.race[key], sign, v)) return null; continue; }
        switch (key) {
          case "phase":
            if (sign === "==") lim([phaseIv[v]]);
            else if (sign === ">=") lim([[phaseIv[v][0], D]]);
            else if (sign === "<=") lim([[0, phaseIv[v][1]]]);
            else if (sign === ">") lim([[phaseIv[Math.min(3, v + 1)][0], D]]);
            else if (sign === "<") lim([[0, phaseIv[Math.max(0, v - 1)][1]]]);
            break;
          case "phase_random": lim([phaseIv[v]]); random = true; break;
          case "phase_firsthalf_random": { const [a, b] = phaseIv[v]; lim([[a, (a + b) / 2]]); random = true; break; }
          case "phase_laterhalf_random": { const [a, b] = phaseIv[v]; lim([[(a + b) / 2, b]]); random = true; break; }
          case "phase_firstquarter_random": { const [a, b] = phaseIv[v]; lim([[a, a + (b - a) / 4]]); random = true; break; }
          case "phase_corner_random": lim(intersect(ctx.corners.map(([a, b]) => [a, b]), [phaseIv[v]])); random = true; break;
          case "phase_straight_random": lim(intersect(ctx.straights, [phaseIv[v]])); random = true; break;
          case "corner_random": lim(ctx.corners.filter((c) => c[2] === v).map(([a, b]) => [a, b])); random = true; break;
          case "all_corner_random": lim(ctx.corners.map(([a, b]) => [a, b])); random = true; break;
          case "corner":
            if ((sign === "!=" && v === 0) || (sign === ">=" && v >= 1)) lim(ctx.corners.map(([a, b]) => [a, b]));
            else if (sign === "==" && v === 0) lim(complement(ctx.corners.map(([a, b]) => [a, b]), D));
            else if (sign === "==") lim(ctx.corners.filter((c) => c[2] === v).map(([a, b]) => [a, b]));
            break;
          case "corner_count": if (!cmp(ctx.corners.length, sign, v)) return null; break;
          case "is_dirtgrade": if (cmp(ctx.course.surface === "ダート" ? 1 : 0, sign, v) === false) return null; break;
          case "straight_random": lim(ctx.straights); random = true; break;
          case "is_finalcorner":
            if (!ctx.finalCorner) return null;
            if (v === 1) lim([[ctx.finalCorner[0], D]]); else lim([[0, ctx.finalCorner[0]]]);
            break;
          case "is_finalcorner_random":
            if (!ctx.finalCorner) return null;
            lim([[ctx.finalCorner[0], ctx.finalCorner[1]]]); random = true; break;
          case "is_finalcorner_laterhalf":
            if (!ctx.finalCorner) return null;
            if (v === 1) lim([[(ctx.finalCorner[0] + ctx.finalCorner[1]) / 2, D]]); break;
          case "is_last_straight": case "is_last_straight_onetime":
            if (v === 1) lim([ctx.lastStraight]); break;
          case "run_at_full_speed":
            // 全開スパート中。仮モデルが無効なら発動しない
            if (!ctx.ft.on) return null;
            lim([[phaseIv[2][0], D]]); ft = true; break;
          case "is_lastspurt": case "lastspurt":
            lim([[phaseIv[2][0], D]]); break;
          case "run_at_full_speed_random":
            if (!ctx.ft.on) return null;
            lim([[phaseIv[2][0], D]]); random = true; ft = true; break;
          case "distance_rate":
            if (sign === ">=" || sign === ">") lim([[(D * v) / 100, D]]);
            else if (sign === "<=" || sign === "<") lim([[0, (D * v) / 100]]);
            break;
          case "distance_rate_after_random": lim([[(D * v) / 100, D]]); random = true; break;
          case "remain_distance":
            if (sign === "<=" || sign === "<") lim([[D - v, D]]);
            else if (sign === ">=" || sign === ">") lim([[0, D - v]]);
            else if (sign === "==") lim([[D - v, D - v + 1]]);
            break;
          case "up_slope_random": lim(ctx.ups.map(([a, b]) => [a, b])); random = true; break;
          case "down_slope_random": lim(ctx.downs.map(([a, b]) => [a, b])); random = true; break;
          case "slope":
            if (v === 1) lim(ctx.ups.map(([a, b]) => [a, b]));
            else if (v === 2) lim(ctx.downs.map(([a, b]) => [a, b]));
            else if (v === 0) lim(complement([...ctx.ups, ...ctx.downs].map(([a, b]) => [a, b]), D));
            break;
          case "accumulatetime":
            if (sign === ">=" || sign === ">") lim([[v * ctx.V0 * 0.9, D]]);
            break;
          case "base_speed": if (!cmp(ctx.stats.spd, sign, v)) return null; break;
          case "base_stamina": if (!cmp(ctx.stats.sta, sign, v)) return null; break;
          case "base_power": if (!cmp(ctx.stats.pow, sign, v)) return null; break;
          case "base_guts": if (!cmp(ctx.stats.gut, sign, v)) return null; break;
          case "base_wiz": if (!cmp(ctx.stats.wit, sign, v)) return null; break;
          case "always": break;
          case "phase_firsthalf": { const [a, b] = phaseIv[v]; lim([[a, (a + b) / 2]]); break; }
          case "phase_laterhalf": { const [a, b] = phaseIv[v]; lim([[(a + b) / 2, b]]); break; }
          case "motivation": if (!cmp(MOTIVATION[ctx.mood] ?? 5, sign, v)) return null; break;
          case "is_badstart": if (!cmp(0, sign, v)) return null; break;
          case "random_lot": case "random_lot_shared": prob *= v / 100; break;
          case "popularity":
            if (ctx.field && ctx.field.popularity) { if (!cmp(ctx.field.popularity, sign, v)) return null; } else unknown.push(key);
            break;
          case "post_number":
            if (ctx.field && ctx.field.post) { if (!cmp(ctx.field.post, sign, v)) return null; }
            else {
              // 枠番は毎レースくじ引き：出走頭数から各枠に入る確率を出す（9頭立てなら1〜7枠が1頭ずつ、8枠が2頭）
              const N = ctx.pos.N, F = Math.min(8, N), dbl = Math.max(0, N - 8);
              let pp = 0;
              for (let k = 1; k <= F; k++) if (cmp(k, sign, v)) pp += (k > F - dbl ? 2 : 1) / N;
              if (pp <= 0) return null;
              prob *= pp; posKeys.push(key);
            }
            break;
          case "running_style_count_same_rate": {
            const f = ctx.field && ctx.field.counts;
            if (f) { const same = (f[STYLE_NAMES[ctx.style]] || 0) + 1, all = 1 + Object.values(f).reduce((x, y) => x + y, 0); if (!cmp((same / all) * 100, sign, v)) return null; }
            else unknown.push(key);
            break;
          }
          case "running_style_count_nige_otherself": case "running_style_count_senko_otherself":
          case "running_style_count_sashi_otherself": case "running_style_count_oikomi_otherself": {
            const f = ctx.field && ctx.field.counts;
            const name = { nige: "逃げ", senko: "先行", sashi: "差し", oikomi: "追込" }[key.split("_")[3]];
            if (f) { if (!cmp(f[name] || 0, sign, v)) return null; } else unknown.push(key);
            break;
          }
          // 同じスキルの別の効果が発動したあとに続けて発動する、という条件（単独では発動しない）
          case "is_activate_other_skill_detail": dep = true; break;
          default: {
            const pp = styleFit(ctx, key, positionProb(ctx, key, sign, v));
            if (pp == null) unknown.push(key);
            else { if (pp <= 0) return null; prob *= pp; posKeys.push(key); }
          }
        }
        if (!region.length) return null;
      }
    }
    return { region, random, unknown, prob, ft, posKeys, dep };
  }

  // スキル1つ分の「発動予定」を作る。frac は 0〜1（ランダム位置のどこで発動するか）
  function planSkill(ctx, skill, frac) {
    const out = [];
    const seen = new Set();
    const pats = (skill.raw && skill.raw.effectPatterns) || skill.ep || skill.effectPatterns || [];
    // 続けて発動する効果（is_activate_other_skill_detail）は、先に単独で発動できる効果があるときだけ。位置はその後ろ
    // 前提条件（preconditions）：どれか1つの組が満たせないと発動しない（距離区分・脚質などの固定条件もここに入っていることがある）
    const preOk = (p) => {
      if (!p.preconditions || !p.preconditions.length) return { ok: true, prob: 1 };
      const rs = p.preconditions.map((g) => groupRegion(ctx, g)).filter(Boolean);
      return rs.length ? { ok: true, prob: Math.max(...rs.map((r) => r.prob ?? 1)) } : { ok: false };
    };
    const ordered = pats.map((p) => {
      const pre = preOk(p);
      const regs = pre.ok ? (p.conditions && p.conditions.length ? p.conditions : [{}]).map((g) => groupRegion(ctx, g)).filter(Boolean) : [];
      if (pre.prob < 1) for (const r of regs) r.prob = (r.prob ?? 1) * pre.prob;
      return { p, regs };
    });
    const mains = ordered.filter((o) => o.regs.length && !o.regs[0].dep);
    for (const { p, regs } of ordered.filter((o) => !o.regs.length || !o.regs[0].dep).concat(ordered.filter((o) => o.regs.length && o.regs[0].dep))) {
      if (!regs.length) continue;
      if (regs[0].dep && !mains.length) continue;
      // 効果の種類が同じパターンは「条件で強さが変わる」分岐なので、最初に発動できる1つだけ採用する
      const sig = (p.effects || []).map((e) => e.target).join(",");
      const r = regs[0];
      let pos = r.random ? pointAt(r.region, frac) : r.region[0][0];
      if (r.dep) { const first = out.find((x) => !x.dep); if (!first) continue; if (first.pos > pos) pos = first.pos; }
      const dur = p.baseTime > 0 ? (p.baseTime / 10000) * (ctx.D / 1000) : 0;
      // 全開スパート中が条件のものは、全開スパート開始位置〜ゴールの中の割合で発動位置を決める（走行中に確定）
      const plan = { pos: r.ft ? Infinity : pos, ftFrac: r.ft ? (r.random ? frac : 0) : null, dur, passive: p.baseTime < 0, effects: p.effects || [], random: r.random, unknown: r.unknown, prob: r.prob, posKeys: r.posKeys, alts: [], dep: !!r.dep };
      if (seen.has(sig)) { const main = out.find((x) => x.sig === sig); if (main) main.alts.push(plan); continue; }
      seen.add(sig);
      plan.sig = sig;
      out.push(plan);
    }
    return out;
  }

  /* ---------- 走行計算 ---------- */
  function run(ctx, plans) {
    const { D, V0, style, apt } = ctx;
    const st = { ...ctx.stats };
    // 常時発動（ステータス上昇）のスキルを先に反映
    const timed = [];
    for (const pl of plans) {
      if (pl.passive) {
        for (const e of pl.effects) {
          const v = e.value / 10000;
          if (e.target === 1) st.spd += v; else if (e.target === 2) st.sta += v; else if (e.target === 3) st.pow += v;
          else if (e.target === 4) st.gut += v; else if (e.target === 5) st.wit += v;
        }
      } else timed.push({ ...pl, fired: false });
    }
    timed.sort((a, b) => a.pos - b.pos);
    const maxHP = 0.8 * STRAT_HP[style] * st.sta + D;
    const distSpd = DIST_SPEED[apt.dist] ?? 1;
    const accBase = 0.0006 * Math.sqrt(500 * st.pow) * (SURF_ACCEL[apt.surf] ?? 1) * (DIST_ACCEL[apt.dist] ?? 1);
    const accUp = 0.0004 * Math.sqrt(500 * st.pow) * (SURF_ACCEL[apt.surf] ?? 1) * (DIST_ACCEL[apt.dist] ?? 1);
    const gutsCoef = 1 + 200 / Math.sqrt(600 * st.gut);
    const lateBase = V0 * STRAT_SPEED[style][2] + Math.sqrt(500 * st.spd) * distSpd * 0.002;
    const spurtMax = (lateBase + 0.01 * V0) * 1.05 + Math.sqrt(500 * st.spd) * distSpd * 0.002 + Math.pow(450 * st.gut, 0.597) * 0.0001;
    const vMin = 0.85 * V0 + Math.sqrt(200 * st.gut) * 0.001;
    const rate = (v, late) => (20 * Math.pow(v - V0 + 12, 2)) / 144 * ctx.hpCoef * (late ? gutsCoef : 1);

    let pos = 0, v = 3, hp = maxHP, t = 0, spurtV = null, startDash = true;
    let hpAtLate = null, needFull = null;
    // 全開スパート（仮モデル）の状態
    let ftStart = null, ftExtra = 0;
    // 持久力温存：中盤のあいだ2秒ごとに「残りを全力スパートで走り切れるか」を判定し、足りなければ発生とみなす
    // （公開資料に閾値の式がないため、位置取り調整に使う分は conserveMargin（最大HPに対する割合）で上乗せする）
    let nextCheck = 0, consumed = 0, consumedAtLate = null;
    const checks = [];
    const ftBaseAcc = 0.068 * (accBase * STRAT_ACCEL[style][2]) / (D / 1000) * 1.5;
    const active = []; // {kind, val, end}
    let minHp = maxHP;
    const decideSpurt = () => {
      const remain = D - pos - 60;
      const need = (sv) => (rate(sv, true) * Math.max(0, remain)) / sv;
      if (hp >= need(spurtMax)) return spurtMax;
      let lo = lateBase, hi = spurtMax;
      if (hp < need(lo)) return lateBase;
      for (let i = 0; i < 20; i++) { const m = (lo + hi) / 2; if (hp >= need(m)) lo = m; else hi = m; }
      return lo;
    };
    // 賢さによる目標速度の揺らぎ（区間ごとの乱数）の平均値。ラストスパートには掛からない
    const witMax = (st.wit / 5500) * Math.log10(st.wit * 0.1);
    const witMean = ctx.opts.witNoise ? (witMax + (witMax - 0.65)) / 2 / 100 : 0;
    // 下り坂加速モード：毎秒 賢さ×0.04% で入り、毎秒20%で抜ける → 下り坂で過ごす時間のうち入っている割合の期待値
    const q = Math.min(1, st.wit * 0.0004);
    const downFrac = ctx.opts.downhill ? q / (q + 0.2) : 0;
    // 掛かり：区間2〜9のどこか（平均で区間5.5）から始まる。期待値モードでは確率×期待持続時間ぶんだけ消費を1.6倍にする
    const rushP = ctx.opts.rushed === "always" ? 1 : ctx.opts.rushed === "expected" ? rushedChance(st.wit) : 0;
    const rushDur = ctx.opts.rushed === "always" ? 12 : RUSHED_EXPECTED_SEC;
    const rushStart = (D / 24) * 5.5;
    let rushT0 = null;
    // 位置取り争い：150m地点から、根性で決まる時間だけ。区間9に入ると必ず終わる。目標速度＋、消費1.4倍
    const spotDur = ctx.comp.spot ? Math.pow(700 * st.gut, 0.5) * 0.012 : 0;
    const spotV = Math.pow(500 * st.gut, 0.6) * 0.0001;
    let spotT0 = null, spotHp = 0;
    // リード確保：区間11〜15のあいだ、期待発動回数×1回の消費を距離に応じて均等に差し引く（速度の上乗せは式が非公開のため入れない）
    const slA = (D * 10) / 24, slB = (D * 15) / 24;
    const slBase = ctx.comp.lead ? (ctx.opts.secureLeadBase || 0) * SL_STYLE_HP[style] * slDistCoef(D) : 0;
    let slHp = 0, slN = 0;
    // その他の位置取り（ポジションキープ・ペースアップ等）による消費の補正：序盤〜中盤の消費に脚質ごとの割合を上乗せ
    const posExtra = 1 + (((ctx.opts.posExtra || {})[STYLE_NAMES[style]] || 0) / 100);
    let reachPos = null, reachT = null, lateT0 = null;
    const slopeAt = (p) => { for (const [a, b, g] of ctx.ups) if (p >= a && p < b) return g; for (const [a, b, g] of ctx.downs) if (p >= a && p < b) return g; return 0; };

    let guard = 0;
    while (pos < D && guard++ < 200000) {
      const phase = pos < ctx.phaseIv[0][1] ? 0 : pos < ctx.phaseIv[1][1] ? 1 : pos < ctx.phaseIv[2][1] ? 2 : 3;
      if (phase >= 2 && spurtV === null) {
        spurtV = decideSpurt();
        hpAtLate = hp;
        needFull = (rate(spurtMax, true) * Math.max(0, D - pos - 60)) / spurtMax;
      }
      // スキル発動
      for (const s of timed) {
        if (s.ftFrac != null && ftStart !== null && s.pos === Infinity) s.pos = ftStart + s.ftFrac * (D - ftStart);
        if (s.fired || pos < s.pos) continue;
        s.fired = true;
        for (const e of s.effects) {
          const val = e.value / 10000;
          if (e.target === 9) {
            // 「持久力をすごく使ってしまうことがある」型の大きな消費は、良い方の結果で評価する
            if (val > -0.5) { hp = Math.min(maxHP, hp + maxHP * val); if (phase >= 2) spurtV = decideSpurt(); }
          }
          else if (e.target === 27) active.push({ kind: "target", val, end: t + s.dur });
          else if (e.target === 31) active.push({ kind: "accel", val, end: t + s.dur });
          // 「前に出る」系：効果時間中は現在速度ごと押し上げる。21 は終了時に上乗せ分を戻し、22 は自然に減速させる
          else if (e.target === 21) { v += val; active.push({ kind: "target", val, end: t + s.dur }); active.push({ kind: "current", val, end: t + s.dur }); }
          else if (e.target === 22) { v += val; active.push({ kind: "target", val, end: t + s.dur }); }
          else if (e.target === 48) active.push({ kind: "nobi", val, end: t + s.dur });
        }
      }
      let tgtSkill = 0, accSkill = 0, nobi = 0;
      for (let i = active.length - 1; i >= 0; i--) {
        const a = active[i];
        if (t >= a.end) { if (a.kind === "current") v -= a.val; active.splice(i, 1); continue; }
        if (a.kind === "target") tgtSkill += a.val; else if (a.kind === "accel") accSkill += a.val; else if (a.kind === "nobi") nobi += a.val;
      }
      const slope = slopeAt(pos);
      let target = phase <= 1 ? V0 * STRAT_SPEED[style][phase] * (1 + witMean) : spurtV;
      if (slope > 0) target -= (slope * 200) / st.pow;
      if (slope < 0 && phase <= 1) target += downFrac * (0.3 + Math.abs(slope) / 10);
      target += tgtSkill;
      const inSpot = spotDur > 0 && pos >= 150 && pos < (D * 8) / 24 && (spotT0 === null || t - spotT0 < spotDur);
      if (inSpot) { if (spotT0 === null) spotT0 = t; target += spotV; }
      // 全開スパート：全力スパート中に最高速度へ届いた瞬間から、最高速度を少しずつ上げ続ける（坂やデバフによる減速は判定から除く）
      if (ctx.ft.on && phase >= 2 && hp > 0) {
        if (ftStart === null && spurtV >= spurtMax - 1e-6 && v >= spurtMax - 0.01) ftStart = pos;
        if (ftStart !== null) {
          const before = ftExtra;
          ftExtra = Math.min(ctx.ft.maxGain, ftExtra + (ftBaseAcc + nobi * ctx.ft.coef) * DT);
          v += ftExtra - before;
          target += ftExtra;
        }
      }
      if (hp <= 0) target = vMin;
      if (startDash && v >= 0.85 * V0) startDash = false;
      let a;
      if (v < target) {
        a = (slope > 0 ? accUp : accBase) * STRAT_ACCEL[style][Math.min(phase, 2)] + accSkill + (startDash ? 24 : 0);
        v = Math.min(target, v + a * DT);
      } else if (v > target) {
        v = Math.max(target, v + DECEL[phase] * DT);
      }
      let status = 1;
      if (slope < 0 && phase <= 1) status *= 1 - 0.6 * downFrac;
      if (phase <= 1) status *= posExtra;
      if (inSpot) status *= 1.4;
      if (rushP > 0 && pos >= rushStart) {
        if (rushT0 === null) rushT0 = t;
        if (t - rushT0 < rushDur) status *= 1 + 0.6 * rushP;
      }
      let use = rate(v, phase >= 2) * status * DT;
      if (inSpot) spotHp += use - use / 1.4;
      if (slBase > 0 && pos >= slA && pos < slB) {
        const n = (DT / 2) * SL_PER_CHECK; // この刻みで起きる期待発動回数
        slN += n; slHp += n * slBase; use += n * slBase;
      }
      hp -= use;
      consumed += use;
      if (phase >= 2 && lateT0 === null) lateT0 = t;
      // 終盤：ラストスパートの目標速度に届いた地点（加速スキルの効き具合の目安）
      if (phase >= 2 && reachPos === null && spurtV !== null && v >= spurtV - 0.01) { reachPos = pos; reachT = t - lateT0; }
      if (phase >= 2 && consumedAtLate === null) consumedAtLate = consumed;
      // 中盤（位置取り調整が起きる区間）のあいだ、2秒ごとに判定点を記録（判定そのものは走行後にまとめて行う）
      // 位置取り調整（＝持久力温存の判定）は中盤の後半（区間11以降）だけで起きる
      if (phase === 1 && pos >= slA && t >= nextCheck) { nextCheck = t + 2; checks.push({ pos, hp, consumed }); }
      if (hp < minHp) minHp = hp;
      pos += v * DT;
      t += DT;
    }
    // 持久力温存の判定：各判定点で「そこから中盤の終わりまでに使う体力（回復を除く）＋終盤を全力で走る体力＋予備」が残っているか
    const needLate = (rate(spurtMax, true) * Math.max(0, D - ctx.phaseIv[2][0] - 60)) / spurtMax;
    let conserveAt = null, conserveWorst = 0, conserveRaw = -Infinity;
    for (const c of checks) {
      const midUse = (consumedAtLate ?? consumed) - c.consumed;
      const short = (midUse + needLate) * (ctx.opts.conserveTarget || CONSERVE_TARGET) + maxHP * (ctx.opts.conserveMargin || 0) - c.hp;
      if (short > conserveWorst) conserveWorst = short;
      if (short > conserveRaw) conserveRaw = short;
      if (short > 0 && conserveAt === null) conserveAt = c.pos;
    }
    // ゴール線を越えた分を戻して、到達時刻を補間
    const over = pos - D;
    const finish = t - over / Math.max(v, 1);
    return { time: finish, maxHP, hpLeft: hp, minHp, spurt: spurtV, spurtMax, finalSpeed: v, hpAtLate, needFull, fullSpurt: spurtV >= spurtMax - 1e-6 && hp > 0,
      rushedChance: rushedChance(st.wit), courseMod: ctx.courseMod, ftStart, ftGain: ftExtra,
      conserveAt, conserveShort: conserveWorst, conserveGap: -conserveRaw,
      lateStart: ctx.phaseIv[2][0], reachPos, reachT, spotHp, secureLeadHp: slHp, secureLeadN: slN, comp: ctx.comp };
  }

  /* ---------- 公開関数 ---------- */
  function baseline(ctx, extraPlans) { return run(ctx, extraPlans || []); }

  // スキル1つの獲得バ身。ランダム位置のスキルは samples 回ずらして平均・最小・最大を出す。
  function skillBashin(ctx, skill, opts) {
    const samples = (opts && opts.samples) || 12;
    const base = (opts && opts.base) || run(ctx, (opts && opts.basePlans) || []);
    const first = planSkill(ctx, skill, 0.5);
    if (!first.length) return { ok: false, reason: "このレースでは発動しない" };
    const isRandom = first.some((p) => p.random);
    const n = isRandom ? samples : 1;
    // 条件で強さが分岐するスキルは「強い方の成立確率×強い方＋外れたとき弱い方」の期待値にする
    const variantsOf = (plans) => {
      const main = plans.find((p) => p.alts && p.alts.length);
      if (!main) return [{ w: plans.reduce((a, p) => a * (p.prob ?? 1), 1), plans }];
      const chain = [main, ...main.alts];
      // 人気など、出走の想定が未定の条件で強さが分かれるものは、分岐どうしが両立しない（4番人気以下／3番人気以内など）。
      // 未定のまま両方を「満たす」扱いで足すと二重に数えるので、成立確率がいちばん高い分岐1つだけで評価する
      if (chain.every((c) => (c.unknown || []).some((k) => /^popularity/.test(k)))) {
        const best = chain.reduce((a, c) => ((c.prob ?? 1) > (a.prob ?? 1) ? c : a), chain[0]);
        return [{ w: best.prob ?? 1, plans: [...plans.filter((p) => p !== main), best] }];
      }
      const out = []; let rest = 1;
      for (const c of chain) {
        const pc = c.prob ?? 1;
        const others = plans.filter((p) => p !== main).map((p) => p);
        out.push({ w: rest * pc, plans: [...others, c] });
        rest *= 1 - pc;
        if (rest < 1e-6) break;
      }
      return out;
    };
    const basePlans = (opts && opts.basePlans) || [];
    const vals = [];
    let pAny = 0;
    for (let i = 0; i < n; i++) {
      const frac = n === 1 ? 0.5 : (i + 0.5) / n;
      const vars = variantsOf(planSkill(ctx, skill, frac));
      let acc = 0;
      for (const vr of vars) {
        if (vr.w <= 0) continue;
        const r = run(ctx, [...basePlans, ...vr.plans]);
        acc += vr.w * (((base.time - r.time) * base.finalSpeed) / BASHIN_M);
      }
      if (i === 0) pAny = vars.reduce((a, vr) => a + vr.w, 0);
      vals.push(acc);
    }
    const mean = vals.reduce((s, x) => s + x, 0) / vals.length;
    // 下位25%点（ランダム位置のスキルを控えめに見るとき用）
    const sv = vals.slice().sort((a, b) => a - b), qi = (sv.length - 1) * 0.25, q25 = sv[Math.floor(qi)] + (sv[Math.ceil(qi)] - sv[Math.floor(qi)]) * (qi - Math.floor(qi));
    const unknown = [...new Set(first.flatMap((p) => p.unknown))];
    const posKeys = [...new Set(first.flatMap((p) => [...(p.posKeys || []), ...(p.alts || []).flatMap((a) => a.posKeys || [])]))];
    return { ok: true, mean, q25, min: Math.min(...vals), max: Math.max(...vals), random: isRandom, unknown, prob: pAny, folded: true, posKeys };
  }

  // 賢さによる発動率（パッシブ以外）
  function activationRate(ctx) { return Math.max(0.2, 1 - 90 / ctx.stats.wit); }

  // スキル群をまとめて受け取り、発動するものだけを残した計画を返す（回復の積み上げ評価用）
  function plansFor(ctx, skills) { return skills.flatMap((s) => planSkill(ctx, s, 0.5)); }

  return { buildContext, run, baseline, skillBashin, planSkill, plansFor, activationRate, groupRegion, distCat, BASHIN_M, rushedChance };
});

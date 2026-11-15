// ---------------------------------------------------------------------------
// qprob/asymptotic/laws.mbt — 第一階數學結構定律總表（無窮漸近極限空間與子場）
// ---------------------------------------------------------------------------

///|
pub fn asym_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    (
      "代數子場塔 ℚ ⊂ ℚ(√d) 與 Galois 共軛不變子場",
      law_subfield_tower(),
    ),
    (
      "非阿基米德漸近噴流場 ℚ((ε))_≤M 與標準部商同態",
      law_asymptotic_jet_field(),
    ),
    (
      "射影極限空間 lim_← V_k 與 Mittag-Leffler 穩定性定理",
      law_projective_limit_space(),
    ),
    (
      "Richardson 外推、Shanks–Aitken Δ² 與 Cesàro 極限演算法",
      law_asymptotic_acceleration(),
    ),
  ]
}

///|
pub fn law_subfield_tower() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let samples = [
    quad_make(qv_int(0), qv_int(0), 2),
    quad_make(qv_int(1), qv_int(0), 2),
    quad_make(qv_int(3), qv_int(-2), 2),
    quad_make(qv_frac(1, 2), qv_frac(3, 4), 2),
    quad_make(qv_frac(-5, 3), qv_int(1), 2),
    quad_make(qv_int(2), qv_int(1), 2),
  ]
  let n = samples.length()
  let mut ring_ok = true
  let mut inv_ok = true
  let mut norm_mult = true
  let mut galois_fixed = true
  let mut non_fixed_cnt = 0
  for i in 0..<n {
    let x = samples[i]
    // Galois 不動點刻畫：conj(x) == x ⇔ x ∈ ℚ（surd == 0）
    let fixed = quad_eq(quad_conj(x), x)
    if fixed != quad_in_base_subfield(x) {
      galois_fixed = false
    }
    if !fixed {
      non_fixed_cnt = non_fixed_cnt + 1
    }
    // 跡與範數皆落在基體 ℚ，x + conj(x) = Tr(x)，x - conj(x) 實部為 0，且 x·conj(x) = N(x) ∈ ℚ ↪ ℚ(√2)
    let sum_conj = quad_add(x, quad_conj(x))
    let diff_conj = quad_sub(x, quad_conj(x))
    let prod_conj = quad_mul(x, quad_conj(x))
    if !quad_eq(prod_conj, quad_of_qv(quad_norm(x), 2)) ||
      !quad_eq(sum_conj, quad_of_qv(quad_trace(x), 2)) ||
      !qv_is_zero(diff_conj.re) {
      norm_mult = false
    }
    if !(qv_is_zero(x.re) && qv_is_zero(x.surd)) {
      match quad_inv(x) {
        None => inv_ok = false
        Some(ix) =>
          if !quad_eq(quad_mul(x, ix), quad_of_qv(qv_one(), 2)) {
            inv_ok = false
          }
      }
    }
    for j in 0..<n {
      let y = samples[j]
      if !qv_eq(quad_norm(quad_mul(x, y)), qv_mul(quad_norm(x), quad_norm(y))) {
        norm_mult = false
      }
      for k in 0..<n {
        let z = samples[k]
        if !quad_eq(quad_mul(quad_mul(x, y), z), quad_mul(x, quad_mul(y, z))) {
          ring_ok = false
        }
        if !quad_eq(
            quad_mul(x, quad_add(y, z)),
            quad_add(quad_mul(x, y), quad_mul(x, z)),
          ) {
          ring_ok = false
        }
      }
    }
  }
  chk(
    out,
    "ℚ(√2) 結合律與分配律（\{n}³ = \{n * n * n} 組）",
    ring_ok,
  )
  chk(
    out, "ℚ(√2) 非零元素皆可逆（範數 a²−2b² 在 ℚ 上無非平凡零解）",
    inv_ok,
  )
  chk(
    out,
    "範數乘法性 N(xy) = N(x)N(y) 與 x·x̄ = N(x) ∈ ℚ（\{n}² 對）",
    norm_mult,
  )
  chk(
    out,
    "Galois 子場定理：Fix(σ) = ℚ（\{n} 樣本中 \{non_fixed_cnt} 個真擴張元被共軛移動）",
    galois_fixed && non_fixed_cnt == 4,
  )
  // √2 的平方精確回到基體 2 ∈ ℚ，且負次冪 qv_pow(2/3, -3) = 27/8 精確滿足逆元指數律
  let sqrt2 = quad_make(qv_zero(), qv_one(), 2)
  let sq = quad_mul(sqrt2, sqrt2)
  let neg_pow_ok = qv_eq(qv_pow(qv_frac(2, 3), -3), qv_frac(27, 8)) &&
    qv_eq(qv_mul(qv_pow(qv_frac(3, 5), 4), qv_pow(qv_frac(3, 5), -4)), qv_one()) &&
    qv_is_zero(qv_pow(qv_zero(), -2))
  chk(
    out,
    "(√2)² = \{qv_show(sq.re)} + \{qv_show(sq.surd)}√2 落回基子場 ℚ，且負指數冪 (2/3)⁻³ = 27/8 滿足乘法群律",
    quad_in_base_subfield(sq) && qv_eq(sq.re, qv_int(2)) && neg_pow_ok,
  )
  // 負控制：可約根號 d = 4（√4 = 2）會產生零因子 (2 - √4)(2 + √4) = 0，範數為 0 不可逆
  let reducible = quad_make(qv_int(2), qv_int(1), 4)
  chk(
    out,
    "負控制：d = 4 非無平方因子時 N(2+√4) = \{qv_show(quad_norm(reducible))}，quad_inv 拒絕回傳 None",
    qv_is_zero(quad_norm(reducible)) && quad_inv(reducible) is None,
  )
  out
}

///|
pub fn law_asymptotic_jet_field() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let cut = 5
  let eps = jet_monomial(qv_one(), 1, cut)
  let eps2 = jet_monomial(qv_one(), 2, cut)
  let inv_eps = jet_monomial(qv_one(), -1, cut)
  let one = jet_const(qv_one(), cut)
  // 非阿基米德序：0 < ε² < ε < 1/1000 < 1 < ε⁻¹
  let tiny_q = jet_const(qv_frac(1, 1000), cut)
  let non_arch = jet_cmp(jet_zero(cut), eps2) < 0 &&
    jet_cmp(eps2, eps) < 0 &&
    jet_cmp(eps, tiny_q) < 0 &&
    jet_cmp(tiny_q, one) < 0 &&
    jet_cmp(one, inv_eps) < 0
  chk(
    out, "非阿基米德有序場鏈：0 < ε² < ε < 1/1000 < 1 < ε⁻¹（無窮小嚴格小於正有理數）",
    non_arch,
  )
  // Laurent 長除法反元素：(ε⁻¹ + 2 + 3ε)⁻¹ = ε - 2ε² - ε³ + ...
  let f = jet_add(
    inv_eps,
    jet_add(jet_const(qv_int(2), cut), jet_monomial(qv_int(3), 1, cut)),
  )
  let inv_ok = match jet_inv(f) {
    None => false
    Some(g) => {
      // f 有 -1 階，g 有 +1 階，乘積精確至 cutoff - 1 = 4 階
      let prod = jet_mul(
        AsymJet::{ min_exp: f.min_exp, cutoff: cut - 1, coeffs: f.coeffs, },
        AsymJet::{ min_exp: g.min_exp, cutoff: cut - 1, coeffs: g.coeffs, },
      )
      jet_eq(prod, jet_const(qv_one(), cut - 1)) && jet_valuation(g) == Some(1)
    }
  }
  chk(
    out, "漸近 Laurent 場反元素：(ε⁻¹ + 2 + 3ε)⁻¹ 賦值階為 +1 且乘積 ≡ 1 (mod ε⁵)",
    inv_ok,
  )
  // 標準部同態定理：st(a + b) = st(a) + st(b) 與 st(a · b) = st(a) · st(b) 對有界噴流成立
  let a = jet_add(
    jet_const(qv_frac(5, 2), cut),
    jet_add(jet_monomial(qv_int(-7), 1, cut), jet_monomial(qv_int(4), 2, cut)),
  )
  let b = jet_add(
    jet_const(qv_frac(-3, 4), cut),
    jet_monomial(qv_int(9), 1, cut),
  )
  let st_hom = match
    (
      jet_standard_part(a),
      jet_standard_part(b),
      jet_standard_part(jet_add(a, b)),
      jet_standard_part(jet_mul(a, b)),
    ) {
    (Some(sa), Some(sb), Some(s_add), Some(s_mul)) =>
      qv_eq(s_add, qv_add(sa, sb)) &&
      qv_eq(s_mul, qv_mul(sa, sb)) &&
      qv_eq(s_mul, qv_frac(-15, 8))
    _ => false
  }
  chk(
    out, "標準部商同態定理：st : ℚ[[ε]] → ℚ 保加法與乘法（st(a·b) = −15/8），完全消去 O(ε) 項",
    st_hom,
  )
  // 核刻畫：st(x) = Some(0) ⇔ x ∈ ε·ℚ[[ε]]（無窮小理想），且 a - a 精確為零噴流
  let diff_inf = jet_sub(a, jet_const(qv_frac(5, 2), cut))
  chk(
    out,
    "商核刻畫：ker(st) = ε·ℚ[[ε]]（a − st(a) 的賦值階 = \{jet_valuation(diff_inf).unwrap_or(-99)} ≥ 1，且 a−a 為零噴流）",
    jet_is_infinitesimal(diff_inf) &&
    !jet_is_zero(diff_inf) &&
    jet_is_zero(jet_sub(a, a)) &&
    jet_standard_part(diff_inf) == Some(qv_zero()),
  )
  // 負控制：無窮大發散元 f = ε⁻¹ + ... 不屬於賦值環，標準部回傳 None
  chk(
    out,
    "負控制：無窮大元 ε⁻¹ + 2 + 3ε（val = −1）不屬於有界子環，jet_standard_part 回傳 None",
    !jet_is_bounded(f) && jet_standard_part(f) is None,
  )
  out
}

///|
pub fn law_projective_limit_space() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  // 1. 滿射截斷射影塔：dims = [2, 3, 4, 5]（Fock 空間有限粒子截斷的原型）
  let surj_tower = tower_canonical_truncation([2, 3, 4, 5])
  let coherent = [
    [qv_int(1), qv_frac(1, 2)],
    [qv_int(1), qv_frac(1, 2), qv_frac(1, 6)],
    [qv_int(1), qv_frac(1, 2), qv_frac(1, 6), qv_frac(1, 24)],
    [qv_int(1), qv_frac(1, 2), qv_frac(1, 6), qv_frac(1, 24), qv_frac(1, 120)],
  ]
  chk(
    out,
    "射影極限相容執行緒：指數相干態截斷 (1/k!)_{k≤N} 在 lim_← ℚ^{N+1} 各層嚴格滿足 π_{N,N+1}(x_{N+1}) = x_N",
    tower_is_coherent_thread(surj_tower, coherent),
  )
  // 函子複合律：π_{0,3} = π_{0,1} ∘ π_{1,2} ∘ π_{2,3}
  let t03 = tower_transition(surj_tower, 0, 3)
  let direct = qmat_vec_mul(t03, 2, 5, coherent[3])
  chk(
    out,
    "射影轉移函子律：π_{0,3}(x_3) = [\{qv_show(direct[0])}, \{qv_show(direct[1])}] = x_0",
    qv_vec_eq(direct, coherent[0]),
  )
  // Mittag-Leffler 滿射穩定性：每層穩定秩等於該層全維度
  let r0 = tower_mittag_leffler_stable_rank(surj_tower, 0)
  let r1 = tower_mittag_leffler_stable_rank(surj_tower, 1)
  let r2 = tower_mittag_leffler_stable_rank(surj_tower, 2)
  chk(
    out,
    "Mittag-Leffler 滿射定理：截斷塔穩定像秩 = [\{r0}, \{r1}, \{r2}] = [2, 3, 4]（無穩定化虧損）",
    r0 == 2 && r1 == 3 && r2 == 4,
  )
  // 2. 非滿射但滿足 Mittag-Leffler 的尼爾冪射影塔：π = [[1, 0], [0, 0]]，2×2 塔穩定至 1 維子空間
  let proj1 = [qv_one(), qv_zero(), qv_zero(), qv_zero()]
  let ml_sub_tower = ProjectiveTower::{
    dims: [2, 2, 2, 2],
    maps: [proj1, proj1, proj1],
  }
  let sub_rank = tower_mittag_leffler_stable_rank(ml_sub_tower, 0)
  chk(
    out,
    "非滿射 Mittag-Leffler 子空間收縮：秩 1 投影塔 Im(π_{0,3}) 穩定維度 = \{sub_rank} < 2",
    sub_rank == 1,
  )
  // 負控制：不相容的序列被射影極限判定器拒絕
  let broken_thread = [
    [qv_int(1), qv_frac(1, 2)],
    [qv_int(1), qv_frac(9, 7), qv_frac(1, 6)],
    [qv_int(1), qv_frac(1, 2), qv_frac(1, 6), qv_frac(1, 24)],
    [qv_int(1), qv_frac(1, 2), qv_frac(1, 6), qv_frac(1, 24), qv_frac(1, 120)],
  ]
  chk(
    out,
    "負控制：破壞第 1 層座標的偽執行緒被 tower_is_coherent_thread 精確拒絕",
    !tower_is_coherent_thread(surj_tower, broken_thread),
  )
  out
}

///|
pub fn law_asymptotic_acceleration() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  // 1. Richardson–Neville 定理：設 A(N) = 7/3 + 5/N - 11/N² + 4/N³，
  //    僅取 4 個有限尺度 N = 1, 2, 3, 4，外推必須零誤差還原無窮極限 L = 7/3！
  let true_l = qv_frac(7, 3)
  let scales = [1, 2, 3, 4]
  let vals : Array[QVal] = []
  for n in scales {
    let inv_n = qv_frac(1, n)
    let term1 = qv_mul(qv_int(5), inv_n)
    let term2 = qv_mul(qv_int(-11), qv_pow(inv_n, 2))
    let term3 = qv_mul(qv_int(4), qv_pow(inv_n, 3))
    vals.push(qv_add(true_l, qv_add(term1, qv_add(term2, term3))))
  }
  let rich_ok = match richardson_extrapolate_limit(scales, vals) {
    None => false
    Some(est) => qv_eq(est, true_l) && !qv_eq(vals[3], true_l)
  }
  chk(
    out,
    "Richardson 漸近外推定理：4 點尺度 [1,2,3,4] 完全消去 N⁻¹..N⁻³ 誤差，精確命中 L = \{qv_show(true_l)}",
    rich_ok,
  )
  // 2. Shanks–Aitken Δ² 定理：對 s_n = 11/5 + 3 · (1/3)^n，任意連續三項一步給出極限 11/5
  let geom_lim = qv_frac(11, 5)
  let geom_seq = [
    for n in 0..<5 => {
      qv_add(geom_lim, qv_mul(qv_int(3), qv_pow(qv_frac(1, 3), n)))
    }
  ]
  let aitken1 = shanks_aitken_step(geom_seq)
  let shanks_exact = aitken1.length() == 3 &&
    qv_eq(aitken1[0], geom_lim) &&
    qv_eq(aitken1[1], geom_lim) &&
    qv_eq(aitken1[2], geom_lim)
  chk(
    out,
    "Shanks–Aitken Δ² 精確極限定理：s_n = 11/5 + 3·(1/3)^n 單步變換全數恆等於 \{qv_show(geom_lim)}",
    shanks_exact,
  )
  // 雙指數暫態 s_n = 2 + (1/2)^n + (-1/3)^n：Wynn ε_4 菱形變換在 2K+1 = 5 個點上**精確零誤差命中極限 2**！
  let bi_exp = [
    for n in 0..<5 => {
      qv_add(
        qv_int(2),
        qv_add(qv_pow(qv_frac(1, 2), n), qv_pow(qv_frac(-1, 3), n)),
      )
    }
  ]
  let wynn_ok = match wynn_epsilon_limit(bi_exp) {
    None => false
    Some(est) => qv_eq(est, qv_int(2)) && !qv_eq(bi_exp[4], qv_int(2))
  }
  chk(
    out, "二階 Shanks–Wynn ε_4 定理：5 點雙模態序列 2 + (1/2)^n + (−1/3)^n 經 ε-算法零誤差精確命中極限 2",
    wynn_ok,
  )
  // 3. Cesàro 正則化：振盪序列 c + (-1)^k 在偶數視窗 N = 2m 上 Cesàro 平均精確等於 c
  let osc = [
    for k in 0..<8 => {
      qv_add(qv_frac(9, 4), if k % 2 == 0 { qv_one() } else { qv_int(-1) })
    }
  ]
  chk(
    out,
    "Cesàro 遍歷平均正則化：振盪序列 9/4 + (−1)^k 在偶視窗 N=8 平均精確收斂至 9/4（末項仍為 5/4）",
    cesaro_mean(osc) == Some(qv_frac(9, 4)) && !qv_eq(osc[7], qv_frac(9, 4)),
  )
  // 負控制：非法零尺度 N = 0 被 Richardson 外推拒絕
  chk(
    out,
    "負控制：含奇異尺度 N = 0 的輸入被 richardson_extrapolate_limit 拒絕（回傳 None）",
    richardson_extrapolate_limit([0, 1, 2], [qv_one(), qv_one(), qv_one()])
    is None,
  )
  out
}

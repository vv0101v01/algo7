// ---------------------------------------------------------------------------
// qprob/ccr_field/laws.mbt — 第四階數學結構定律總表（連續創生與湮滅算子場）
// ---------------------------------------------------------------------------

///|
pub fn ccr_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    (
      "塗抹連續場 CCR 對易律與離散格點場 N→∞ Richardson 連續極限定理",
      law_continuum_smearing_limit(),
    ),
    (
      "Wick 正規序展開演算法與連續高斯場 4 點／6 點關聯函數定理",
      law_wick_normal_ordering(),
    ),
    (
      "Weyl 相空間辛形式反對稱性、2-上循環恆等式與海森堡群中心擴張",
      law_weyl_symplectic_cocycle(),
    ),
    (
      "Hudson–Parthasarathy 量子 Itô 乘法表結合律與么正隨機演化判準",
      law_hudson_parthasarathy_ito(),
    ),
  ]
}

///|
pub fn law_continuum_smearing_limit() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let z0 = @asymptotic.qv_zero()
  let z1 = @asymptotic.qv_one()
  // 在 [0, 1] 上取 g(t) = 1 + 2t，f(t) = 3 - t + t²
  // 乘積 g(t)f(t) = 3 + 5t - t² + 2t³
  // 精確積分 ∫_0^1 (3 + 5t - t² + 2t³) dt = 3 + 5/2 - 1/3 + 1/2 = 17/3！
  let g = ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [@asymptotic.qv_one(), @asymptotic.qv_int(2)],
  }
  let f = ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [
      @asymptotic.qv_int(3),
      @asymptotic.qv_int(-1),
      @asymptotic.qv_one(),
    ],
  }
  let exact_comm = continuum_l2_inner(g, f)
  @asymptotic.chk(
    out,
    "塗抹連續場對易律：[A(1+2t), A†(3−t+t²)] = ∫_0^1 g(t)f(t)dt = \{@asymptotic.qv_show(exact_comm)} = 17/3",
    @asymptotic.qv_eq(exact_comm, @asymptotic.qv_frac(17, 3)),
  )
  // 跨層定理連結（第一階 × 第四階）：
  // 由於 g(t)f(t) 為 3 次多項式，左端點 Riemann 格點對易子 [A_N(g), A_N†(f)] 具有精確 3 階漸近展開
  // L + c_1/N + c_2/N² + c_3/N³（Euler–Maclaurin 公式，B_4 項對 3 次多項式導數為 0！）。
  // 因此取 4 個離散格點尺度 N = [2, 4, 8, 16] 送入第一階的 Richardson 外推器，必須**零誤差**命中 17/3！
  let scales = [2, 4, 8, 16]
  let lat_comms = [
    for n in scales => fock_lattice_bosonic_commutator(g, f, n)
  ]
  let limit_ok = match
    @asymptotic.richardson_extrapolate_limit(scales, lat_comms) {
    None => false
    Some(lim) =>
      @asymptotic.qv_eq(lim, exact_comm) &&
      !@asymptotic.qv_eq(lat_comms[3], exact_comm)
  }
  @asymptotic.chk(
    out, "離散格點場 → 連續量子場漸近極限定理：4 個格點尺度 [2,4,8,16] 經 Richardson 外推零誤差重現連續對易子 17/3",
    limit_ok,
  )
  // Legendre 正交模態解耦：P_0(t) = 1 與平移 P_1(t) = 2t - 1 在 [0, 1] 上正交 ⇒ [A(P_0), A†(P_1)] = 0！
  let p0 = ContinuumTestFn::{ t_start: z0, t_end: z1, coeffs: [z1], }
  let p1 = ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [@asymptotic.qv_int(-1), @asymptotic.qv_int(2)],
  }
  let scaled_g = test_fn_scale(@asymptotic.qv_int(3), g)
  @asymptotic.chk(
    out,
    "連續正交波包解耦與雙線性：∫_0^1 1·(2t−1)dt = 0 且 [A(3g), A†(f)] = 3[A(g), A†(f)]",
    @asymptotic.qv_is_zero(continuum_l2_inner(p0, p1)) &&
    @asymptotic.qv_eq(
      continuum_l2_inner(scaled_g, f),
      @asymptotic.qv_mul(@asymptotic.qv_int(3), exact_comm),
    ),
  )
  out
}

///|
pub fn law_wick_normal_ordering() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let z0 = @asymptotic.qv_zero()
  let z1 = @asymptotic.qv_one()
  // 取歸一化常數波包 f_0(t) = 1（∫_0^1 1² dt = 1）
  let f0 = ContinuumTestFn::{ t_start: z0, t_end: z1, coeffs: [z1], }
  // 1. 檢驗 A(f_0)² A†(f_0)² 的正規序展開：
  //    A² (A†)² = : (A†)² A² : + 4 ⟨f_0,f_0⟩ A† A + 2 ⟨f_0,f_0⟩² I
  //    故真空期望值 ⟨Ω | A(f_0)² A†(f_0)² | Ω⟩ = 2！且總展開項合併前縮併係數和滿足代數恆等
  let seq_22 = [Annihilate(f0), Annihilate(f0), Create(f0), Create(f0)]
  let vev_22 = wick_vacuum_expectation(seq_22)
  let vev_33 = wick_vacuum_expectation([
    Annihilate(f0),
    Annihilate(f0),
    Annihilate(f0),
    Create(f0),
    Create(f0),
    Create(f0),
  ])
  @asymptotic.chk(
    out,
    "Wick 正規序階層定理：⟨Ω| A(f_0)^n A†(f_0)^n |Ω⟩ 在 n=2, 3 時精確算出 \{@asymptotic.qv_show(vev_22)}!→2 與 \{@asymptotic.qv_show(vev_33)} = 3! = 6",
    @asymptotic.qv_eq(vev_22, @asymptotic.qv_int(2)) &&
    @asymptotic.qv_eq(vev_33, @asymptotic.qv_int(6)),
  )
  // 2. 連續高斯場算子 Φ(f) = A(f) + A†(f) 的 4 點關聯函數 Wick 配對定理：
  //    ⟨Ω | Φ(f_1) Φ(f_2) Φ(f_3) Φ(f_4) | Ω⟩
  //      = ⟨f_1,f_2⟩⟨f_3,f_4⟩ + ⟨f_1,f_3⟩⟨f_2,f_4⟩ + ⟨f_1,f_4⟩⟨f_2,f_3⟩（3 組配對和！）
  //    我們一方面把 Φ(f_i) = A(f_i) + A†(f_i) 展開為 2⁴ = 16 個單項場串列送入 wick_vacuum_expectation，
  //    另一方面獨立用 3 組配對公式計算，兩條完全獨立路徑必須逐位相等！
  let f1 = ContinuumTestFn::{ t_start: z0, t_end: z1, coeffs: [z1], }
  let f2 = ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [z0, @asymptotic.qv_int(2)],
  }
  let f3 = ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [@asymptotic.qv_one(), @asymptotic.qv_int(-1)],
  }
  let f4 = ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [z0, z0, @asymptotic.qv_int(3)],
  }
  let fs = [f1, f2, f3, f4]
  let mut wick_sum_16 = @asymptotic.qv_zero()
  for mask in 0..<16 {
    let word : Array[FieldFactor] = []
    for bit in 0..<4 {
      if ((mask >> bit) & 1) == 0 {
        word.push(Annihilate(fs[bit]))
      } else {
        word.push(Create(fs[bit]))
      }
    }
    wick_sum_16 = @asymptotic.qv_add(wick_sum_16, wick_vacuum_expectation(word))
  }
  let pair_formula = @asymptotic.qv_add(
    @asymptotic.qv_mul(continuum_l2_inner(f1, f2), continuum_l2_inner(f3, f4)),
    @asymptotic.qv_add(
      @asymptotic.qv_mul(continuum_l2_inner(f1, f3), continuum_l2_inner(f2, f4)),
      @asymptotic.qv_mul(continuum_l2_inner(f1, f4), continuum_l2_inner(f2, f3)),
    ),
  )
  @asymptotic.chk(
    out,
    "連續高斯場 4 點關聯 Wick 定理：16 支正規序展開總和 = \{@asymptotic.qv_show(wick_sum_16)} = 三配對公式",
    @asymptotic.qv_eq(wick_sum_16, pair_formula) &&
    !@asymptotic.qv_is_zero(wick_sum_16),
  )
  // 負控制：奇數個場算子的真空期望值恆為 0（粒子數宇稱守恆）
  let odd_vev = wick_vacuum_expectation([Annihilate(f1), Create(f2), Create(f3)])
  @asymptotic.chk(
    out,
    "負控制：粒子數不平衡場乘積 A(f_1)A†(f_2)A†(f_3) 真空期望值恆為 0",
    @asymptotic.qv_is_zero(odd_vev),
  )
  out
}

///|
pub fn law_weyl_symplectic_cocycle() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let z0 = @asymptotic.qv_zero()
  let z1 = @asymptotic.qv_one()
  let cf_add = (a : ComplexFieldFn, b : ComplexFieldFn) => ComplexFieldFn::{
    re: test_fn_add(a.re, b.re),
    im: test_fn_add(a.im, b.im),
  }
  let f = ComplexFieldFn::{
    re: ContinuumTestFn::{ t_start: z0, t_end: z1, coeffs: [z1, z1], },
    im: ContinuumTestFn::{
      t_start: z0,
      t_end: z1,
      coeffs: [@asymptotic.qv_int(2), @asymptotic.qv_int(-1)],
    },
  }
  let g = ComplexFieldFn::{
    re: ContinuumTestFn::{
      t_start: z0,
      t_end: z1,
      coeffs: [@asymptotic.qv_int(-1), @asymptotic.qv_int(3)],
    },
    im: ContinuumTestFn::{ t_start: z0, t_end: z1, coeffs: [z0, z1, z1], },
  }
  let h = ComplexFieldFn::{
    re: ContinuumTestFn::{ t_start: z0, t_end: z1, coeffs: [z1, z0, z1], },
    im: ContinuumTestFn::{
      t_start: z0,
      t_end: z1,
      coeffs: [@asymptotic.qv_int(3)],
    },
  }
  let s_fg = weyl_symplectic_form(f, g)
  let s_gf = weyl_symplectic_form(g, f)
  @asymptotic.chk(
    out,
    "Weyl 辛形式反對稱性：σ(f, g) = \{@asymptotic.qv_show(s_fg)} = −σ(g, f) 且 σ(f, f) = 0",
    @asymptotic.qv_eq(s_fg, @asymptotic.qv_neg(s_gf)) &&
    @asymptotic.qv_is_zero(weyl_symplectic_form(f, f)) &&
    !@asymptotic.qv_is_zero(s_fg),
  )
  // 群 2-上循環結合律恆等式（保證 (W(f)W(g))W(h) = W(f)(W(g)W(h))）：
  // σ(f, g) + σ(f + g, h) == σ(g, h) + σ(f, g + h)
  let cocycle_lhs = @asymptotic.qv_add(
    weyl_symplectic_form(f, g),
    weyl_symplectic_form(cf_add(f, g), h),
  )
  let cocycle_rhs = @asymptotic.qv_add(
    weyl_symplectic_form(g, h),
    weyl_symplectic_form(f, cf_add(g, h)),
  )
  @asymptotic.chk(
    out,
    "Weyl CCR 群 2-上循環定理：σ(f,g) + σ(f+g,h) = \{@asymptotic.qv_show(cocycle_lhs)} = σ(g,h) + σ(f,g+h)（保證連續場位移結合律）",
    @asymptotic.qv_eq(cocycle_lhs, cocycle_rhs),
  )
  out
}

///|
pub fn law_hudson_parthasarathy_ito() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let diffs = [ZeroDiff, Dt, DA, DADag, DLambda]
  // 1. 窮舉 5³ = 125 組微元三元組驗證量子 Itô 乘法結合律：(x · y) · z == x · (y · z)
  let mut assoc_ok = true
  let mut non_comm_cnt = 0
  for x in diffs {
    for y in diffs {
      if quantum_ito_mul(x, y) != quantum_ito_mul(y, x) {
        non_comm_cnt = non_comm_cnt + 1
      }
      for z in diffs {
        if quantum_ito_mul(quantum_ito_mul(x, y), z) !=
          quantum_ito_mul(x, quantum_ito_mul(y, z)) {
          assoc_ok = false
        }
      }
    }
  }
  @asymptotic.chk(
    out,
    "Hudson–Parthasarathy 量子 Itô 微元代數：5³ = 125 組三元組全數滿足結合律，且存在 \{non_comm_cnt} 對非交換微元（如 dA·dA† = dt ≠ 0 = dA†·dA）",
    assoc_ok && non_comm_cnt == 6,
  )
  // 2. 量子隨機演化么正性定理（Hudson–Parthasarathy Unitarity Theorem）：
  //    設 dU = U · dG，若 dU 為么正（即 dG + dG† + dG† · dG = 0 與 dG + dG† + dG · dG† = 0），
  //    取標準耗散耦合生成元（W = I 時）：L = 1 + i（|L|² = 2），H = 1（自伴）：
  //      dG = (-(1/2)|L|² - i H) dt - L† dA + L dA†
  //    驗證量子 Itô 修正項 dG† · dG = |L|² dt 恰好抵消 -(1/2)|L|² dt + (-(1/2)|L|²) dt = -|L|² dt！
  let l_op = @unbounded.qc_make(@asymptotic.qv_one(), @asymptotic.qv_one())
  let l_norm2 = @unbounded.qc_norm_sq(l_op) // 2
  let drift = @unbounded.qc_make(
    @asymptotic.qv_mul(@asymptotic.qv_frac(-1, 2), l_norm2),
    @asymptotic.qv_int(-1),
  )
  let dg = QuantumSdeIncrement::{
    c_dt: drift,
    c_da: @unbounded.qc_neg(@unbounded.qc_conj(l_op)),
    c_dadag: l_op,
    c_dlambda: @unbounded.qc_zero(),
  }
  let dg_dag = qsde_adjoint(dg)
  let ito_corr_1 = qsde_ito_product(dg_dag, dg)
  let ito_corr_2 = qsde_ito_product(dg, dg_dag)
  let iso_1 = qsde_add(qsde_add(dg, dg_dag), ito_corr_1)
  let iso_2 = qsde_add(qsde_add(dg, dg_dag), ito_corr_2)
  let zero_inc = QuantumSdeIncrement::{
    c_dt: @unbounded.qc_zero(),
    c_da: @unbounded.qc_zero(),
    c_dadag: @unbounded.qc_zero(),
    c_dlambda: @unbounded.qc_zero(),
  }
  @asymptotic.chk(
    out,
    "量子隨機微分方程么正性定理：dG + dG† + dG†·dG = 0 且 dG + dG† + dG·dG† = 0（Itô 修正項 |L|²dt = 2dt 精確抵消耗散漂移）",
    qsde_eq(iso_1, zero_inc) && qsde_eq(iso_2, zero_inc),
  )
  // 負控制：若忽略 Itô 二次變差修正項（古典樸素鏈鎖律 dG + dG†），結果為 -2 dt ≠ 0，破壞么正概率守恆！
  @asymptotic.chk(
    out,
    "負控制：忽略量子 Itô 修正項時 dG + dG† = (−2)dt ≠ 0（概率外洩）",
    !qsde_eq(qsde_add(dg, dg_dag), zero_inc),
  )
  out
}

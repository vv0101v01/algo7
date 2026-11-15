// ---------------------------------------------------------------------------
// qprob/context_cat/laws.mbt — 第六階雙範疇、命題纖維化、機率單子與量子機率脈絡合流定律
// ---------------------------------------------------------------------------

///|
pub fn context_cat_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    (
      "空間與子場雙範疇 ℬ_qprob：1-態射路徑、2-態射 Whiskering 與 Godement 縱橫互換律",
      law_space_subfield_bicategory(),
    ),
    (
      "主命題纖維化 π : ∫ Prop → ℬ_qprob：逆變拉回贗函子、笛卡兒提升與泛因式分解",
      law_principal_prop_fibration(),
    ),
    (
      "精確有理機率單子 D_ℚ：單子三律、Kleisli 馬可夫複合、Fubini 積與 CPTP 對偶",
      law_rational_probability_monad(),
    ),
    (
      "量子機率脈絡範疇 QProbCtx：Bohr 相容性判準、Naimark 脈絡自然性與菱形合流大定理",
      law_quantum_context_confluence(),
    ),
  ]
}

///|
fn mk_diag_op(vals : Array[@asymptotic.QVal]) -> @unbounded.UnboundedOp {
  let d = vals.length()
  let es = Array::make(d * d, @unbounded.qc_zero())
  for i in 0..<d {
    es[i * d + i] = @unbounded.qc_real(vals[i])
  }
  @unbounded.UnboundedOp::{ dim: d, growth_deg: 0, entries: es, }
}

// ---------------------------------------------------------------------------
// 1. 空間與子場雙範疇 ℬ_qprob
// ---------------------------------------------------------------------------

///|
pub fn law_space_subfield_bicategory() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let z0 = @asymptotic.qv_zero()
  let z1 = @asymptotic.qv_one()

  // (a) 子場塔 1-態射分裂冪等：ℚ ↪ ℚ(√2) → ℚ 與 ℚ ↪ ℚ((ε))_≤4 → ℚ 在基體元素上精確左逆
  let r_sample = @asymptotic.qv_frac(-7, 11)
  let quad_rt = subfield_quad_roundtrip(r_sample, 2)
  let jet_rt = match
    subfield_jet_roundtrip(r_sample, @asymptotic.qv_frac(9, 5), 4) {
    Some(v) => @asymptotic.qv_eq(v, r_sample)
    None => false
  }
  @asymptotic.chk(
    out,
    "子場 1-態射左逆截面：(1/2)Tr∘ι_√2(-7/11) = \{@asymptotic.qv_show(quad_rt)} 且 st∘ι_ε(-7/11 + 9/5·ε) = -7/11",
    @asymptotic.qv_eq(quad_rt, r_sample) && jet_rt,
  )

  // (b) 跨空間 1-態射鏈結合律與單位律：
  //     ℚ ↪ Op*(𝒟_4) → ℱ_0(ℚ¹) → CCR(L²) → NCMeas_≤4
  let f_q_unb = bicat_atom1(
    SubfieldQ,
    SpaceUnbounded(4),
    "scalar_embed",
    @asymptotic.qv_int(2),
    true,
  )
  let f_unb_fock = bicat_atom1(
    SpaceUnbounded(4),
    SpaceFock(1, z0),
    "fock_lift",
    z1,
    true,
  )
  let f_fock_nc = bicat_atom1(
    SpaceFock(1, z0),
    SpaceNcMeasure(4),
    "vacuum_law",
    @asymptotic.qv_int(3),
    true,
  )
  let assoc_unit_ok = match
    (
      bicat_comp1(f_unb_fock, f_q_unb),
      bicat_comp1(f_fock_nc, f_unb_fock),
      bicat_comp1(bicat_id1(SpaceUnbounded(4)), f_q_unb),
      bicat_comp1(f_q_unb, bicat_id1(SubfieldQ)),
    ) {
    (Some(gf), Some(hg), Some(lu), Some(ru)) =>
      match (bicat_comp1(f_fock_nc, gf), bicat_comp1(hg, f_q_unb)) {
        (Some(lhs), Some(rhs)) =>
          bicat_eq1(lhs, rhs) &&
          bicat_eq1(lu, f_q_unb) &&
          bicat_eq1(ru, f_q_unb) &&
          @asymptotic.qv_eq(lhs.scale_factor, @asymptotic.qv_int(6)) &&
          cell0_label(lhs.dom) == "ℚ" &&
          cell0_label(lhs.cod) == "NCMeas_≤4"
        _ => false
      }
    _ => false
  }
  @asymptotic.chk(
    out, "空間與子場 1-態射範疇律：(h ∘_h g) ∘_h f == h ∘_h (g ∘_h f) 且左右單位 id_X 嚴格成立",
    assoc_unit_ok,
  )

  // (c) 雙範疇 2-態射 Godement 縱橫互換律（Interchange Law）：
  //     X = SubfieldJet(4) ⇉ Y = SpaceContinuumCCR(2) ⇉ Z = SpaceNcMeasure(4)
  let f1 = bicat_atom1(
    SubfieldJet(4),
    SpaceContinuumCCR(2),
    "lattice_N2",
    @asymptotic.qv_int(2),
    true,
  )
  let f2 = bicat_atom1(
    SubfieldJet(4),
    SpaceContinuumCCR(2),
    "lattice_N4",
    @asymptotic.qv_int(2),
    true,
  )
  let f3 = bicat_atom1(
    SubfieldJet(4),
    SpaceContinuumCCR(2),
    "richardson_cont",
    @asymptotic.qv_int(2),
    true,
  )
  let g1 = bicat_atom1(
    SpaceContinuumCCR(2),
    SpaceNcMeasure(4),
    "wick_raw",
    @asymptotic.qv_int(3),
    true,
  )
  let g2 = bicat_atom1(
    SpaceContinuumCCR(2),
    SpaceNcMeasure(4),
    "wick_ordered",
    @asymptotic.qv_int(3),
    true,
  )
  let g3 = bicat_atom1(
    SpaceContinuumCCR(2),
    SpaceNcMeasure(4),
    "cumulant_law",
    @asymptotic.qv_int(3),
    true,
  )
  let interchange_ok = match
    (
      bicat_make2(f1, f2, @asymptotic.qv_frac(1, 4), "rich_step1"),
      bicat_make2(f2, f3, @asymptotic.qv_frac(-1, 8), "rich_step2"),
      bicat_make2(g1, g2, @asymptotic.qv_frac(2, 5), "ito_corr1"),
      bicat_make2(g2, g3, @asymptotic.qv_frac(3, 10), "ito_corr2"),
    ) {
    (Some(a1), Some(a2), Some(b1), Some(b2)) =>
      bicat_check_interchange(b2, b1, a2, a1) &&
      (match bicat_vcomp2(bicat_id2(f2), a1) {
        Some(u) => bicat_eq2(u, a1)
        None => false
      })
    _ => false
  }
  @asymptotic.chk(
    out, "雙範疇 Godement 縱橫互換律：(β₂ ∘_h α₂) ∘_v (β₁ ∘_h α₁) == (β₂ ∘_v β₁) ∘_h (α₂ ∘_v α₁) 精確成立",
    interchange_ok,
  )

  // (d) 負控制：不同源匯或不相容 1-態射／2-態射複合被雙範疇型別檢查拒絕
  let bad_comp1 = bicat_comp1(f1, g1) is None
  let bad_cell2 = bicat_make2(f1, g1, z0, "mismatch") is None
  let bad_vcomp2 = match
    (bicat_make2(f1, f2, z1, "a"), bicat_make2(f1, f3, z1, "b")) {
    (Some(x), Some(y)) => bicat_vcomp2(y, x) is None
    _ => false
  }
  @asymptotic.chk(
    out,
    "負控制：不相容源匯之 1-態射複合、跨端點偽 2-胞與錯位垂直複合皆被拒絕 (None)",
    bad_comp1 && bad_cell2 && bad_vcomp2,
  )
  out
}

// ---------------------------------------------------------------------------
// 2. Grothendieck 主命題纖維化 π : ∫ Prop → ℬ_qprob 與主命題間態射
// ---------------------------------------------------------------------------

///|
pub fn law_principal_prop_fibration() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let z0 = @asymptotic.qv_zero()
  let z1 = @asymptotic.qv_one()

  // (a) 八大空間與子場錨定主命題切面全部為真，且子場族不變量 = 1、量子空間族不變量 = 2
  let sec = canonical_principal_prop_section()
  let mut all_hold = sec.length() == 8
  for p in sec {
    if !p.holds {
      all_hold = false
    }
  }
  let inv_split_ok = @asymptotic.qv_eq(sec[0].invariant, z1) &&
    @asymptotic.qv_eq(sec[1].invariant, z1) &&
    @asymptotic.qv_eq(sec[2].invariant, z1) &&
    @asymptotic.qv_eq(sec[3].invariant, @asymptotic.qv_int(2)) &&
    @asymptotic.qv_eq(sec[5].invariant, @asymptotic.qv_int(2)) &&
    @asymptotic.qv_eq(sec[7].invariant, @asymptotic.qv_int(2))
  @asymptotic.chk(
    out,
    "八空間與子場主命題錨定切面：ℚ / ℚ(√2) / ℚ((ε)) (不變量=1) 與極限 / 無界 / 福克 / 連續場 / 測度 (不變量=2) 全部實算成立",
    all_hold && inv_split_ok,
  )

  // (b) 逆變拉回贗函子律：(g ∘_h f)*(R) == f*(g*(R)) 且 (id_Z)*(R) == R
  let p_nc = sec[7] // SpaceNcMeasure(4), invariant = 2
  let u_fock_ccr = bicat_atom1(
    SpaceFock(1, z0),
    SpaceContinuumCCR(0),
    "smear",
    z1,
    true,
  )
  let f_ccr_nc = bicat_atom1(
    SpaceContinuumCCR(0),
    SpaceNcMeasure(4),
    "born_law",
    z1,
    true,
  )
  let contravariant_ok = match bicat_comp1(f_ccr_nc, u_fock_ccr) {
    Some(gf) =>
      match
        (
          pullback_principal_prop(gf, p_nc),
          pullback_principal_prop(f_ccr_nc, p_nc),
          pullback_principal_prop(bicat_id1(p_nc.base), p_nc),
        ) {
        (Some(lhs), Some(mid), Some(id_pull)) =>
          match pullback_principal_prop(u_fock_ccr, mid) {
            Some(rhs) => fiber_prop_eq(lhs, rhs) && fiber_prop_eq(id_pull, p_nc)
            None => false
          }
        _ => false
      }
    None => false
  }
  @asymptotic.chk(
    out, "主命題纖維化逆變拉回定律：(g ∘_h f)*(R) == f*(g*(R)) 且 (id_Z)*(R) == R",
    contravariant_ok,
  )

  // (c) 笛卡兒提升泛因式分解定理：強命題 P_strong (rank=3) 沿 f∘u 至 R (rank=2) 唯一分解過 Cart(f, R)
  let p_fock_strong = FiberPrincipalProp::{
    base: SpaceFock(1, z0),
    prop_code: "quantum-moment-4",
    statement: "ℱ_0(ℚ¹) 強 Cuntz–Toeplitz 半圓四階矩證書",
    invariant: @asymptotic.qv_int(2),
    strength_rank: 3,
    holds: true,
  }
  let cart_factor_ok = match
    (bicat_comp1(f_ccr_nc, u_fock_ccr), cartesian_lift_morphism(f_ccr_nc, p_nc)) {
    (Some(tot_base), Some(cart_f)) =>
      match make_prop_morphism(p_fock_strong, p_nc, tot_base) {
        Some(h_tot) =>
          !h_tot.is_cartesian &&
          cart_f.is_cartesian &&
          (match factor_through_cartesian_lift(h_tot, u_fock_ccr, cart_f) {
            Some(u_bar) =>
              match
                (
                  prop_morphism_comp(cart_f, u_bar),
                  prop_morphism_comp(u_bar, prop_morphism_id(p_fock_strong)),
                ) {
                (Some(recomp), Some(u_id)) =>
                  fiber_prop_eq(recomp.src, h_tot.src) &&
                  fiber_prop_eq(recomp.tgt, h_tot.tgt) &&
                  bicat_eq1(recomp.base_map, h_tot.base_map) &&
                  bicat_eq1(u_id.base_map, u_bar.base_map)
                _ => false
              }
            None => false
          })
        None => false
      }
    _ => false
  }
  @asymptotic.chk(
    out, "Grothendieck 笛卡兒提升泛性質：任意主命題態射 h : (X,P) → (Z,R) 沿 f∘u 唯一分解為 Cart(f,R) ∘ ū",
    cart_factor_ok,
  )

  // (d) 跨五階主命題態射鏈：SpaceProjTower → SpaceUnbounded → SpaceFock → SpaceContinuumCCR → SpaceNcMeasure 全鏈貫通，
  //     且負控制（破壞正定性 `q=2` 態射或由真推假）被主命題態射檢查器拒絕
  let m12 = make_prop_morphism(
    sec[3],
    sec[4],
    bicat_atom1(sec[3].base, sec[4].base, "core_dense", z1, true),
  )
  let m23 = make_prop_morphism(
    sec[4],
    sec[5],
    bicat_atom1(sec[4].base, sec[5].base, "second_quant", z1, true),
  )
  let m34 = make_prop_morphism(sec[5], sec[6], u_fock_ccr)
  let m45 = make_prop_morphism(sec[6], sec[7], f_ccr_nc)
  let chain_ok = match (m12, m23, m34, m45) {
    (Some(a), Some(b), Some(c), Some(d)) =>
      match prop_morphism_comp(b, a) {
        Some(ab) =>
          match prop_morphism_comp(c, ab) {
            Some(abc) =>
              match prop_morphism_comp(d, abc) {
                Some(abcd) =>
                  abcd.is_cartesian &&
                  abcd.src.base == SpaceProjTower(2) &&
                  abcd.tgt.base == SpaceNcMeasure(4)
                None => false
              }
            None => false
          }
        None => false
      }
    _ => false
  }
  let non_pos_map = bicat_atom1(
    sec[5].base,
    sec[7].base,
    "q2_ghost_deformation",
    z1,
    false,
  )
  let neg_ctrl_rejected = make_prop_morphism(sec[5], sec[7], non_pos_map)
    is None
  @asymptotic.chk(
    out,
    "五階主命題笛卡兒態射鏈貫通（極限→無界→福克→連續場→非交換測度），且非正定變形態射被拒絕",
    chain_ok && neg_ctrl_rejected,
  )
  out
}

// ---------------------------------------------------------------------------
// 3. 精確有理機率單子 D_ℚ 統一機率脈絡
// ---------------------------------------------------------------------------

///|
pub fn law_rational_probability_monad() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []

  // 構造測試分佈與隨機核 k, h : Int32 -> ProbDist[Int32]
  let d0 = match
    dist_normalize([
      (0, @asymptotic.qv_frac(1, 3)),
      (1, @asymptotic.qv_frac(1, 2)),
      (0, @asymptotic.qv_frac(1, 6)),
    ]) {
    Some(d) => d
    None => abort("unexpected d0")
  }
  let k_kern = (x : Int32) => {
    match
      dist_normalize([
        (x, @asymptotic.qv_frac(2, 5)),
        (x + 1, @asymptotic.qv_frac(3, 5)),
      ]) {
      Some(d) => d
      None => abort("unexpected k_kern")
    }
  }
  let h_kern = (y : Int32) => {
    match
      dist_normalize([
        (y * 2, @asymptotic.qv_frac(1, 4)),
        (y + 3, @asymptotic.qv_frac(3, 4)),
      ]) {
      Some(d) => d
      None => abort("unexpected h_kern")
    }
  }

  // (a) Kleisli 與 Eilenberg–Moore 機率單子三律：
  //     1. 左單位 bind(pure(x), k) == k(x)
  //     2. 右單位 bind(d0, pure) == d0
  //     3. 結合律 bind(bind(d0, k), h) == bind(d0, x => bind(k(x), h))
  let left_unit = dist_eq(dist_bind(dist_pure(1), k_kern), k_kern(1))
  let right_unit = dist_eq(dist_bind(d0, (x : Int32) => dist_pure(x)), d0)
  let assoc_bind = dist_eq(
    dist_bind(dist_bind(d0, k_kern), h_kern),
    kleisli_compose(k_kern, h_kern)(0),
  )
  let assoc_full = dist_eq(
    dist_bind(dist_bind(d0, k_kern), h_kern),
    dist_bind(d0, kleisli_compose(k_kern, h_kern)),
  )
  // 雙層分佈壓平律：μ(η_{D(X)}(d0)) == d0 且 μ(D(η_X)(d0)) == d0，且同支撐自動合併 d0(0) = 1/3 + 1/6 = 1/2
  let outer_eta = dist_pure(d0)
  let inner_eta = dist_map(d0, (x : Int32) => dist_pure(x))
  let mu_unit_ok = dist_eq(dist_flatten(outer_eta), d0) &&
    dist_eq(dist_flatten(inner_eta), d0) &&
    @asymptotic.qv_eq(dist_prob(d0, 0), @asymptotic.qv_frac(1, 2)) &&
    !assoc_bind
  @asymptotic.chk(
    out,
    "Giry–Lawvere 有理機率單子 (D_ℚ, η, μ) 滿足左右單位律、Kleisli 結合律與雙層壓平恆等式",
    left_unit && right_unit && assoc_full && mu_unit_ok,
  )

  // (b) 強交換單子張量積 Fubini 定律：邊際化 π₁*(d_A ⊗ d_B) == d_A, π₂*(d_A ⊗ d_B) == d_B 且獨立乘積期望分解
  let db = k_kern(2)
  let prod = dist_product(d0, db)
  let marg1 = dist_map(prod, p => p.0)
  let marg2 = dist_map(prod, p => p.1)
  let exp_prod = dist_expect_q(prod, p => {
    @asymptotic.qv_mul(@asymptotic.qv_int(p.0), @asymptotic.qv_int(p.1))
  })
  let exp_sep = @asymptotic.qv_mul(
    dist_expect_q(d0, a => @asymptotic.qv_int(a)),
    dist_expect_q(db, b => @asymptotic.qv_int(b)),
  )
  @asymptotic.chk(
    out,
    "交換機率單子 Fubini 定律：邊際投影 π₁*(p⊗q)=p、π₂*(p⊗q)=q，且 𝔼[X·Y] = 𝔼[X]·𝔼[Y]",
    dist_eq(marg1, d0) &&
    dist_eq(marg2, db) &&
    @asymptotic.qv_eq(exp_prod, exp_sep),
  )

  // (c) CPTP 量子通道與 Kleisli 機率單子對偶：振幅阻尼型勾股 Kraus 通道後接對角 POVM 量測，
  //     Schrödinger 密度演化與 Heisenberg 複合單子邊際分佈完全一致
  let k0 = mk_diag_op([@asymptotic.qv_one(), @asymptotic.qv_frac(3, 5)])
  let k1 = @unbounded.UnboundedOp::{
    dim: 2,
    growth_deg: 0,
    entries: [
      @unbounded.qc_zero(),
      @unbounded.qc_real(@asymptotic.qv_frac(4, 5)),
      @unbounded.qc_zero(),
      @unbounded.qc_zero(),
    ],
  }
  let obs_z = @nc_measure.PovmMeasure::{
    dim: 2,
    kraus_roots: [
      mk_diag_op([@asymptotic.qv_one(), @asymptotic.qv_zero()]),
      mk_diag_op([@asymptotic.qv_zero(), @asymptotic.qv_one()]),
    ],
  }
  let st_plus = match
    @unbounded.qstate_pure([
      @unbounded.qc_real(@asymptotic.qv_frac(3, 5)),
      @unbounded.qc_real(@asymptotic.qv_frac(4, 5)),
    ]) {
    Some(s) => s
    None => abort("unexpected st_plus")
  }
  @asymptotic.chk(
    out,
    "CPTP 量子馬可夫通道 × 機率單子對偶：Born(Φ(ρ), E) == D_ℚ(π₂)(Born(ρ, E∘Φ*))",
    verify_cptp_kleisli_duality([k0, k1], st_plus, obs_z),
  )

  // (d) 負控制：零總質量或含負權重（如 q=2 幽靈態或 Wigner 準機率負值）被 D_ℚ 正規化器拒絕
  let neg_rejected = dist_normalize([
      (0, @asymptotic.qv_frac(3, 2)),
      (1, @asymptotic.qv_frac(-1, 2)),
    ])
    is None
  let zero_rejected = dist_normalize([(0, @asymptotic.qv_zero())]) is None
  @asymptotic.chk(
    out,
    "負控制：含負權重準機率 [3/2, -1/2] 與零質量分佈皆被機率單子 D_ℚ 拒絕 (None)",
    neg_rejected && zero_rejected,
  )
  out
}

// ---------------------------------------------------------------------------
// 4. 量子機率脈絡範疇 QProbCtx 與合流大定理
// ---------------------------------------------------------------------------

///|
pub fn law_quantum_context_confluence() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let z0 = @asymptotic.qv_zero()
  let z1 = @asymptotic.qv_one()

  // 構造 4 維雙量子位元（2-qubit，ℋ = ℂ² ⊗ ℂ² ≅ ℂ⁴）上的交換觀測量族與量子概率態：
  //   Z₁ = diag(1, 1, -1, -1)（第一粒子自旋 Z）
  //   Z₂ = diag(1, -1, 1, -1)（第二粒子自旋 Z）
  //   ZZ = Z₁·Z₂ = diag(1, -1, -1, 1)（宇稱奇偶觀測量）
  //   注意 [Z₁, Z₂] = [Z₁, ZZ] = [Z₂, ZZ] = 0（構成相容 Bohr 交換觀測脈絡格！）
  let minus1 = @asymptotic.qv_int(-1)
  let z_first = mk_diag_op([z1, z1, minus1, minus1])
  let z_second = mk_diag_op([z1, minus1, z1, minus1])
  let zz_parity = mk_diag_op([z1, minus1, minus1, z1])

  // 非均勻糾纏／相干純態 |ψ⟩ ∝ (1, 2, 2, 4)（範數平方 1+4+4+16 = 25，機率分佈 [1/25, 4/25, 4/25, 16/25]）
  let st4 = match
    @unbounded.qstate_pure([
      @unbounded.qc_real(z1),
      @unbounded.qc_real(@asymptotic.qv_int(2)),
      @unbounded.qc_real(@asymptotic.qv_int(2)),
      @unbounded.qc_real(@asymptotic.qv_int(4)),
    ]) {
    Some(s) => s
    None => abort("unexpected st4")
  }

  // 頂點精細脈絡 C_apex：4 個計算基底投影 P_0, P_1, P_2, P_3，同時分辨 (Z₁, Z₂, ZZ)
  let p0 = mk_diag_op([z1, z0, z0, z0])
  let p1 = mk_diag_op([z0, z1, z0, z0])
  let p2 = mk_diag_op([z0, z0, z1, z0])
  let p3 = mk_diag_op([z0, z0, z0, z1])
  let ctx_apex = QuantumProbContext::{
    name: "C_apex(Z1,Z2,ZZ)",
    base_cell: SpaceUnbounded(4),
    state: st4,
    commuting_obs: [z_first, z_second, zz_parity],
    povm: @nc_measure.PovmMeasure::{ dim: 4, kraus_roots: [p0, p1, p2, p3], },
  }

  // 左分支脈絡 C_left（保留 0 態與 3 態，合併 {1, 2} 為奇宇稱單一結果）：3 個結果 [P_0, P_{1,2}, P_3]
  // 注意 P_{1,2} = diag(0,1,1,0) 與 ZZ = diag(1,-1,-1,1) 對易！
  let p12 = mk_diag_op([z0, z1, z1, z0])
  let ctx_left = QuantumProbContext::{
    name: "C_left(0,{1,2},3)",
    base_cell: SpaceNcMeasure(3),
    state: st4,
    commuting_obs: [zz_parity],
    povm: @nc_measure.PovmMeasure::{ dim: 4, kraus_roots: [p0, p12, p3], },
  }

  // 右分支脈絡 C_right（合併 {0, 3} 為偶宇稱單一結果，保留 1 態與 2 態）：3 個結果 [P_{0,3}, P_1, P_2]
  let p03 = mk_diag_op([z1, z0, z0, z1])
  let ctx_right = QuantumProbContext::{
    name: "C_right({0,3},1,2)",
    base_cell: SpaceNcMeasure(3),
    state: st4,
    commuting_obs: [zz_parity],
    povm: @nc_measure.PovmMeasure::{ dim: 4, kraus_roots: [p03, p1, p2], },
  }

  // 匯流底點脈絡 C_parity（最終宇稱脈絡 ZZ：偶宇稱 {0,3} vs 奇宇稱 {1,2}）：2 個結果 [P_{0,3}, P_{1,2}]
  let ctx_parity = QuantumProbContext::{
    name: "C_nadir(ZZ_parity)",
    base_cell: SpaceNcMeasure(2),
    state: st4,
    commuting_obs: [zz_parity],
    povm: @nc_measure.PovmMeasure::{ dim: 4, kraus_roots: [p03, p12], },
  }

  // (a) 驗證四個相容脈絡與恆等態射良構，且奇偶機率精確為 P(even) = 17/25, P(odd) = 8/25
  let id_ok = qctx_morphism_is_valid(qctx_morphism_id(ctx_apex))
  let parity_probs_ok = match qctx_to_prob_monad(ctx_parity) {
    Some(dp) =>
      @asymptotic.qv_eq(dist_prob(dp, 0), @asymptotic.qv_frac(17, 25)) &&
      @asymptotic.qv_eq(dist_prob(dp, 1), @asymptotic.qv_frac(8, 25))
    None => false
  }
  @asymptotic.chk(
    out,
    "量子機率脈絡範疇 QProbCtx 良構性：相容對易觀測量族 [Z₁, Z₂, ZZ] 通過 Bohr 公理，宇稱分佈 = [17/25, 8/25]",
    qctx_is_valid(ctx_apex) && id_ok && parity_probs_ok,
  )

  // (b) 量子機率脈絡菱形合流大定理（Diamond Confluence in QProbCtx）：
  //     C_apex ──left_leg──▶ C_left ──left_join──▶ C_parity
  //       │                                           ▲
  //     right_leg                                 right_join
  //       ▼                                           │
  //     C_right ──────────────────────────────────────┘
  let left_leg = ContextMorphism::{
    src: ctx_apex,
    tgt: ctx_left,
    outcome_map: [0, 1, 1, 2],
  }
  let right_leg = ContextMorphism::{
    src: ctx_apex,
    tgt: ctx_right,
    outcome_map: [0, 1, 2, 0],
  }
  let left_join = ContextMorphism::{
    src: ctx_left,
    tgt: ctx_parity,
    outcome_map: [0, 1, 0],
  }
  let right_join = ContextMorphism::{
    src: ctx_right,
    tgt: ctx_parity,
    outcome_map: [0, 1, 1],
  }
  @asymptotic.chk(
    out,
    "量子機率脈絡菱形合流定理：兩條不等價中間粗粒化脈絡 C_left ≠ C_right 在 QProbCtx 與機率單子 D_ℚ 下零誤差合流至 C_parity",
    verify_qctx_diamond_confluence(left_leg, right_leg, left_join, right_join),
  )

  // (b2) 脈絡預層截面自然性（Heisenberg–Bohr Presheaf Section Gluing）：
  //      粗脈絡觀測量函數在粗單子分佈、拉回細單子分佈與算子跡泛函三路完全吻合
  let presheaf_gluing_ok = verify_qctx_presheaf_section(left_leg, [
      @asymptotic.qv_int(5),
      @asymptotic.qv_int(-3),
      @asymptotic.qv_int(2),
    ]) &&
    verify_qctx_presheaf_section(right_leg, [
      @asymptotic.qv_int(4),
      @asymptotic.qv_int(-1),
      @asymptotic.qv_int(7),
    ])
  @asymptotic.chk(
    out, "脈絡預層截面自然性：粗觀測量在粗單子 𝔼_{D_ℚ(C_coarse)}、細單子拉回 𝔼_{D_ℚ(C_fine)}∘π 與算子跡 Tr(ρ A) 三路恆等",
    presheaf_gluing_ok,
  )

  // (c) 跨空間合流閉環：連續場波包 L² 範數 → 全福克半圓場 X = ℓ*+ℓ（3 維截斷譜 {-1, 0, +1}）→
  //     具體量子機率脈絡 Born 分佈 [1/4, 1/2, 1/4]，其單子矩 [1, 0, 1/2? -> 實算 X = [[0,1,0],[1,0,1],[0,1,0]] 在 |0⟩ 機率 [1/4, 1/2, 1/4]?
  //     在 2 維截斷 X₂ = [[0,1],[1,0]]（本徵值 ±1，各機率 1/2），Born 單子矩 [1, 0, 1, 0, 1] 對應 Rademacher 自由元，
  //     再經 Free CLT 合流回半圓律！驗證 2 維 Pauli-X 脈絡與對角 Hadamard 轉換下機率單子期望值 Tr(ρ X₂²) = 1！
  let pauli_x = @unbounded.UnboundedOp::{
    dim: 2,
    growth_deg: 0,
    entries: [
      @unbounded.qc_zero(),
      @unbounded.qc_one(),
      @unbounded.qc_one(),
      @unbounded.qc_zero(),
    ],
  }
  // X 的正負本徵投影根：M_+ = (1/2)[[1,1],[1,1]]（冪等投影 M_+† M_+ = M_+！），M_- = (1/2)[[1,-1],[-1,1]]
  let half = @asymptotic.qv_frac(1, 2)
  let mhc = @unbounded.qc_real(@asymptotic.qv_frac(-1, 2))
  let hc = @unbounded.qc_real(half)
  let proj_plus = @unbounded.UnboundedOp::{
    dim: 2,
    growth_deg: 0,
    entries: [hc, hc, hc, hc],
  }
  let proj_minus = @unbounded.UnboundedOp::{
    dim: 2,
    growth_deg: 0,
    entries: [hc, mhc, mhc, hc],
  }
  let vac2 = match
    @unbounded.qstate_pure([@unbounded.qc_one(), @unbounded.qc_zero()]) {
    Some(s) => s
    None => abort("unexpected vac2")
  }
  let ctx_x = QuantumProbContext::{
    name: "C_PauliX",
    base_cell: SpaceFock(1, z0),
    state: vac2,
    commuting_obs: [pauli_x],
    povm: @nc_measure.PovmMeasure::{
      dim: 2,
      kraus_roots: [proj_plus, proj_minus],
    },
  }
  let x_monad_ok = match qctx_to_prob_monad(ctx_x) {
    Some(dx) => {
      let eig = (i : Int32) => if i == 0 { z1 } else { minus1 }
      let m1_monad = dist_expect_q(dx, i => eig(i))
      let m2_monad = dist_expect_q(dx, i => @asymptotic.qv_mul(eig(i), eig(i)))
      let m1_op = @unbounded.qstate_expect(vac2, pauli_x).re
      let m2_op = @unbounded.qstate_expect(
          vac2,
          @unbounded.uop_mul(pauli_x, pauli_x),
        ).re
      @asymptotic.qv_eq(dist_prob(dx, 0), half) &&
      @asymptotic.qv_eq(dist_prob(dx, 1), half) &&
      @asymptotic.qv_eq(m1_monad, m1_op) &&
      @asymptotic.qv_eq(m2_monad, m2_op)
    }
    None => false
  }
  @asymptotic.chk(
    out,
    "非對角交換脈絡 C(σ_x) 譜合流：機率單子期望值 𝔼_{D_ℚ}[λ^k] 與算子代數跡泛函 φ(σ_x^k) 精確一致",
    qctx_is_valid(ctx_x) && x_monad_ok,
  )

  // (d) 負控制（Kochen–Specker / Heisenberg 脈絡性阻礙）：
  //     1. 將非對易觀測量 σ_x 與 σ_z 強行塞入同一脈絡（[σ_x, σ_z] ≠ 0）必被 `qctx_is_valid` 拒絕；
  //     2. 錯誤接線的粗粒化映射 `[0, 0, 1, 2]`（違反效應算子拉回守恆）必被 `qctx_morphism_is_valid` 拒絕！
  let pauli_z = mk_diag_op([z1, minus1])
  let incompatible_ctx = QuantumProbContext::{
    name: "Incompatible(X,Z)",
    base_cell: SpaceUnbounded(2),
    state: vac2,
    commuting_obs: [pauli_x, pauli_z],
    povm: ctx_x.povm,
  }
  let bad_coarse = ContextMorphism::{
    src: ctx_apex,
    tgt: ctx_left,
    outcome_map: [0, 0, 1, 2],
  }
  @asymptotic.chk(
    out,
    "負控制（Heisenberg 脈絡不相容阻礙）：非對易脈絡 {σ_x, σ_z} 與不守恆粗粒化映射皆被 QProbCtx 拒絕",
    !qctx_is_valid(incompatible_ctx) &&
    qctx_to_prob_monad(incompatible_ctx) is None &&
    !qctx_morphism_is_valid(bad_coarse),
  )

  // (e) 四層終極合流大定理：雙範疇 ℬ_qprob → 主命題纖維化 ∫ Prop → 機率單子 Kl(D_ℚ) → 量子機率脈絡範疇 QProbCtx
  let grand = verify_grand_qprob_context_confluence()
  @asymptotic.chk(
    out,
    "六階終極合流大定理：雙範疇 \{grand.bicat_cells_verified} 空間子場 × 主命題纖維化 \{grand.fibered_props_verified}/8 × 機率單子 D_ℚ × 量子機率脈絡範疇 QProbCtx 全鏈合流",
    grand.all_holds,
  )
  out
}

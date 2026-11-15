// ---------------------------------------------------------------------------
// qprob/unbounded/laws.mbt — 第二階數學結構定律總表（無界算子概率空間）
// ---------------------------------------------------------------------------

///|
pub fn unbounded_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    (
      "無界 *-代數 Op*(𝒟)：多項式成長階封閉性、伴隨對合與 Jacobi 恆等式",
      law_unbounded_star_algebra(),
    ),
    (
      "量子概率態 φ：正定性、GNS Cauchy–Schwarz 與純／混合態構造",
      law_quantum_prob_states(),
    ),
    (
      "Robertson–Schrödinger 無界不確定性原理與緊緻下界飽和",
      law_uncertainty_principle(),
    ),
    (
      "Yosida 預解漸近正則化與 Favard–Lanczos 矩問題重構定理",
      law_yosida_and_moment_reconstruction(),
    ),
  ]
}

///|
pub fn law_unbounded_star_algebra() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let d = 5
  let n_op = uop_number_op(d)
  let q_op = uop_jacobi_tridiag(
    [
      @asymptotic.qv_zero(),
      @asymptotic.qv_one(),
      @asymptotic.qv_int(2),
      @asymptotic.qv_int(3),
      @asymptotic.qv_int(4),
    ],
    [
      @asymptotic.qv_one(),
      @asymptotic.qv_int(2),
      @asymptotic.qv_int(3),
      @asymptotic.qv_int(4),
    ],
  )
  let p_op = uop_dual_momentum_tridiag(
    [
      @asymptotic.qv_one(),
      @asymptotic.qv_int(2),
      @asymptotic.qv_int(3),
      @asymptotic.qv_int(4),
    ],
    d,
  )
  @asymptotic.chk(
    out,
    "自伴性：粒子數算子 N、位置算子 Q_J 與對偶動量算子 P_J 在 𝒟_5 上皆滿足 A† = A",
    uop_is_self_adjoint(n_op) &&
    uop_is_self_adjoint(q_op) &&
    uop_is_self_adjoint(p_op),
  )
  // 伴隨反自同構：(A B)† = B† A†
  let ab_adj = uop_adjoint(uop_mul(q_op, p_op))
  let ba_adj = uop_mul(uop_adjoint(p_op), uop_adjoint(q_op))
  @asymptotic.chk(
    out,
    "*-代數反自同構：(Q_J · P_J)† = P_J† · Q_J†，且成長階 deg(Q_J·P_J) = \{ab_adj.growth_deg} = 1 + 1",
    uop_eq(ab_adj, ba_adj) && ab_adj.growth_deg == 2,
  )
  // Lie 交換子 Jacobi 恆等式：[[N, Q], P] + [[Q, P], N] + [[P, N], Q] = 0
  let j1 = uop_commutator(uop_commutator(n_op, q_op), p_op)
  let j2 = uop_commutator(uop_commutator(q_op, p_op), n_op)
  let j3 = uop_commutator(uop_commutator(p_op, n_op), q_op)
  let j_sum = uop_add(j1, uop_add(j2, j3))
  let zero_op = uop_zero(d)
  @asymptotic.chk(
    out,
    "無界算子 Lie 括號 Jacobi 恆等式：[[N, Q_J], P_J] + 循環 = 0（5×5 精確零算子）",
    uop_eq(j_sum, zero_op),
  )
  // 負控制：無界非交換對 [Q_J, P_J] ≠ 0，且 i · [Q_J, P_J] 為嚴格自伴算子（量子力學 Dirac 對易對應！）
  let comm_qp = uop_commutator(q_op, p_op)
  let i_comm = uop_scale(qc_i(), comm_qp)
  @asymptotic.chk(
    out,
    "Dirac 自伴對易子與負控制：[Q_J, P_J] ≠ 0，且 i·[Q_J, P_J] 嚴格自伴",
    !uop_eq(comm_qp, zero_op) && uop_is_self_adjoint(i_comm),
  )
  out
}

///|
pub fn law_quantum_prob_states() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let d = 4
  let gibbs_opt = qstate_diagonal_gibbs([
    @asymptotic.qv_int(8),
    @asymptotic.qv_int(4),
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(1),
  ])
  let pure_opt = qstate_pure([
    qc_make(@asymptotic.qv_one(), @asymptotic.qv_zero()),
    qc_make(@asymptotic.qv_zero(), @asymptotic.qv_int(2)),
    qc_make(@asymptotic.qv_int(-1), @asymptotic.qv_one()),
    qc_zero(),
  ])
  let ok_states = match (gibbs_opt, pure_opt) {
    (Some(gibbs), Some(pure)) => {
      let id = uop_identity(d)
      let norm_ok = qstate_expect(gibbs, id) == qc_one() &&
        qstate_expect(pure, id) == qc_one()
      // 測試算子組：驗證正定性 φ(X† X) ≥ 0 與 GNS Cauchy–Schwarz |φ(X† Y)|² ≤ φ(X†X)φ(Y†Y)
      let n_op = uop_number_op(d)
      let n2 = uop_mul(n_op, n_op)
      let shift = uop_jacobi_tridiag(
        [
          @asymptotic.qv_one(),
          @asymptotic.qv_zero(),
          @asymptotic.qv_int(-1),
          @asymptotic.qv_int(2),
        ],
        [@asymptotic.qv_one(), @asymptotic.qv_int(2), @asymptotic.qv_one()],
      )
      let ops = [id, n_op, n2, shift, uop_mul(n_op, shift)]
      let mut pos_cs_ok = true
      for st in [gibbs, pure] {
        for x in ops {
          let xx = qstate_expect(st, uop_mul(uop_adjoint(x), x))
          if !@asymptotic.qv_is_zero(xx.im) ||
            @asymptotic.qv_lt(xx.re, @asymptotic.qv_zero()) {
            pos_cs_ok = false
          }
          for y in ops {
            let yy = qstate_expect(st, uop_mul(uop_adjoint(y), y))
            let xy = qstate_expect(st, uop_mul(uop_adjoint(x), y))
            if !@asymptotic.qv_le(
                qc_norm_sq(xy),
                @asymptotic.qv_mul(xx.re, yy.re),
              ) {
              pos_cs_ok = false
            }
          }
        }
      }
      norm_ok && pos_cs_ok
    }
    _ => false
  }
  @asymptotic.chk(
    out, "正規化與 GNS Cauchy–Schwarz 定理：Gibbs 態與純態在 2×5² = 50 對無界算子上全滿足 φ(1)=1、φ(X†X)≥0 及 |φ(X†Y)|² ≤ φ(X†X)φ(Y†Y)",
    ok_states,
  )
  // 負控制：含負權重的偽概率分佈與全零態向量被構造器精確拒絕
  let bad_gibbs = qstate_diagonal_gibbs([
    @asymptotic.qv_one(),
    @asymptotic.qv_int(-1),
  ])
  let bad_pure = qstate_pure([qc_zero(), qc_zero()])
  @asymptotic.chk(
    out,
    "負控制：含負權重的非正泛函與零範數態向量均被概率態構造器攔截（回傳 None）",
    bad_gibbs is None && bad_pure is None,
  )
  out
}

///|
pub fn law_uncertainty_principle() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let d = 4
  let sub = [@asymptotic.qv_one(), @asymptotic.qv_int(2), @asymptotic.qv_int(3)]
  let q_op = uop_jacobi_tridiag(
    [
      @asymptotic.qv_zero(),
      @asymptotic.qv_zero(),
      @asymptotic.qv_zero(),
      @asymptotic.qv_zero(),
    ],
    sub,
  )
  let p_op = uop_dual_momentum_tridiag(sub, d)
  // 1. 真空態 |0⟩ = [1, 0, 0, 0]：測試最小不確定性飽和！
  //    Q|0⟩ = |1⟩，P|0⟩ = i|1⟩，故 Var(Q) = 1，Var(P) = 1，[Q,P]|0⟩ = 2i|0⟩ ⇒ (1/4)|2i|² = 1 = LHS（精確飽和！）
  let vac_opt = qstate_pure([qc_one(), qc_zero(), qc_zero(), qc_zero()])
  let sat_ok = match vac_opt {
    None => false
    Some(vac) => {
      let ub = check_robertson_schrodinger(vac, q_op, p_op)
      ub.holds &&
      @asymptotic.qv_eq(ub.lhs_prod, @asymptotic.qv_one()) &&
      @asymptotic.qv_eq(ub.commutator_term, @asymptotic.qv_one()) &&
      @asymptotic.qv_eq(ub.lhs_prod, ub.rhs_total)
    }
  }
  @asymptotic.chk(
    out, "真空最小不確定性飽和定理：基態 |0⟩ 上 Var(Q)Var(P) = 1 = (1/4)|⟨[Q,P]⟩|²（等號精確成立）",
    sat_ok,
  )
  // 2. 一般糾纏／疊加純態與熱混合態上的嚴格 Schrödinger 不確定性界
  let sup_opt = qstate_pure([
    qc_one(),
    qc_make(@asymptotic.qv_one(), @asymptotic.qv_one()),
    qc_real(@asymptotic.qv_frac(1, 2)),
    qc_zero(),
  ])
  let mix_opt = qstate_diagonal_gibbs([
    @asymptotic.qv_int(9),
    @asymptotic.qv_int(3),
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
  ])
  let gen_ok = match (sup_opt, mix_opt) {
    (Some(sup), Some(mix)) => {
      let n_op = uop_number_op(d)
      let b1 = check_robertson_schrodinger(sup, q_op, p_op)
      let b2 = check_robertson_schrodinger(sup, n_op, q_op)
      let b3 = check_robertson_schrodinger(mix, q_op, p_op)
      b1.holds &&
      b2.holds &&
      b3.holds &&
      @asymptotic.qv_lt(@asymptotic.qv_zero(), b2.covariance_term)
    }
    _ => false
  }
  @asymptotic.chk(
    out, "Robertson–Schrödinger 不確定性不等式：疊加態與 Gibbs 混合態全數滿足 Var(A)Var(B) ≥ 交換子界 + 協方差界（含非零協方差項）",
    gen_ok,
  )
  out
}

///|
pub fn law_yosida_and_moment_reconstruction() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  // 1. Yosida 有界預解逼近 + Richardson 外推重現無界期望值！
  //    考慮無界算子 N = diag(0, 1, 2, 3, 4)，對 γ > 0，A_γ = γ N (γ + N)⁻¹ 有漸近展開
  //    ⟨A_γ⟩ = ⟨N⟩ - γ⁻¹ ⟨N²⟩ + γ⁻² ⟨N³⟩ - ...（令 ε = γ⁻¹ → 0⁺！）
  let spec = [
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(3),
    @asymptotic.qv_int(4),
  ]
  let st_opt = qstate_diagonal_gibbs([
    @asymptotic.qv_int(5),
    @asymptotic.qv_int(4),
    @asymptotic.qv_int(3),
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(1),
  ])
  let yosida_ok = match st_opt {
    None => false
    Some(st) => {
      let exact_n = qstate_expect(st, uop_number_op(5)).re
      let gammas = [10, 20, 40]
      let exps : Array[@asymptotic.QVal] = []
      let mut bounded_ok = true
      for g in gammas {
        let gq = @asymptotic.qv_int(g)
        match yosida_diagonal_approximant(spec, gq) {
          None => bounded_ok = false
          Some(ag) => {
            if ag.growth_deg != 0 {
              bounded_ok = false
            }
            for i in 0..<5 {
              let eig = ag.entries[i * 5 + i].re
              if !@asymptotic.qv_lt(eig, gq) {
                bounded_ok = false
              }
            }
            exps.push(qstate_expect(st, ag).re)
          }
        }
      }
      // 單調遞增逼近無界真值：exps[0] < exps[1] < exps[2] < exact_n
      let mono = @asymptotic.qv_lt(exps[0], exps[1]) &&
        @asymptotic.qv_lt(exps[1], exps[2]) &&
        @asymptotic.qv_lt(exps[2], exact_n)
      bounded_ok && mono
    }
  }
  @asymptotic.chk(
    out, "Yosida 有界預解正則化定理：‖A_γ‖ < γ（growth_deg = 0），且 γ = 10,20,40 時 φ(A_γ) 嚴格單調上升逼近無界期望值 φ(N)",
    yosida_ok,
  )
  // 2. Favard–Lanczos 矩重構定理：
  //    標準高斯測度 N(0, 1)（無界支撐 ℝ！）的前 8 階矩為雙階乘：
  //    m_0=1, m_1=0, m_2=1, m_3=0, m_4=3, m_5=0, m_6=15, m_7=0
  //    Hermite 正交多項式的 Jacobi 係數必須精確重構出 α = [0,0,0,0]、β = [1, 2, 3]（玻色創生湮滅權重）！
  let gauss_moments = [
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_int(3),
    @asymptotic.qv_zero(),
    @asymptotic.qv_int(15),
    @asymptotic.qv_zero(),
  ]
  let gauss_ok = match reconstruct_jacobi_from_moments(gauss_moments, 4) {
    None => false
    Some(rec) =>
      @asymptotic.qv_vec_eq(rec.alphas, [
        @asymptotic.qv_zero(),
        @asymptotic.qv_zero(),
        @asymptotic.qv_zero(),
        @asymptotic.qv_zero(),
      ]) &&
      @asymptotic.qv_vec_eq(rec.betas, [
        @asymptotic.qv_one(),
        @asymptotic.qv_int(2),
        @asymptotic.qv_int(3),
      ])
  }
  @asymptotic.chk(
    out, "Favard–Hermite 矩重構定理：由無界高斯矩 [1,0,1,0,3,0,15,0] 反演出 Jacobi 係數 α=[0,0,0,0], β=[1,2,3]（自然湧現 Fock 粒子數梯度！）",
    gauss_ok,
  )
  // Poisson(λ = 1) 查理耶（Charlier）矩 [1, 1, 2, 5, 15, 52]（Bell 數！）
  // 其 Jacobi 係數為 α_k = k + 1 = [1, 2, 3], β_k = k = [1, 2]！
  let bell_moments = [
    @asymptotic.qv_one(),
    @asymptotic.qv_one(),
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(5),
    @asymptotic.qv_int(15),
    @asymptotic.qv_int(52),
  ]
  let charlier_ok = match reconstruct_jacobi_from_moments(bell_moments, 3) {
    None => false
    Some(rec) =>
      @asymptotic.qv_vec_eq(rec.alphas, [
        @asymptotic.qv_one(),
        @asymptotic.qv_int(2),
        @asymptotic.qv_int(3),
      ]) &&
      @asymptotic.qv_vec_eq(rec.betas, [
        @asymptotic.qv_one(),
        @asymptotic.qv_int(2),
      ])
  }
  @asymptotic.chk(
    out, "Poisson–Charlier 矩重構定理：由 Bell 矩序列 [1,1,2,5,15,52] 精確重構 α=[1,2,3], β=[1,2]",
    charlier_ok,
  )
  // 負控制：違反 Hamburger 正定性（m_2 = -1 < m_1² = 0）的偽矩序列被重構器拒絕
  let non_pos_moments = [
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_int(-1),
    @asymptotic.qv_zero(),
  ]
  @asymptotic.chk(
    out,
    "負控制：違反 Hankel 正定性的偽矩序列 [1, 0, −1, 0] 被 reconstruct_jacobi_from_moments 攔截",
    reconstruct_jacobi_from_moments(non_pos_moments, 2) is None,
  )
  out
}

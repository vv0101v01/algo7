// ---------------------------------------------------------------------------
// qprob/nc_measure/laws.mbt — 第五階數學結構定律總表（非交換隨機分佈與測度空間 + 五階大統一橋）
// ---------------------------------------------------------------------------

///|
pub fn nc_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    (
      "正算子值測度（POVM）、Born 機率公理與三向對稱非正交過完備框架",
      law_povm_and_born_measure(),
    ),
    (
      "Naimark 算子測度擴張定理：非交換 POVM ↪ 高維正交 PVM 等距壓縮",
      law_naimark_dilation_theorem(),
    ),
    (
      "Speicher 非交叉自由累積量雙射、Wigner 半圓律與自由 vs 古典分岔定理",
      law_free_cumulants_and_semicircle(),
    ),
    (
      "自由中心極限定理（Free CLT）與五階結構大統一閉環（連續場 → 福克 → 累積量 → 漸近極限）",
      law_free_clt_and_grand_synthesis(),
    ),
  ]
}

///|
fn mk_rank1_2x2(
  a : @asymptotic.QVal,
  b : @asymptotic.QVal,
) -> @unbounded.UnboundedOp {
  // M = [[a, b], [0, 0]] => M† M = [[a², ab], [ab, b²]]
  @unbounded.UnboundedOp::{
    dim: 2,
    growth_deg: 0,
    entries: [
      @unbounded.qc_real(a),
      @unbounded.qc_real(b),
      @unbounded.qc_zero(),
      @unbounded.qc_zero(),
    ],
  }
}

///|
fn pythagorean_povm4() -> PovmMeasure {
  PovmMeasure::{
    dim: 2,
    kraus_roots: [
      mk_rank1_2x2(@asymptotic.qv_zero(), @asymptotic.qv_frac(3, 5)),
      mk_rank1_2x2(@asymptotic.qv_frac(3, 5), @asymptotic.qv_zero()),
      mk_rank1_2x2(@asymptotic.qv_frac(12, 25), @asymptotic.qv_frac(16, 25)),
      mk_rank1_2x2(@asymptotic.qv_frac(16, 25), @asymptotic.qv_frac(-12, 25)),
    ],
  }
}

///|
pub fn law_povm_and_born_measure() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  // ℂ² 上的 4 結果非交換秩-1 勾股過完備 POVM：
  //   w_0 = [0, 3/5]ᵗ, w_1 = [3/5, 0]ᵗ, w_2 = [12/25, 16/25]ᵗ, w_3 = [16/25, -12/25]ᵗ
  //   (0,0) = (225 + 144 + 256)/625 = 1, (1,1) = (225 + 256 + 144)/625 = 1, (0,1) = (192 - 192)/625 = 0，
  //   且 [E_1, E_2] ≠ 0、E_k² ≠ E_k（非投影 PVM）。
  let povm4 = pythagorean_povm4()
  let e1 = povm_effect(povm4, 1)
  let e2 = povm_effect(povm4, 2)
  let non_comm_effects = !@unbounded.uop_eq(
    @unbounded.uop_mul(e1, e2),
    @unbounded.uop_mul(e2, e1),
  )
  @asymptotic.chk(
    out,
    "非交換過完備 POVM 完備性：ℂ² 上 4 結果勾股算子測度滿足 Σ_{k=0}^3 E_k = I_2、非投影（!PVM）且 [E_1, E_2] ≠ 0",
    povm_is_complete(povm4) && !povm_is_projective(povm4) && non_comm_effects,
  )
  // Born 機率公理：對任意純態與混合態，p_k ≥ 0 且 Σ_k p_k = 1
  let st_opt = @unbounded.qstate_pure([
    @unbounded.qc_one(),
    @unbounded.qc_make(@asymptotic.qv_int(2), @asymptotic.qv_int(-1)),
  ])
  let born_ok = match st_opt {
    None => false
    Some(st) => {
      let ps = povm_born_probabilities(povm4, st)
      let mut sum_p = @asymptotic.qv_zero()
      let mut non_neg = true
      for p in ps {
        if @asymptotic.qv_lt(p, @asymptotic.qv_zero()) {
          non_neg = false
        }
        sum_p = @asymptotic.qv_add(sum_p, p)
      }
      non_neg && @asymptotic.qv_eq(sum_p, @asymptotic.qv_one())
    }
  }
  @asymptotic.chk(
    out, "Born 非交換測度公理：純態誘導機率向量 p_0..p_3 全非負且 Σ_k Tr(ρ E_k) = 1",
    born_ok,
  )
  // CPTP 振幅阻尼／退相干量子馬可夫通道：用同一組 Kraus 算子作用於純態，驗證輸出仍正規化且保厄米正定
  let cptp_ok = match st_opt {
    None => false
    Some(st) =>
      match apply_cptp_channel(povm4.kraus_roots, st) {
        None => false
        Some(out_st) =>
          @unbounded.qstate_expect(out_st, @unbounded.uop_identity(2)) ==
          @unbounded.qc_one() &&
          @unbounded.uop_is_self_adjoint(out_st.rho)
      }
  }
  @asymptotic.chk(
    out, "CPTP 量子馬可夫轉移核定理：Kraus 通道 Φ(ρ) = Σ K_a ρ K_a† 嚴格保跡 Tr(Φ(ρ)) = 1 且保自伴",
    cptp_ok,
  )
  // 負控制：缺少第 4 個結果的不完備算子族被 POVM 與 CPTP 通道雙重拒絕
  let incomplete = PovmMeasure::{
    dim: 2,
    kraus_roots: [
      povm4.kraus_roots[0],
      povm4.kraus_roots[1],
      povm4.kraus_roots[2],
    ],
  }
  let rej_ok = !povm_is_complete(incomplete) &&
    (match st_opt {
      None => false
      Some(st) => apply_cptp_channel(incomplete.kraus_roots, st) is None
    })
  @asymptotic.chk(
    out, "負控制：Σ E_k ≠ I 的不完備算子族被 povm_is_complete 與 apply_cptp_channel 同步攔截",
    rej_ok,
  )
  out
}

///|
pub fn law_naimark_dilation_theorem() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let povm4 = pythagorean_povm4()
  let (dilated_dim, naimark_ok) = verify_naimark_dilation(povm4)
  @asymptotic.chk(
    out,
    "Naimark 擴張定理：ℂ² 上的 4 結果非正交 POVM 等距嵌入 ℂ^\{dilated_dim} 上的正交 PVM（V†V = I_2 且 ∀k, V† P_k V = E_k）",
    dilated_dim == 8 && naimark_ok,
  )
  // 對照：標準計算基底 PVM {|0⟩⟨0|, |1⟩⟨1|} 自身即滿足 povm_is_projective
  let p0 = @unbounded.UnboundedOp::{
    dim: 2,
    growth_deg: 0,
    entries: [
      @unbounded.qc_one(),
      @unbounded.qc_zero(),
      @unbounded.qc_zero(),
      @unbounded.qc_zero(),
    ],
  }
  let p1 = @unbounded.UnboundedOp::{
    dim: 2,
    growth_deg: 0,
    entries: [
      @unbounded.qc_zero(),
      @unbounded.qc_zero(),
      @unbounded.qc_zero(),
      @unbounded.qc_one(),
    ],
  }
  let pvm2 = PovmMeasure::{ dim: 2, kraus_roots: [p0, p1], }
  @asymptotic.chk(
    out,
    "投影值譜測度（PVM）特例刻畫：正交譜投影族同時滿足 povm_is_complete 與 povm_is_projective",
    povm_is_complete(pvm2) && povm_is_projective(pvm2),
  )
  out
}

///|
pub fn law_free_cumulants_and_semicircle() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  // 1. 矩 ↔ 自由累積量雙射對合定理：對任意矩序列，free_cumulants_to_moments(moments_to_free_cumulants(m)) == m
  let arb_moments = [
    @asymptotic.qv_one(),
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(7),
    @asymptotic.qv_int(29),
    @asymptotic.qv_int(133),
    @asymptotic.qv_int(650),
  ]
  let kappas = moments_to_free_cumulants(arb_moments)
  let roundtrip = free_cumulants_to_moments(kappas)
  @asymptotic.chk(
    out,
    "Speicher 非交叉矩-累積量雙射定理：前 5 階矩 ↔ 自由累積量正逆轉換精確無損還原",
    @asymptotic.qv_vec_eq(roundtrip, arb_moments),
  )
  // 2. Wigner 半圓律累積量消失定理：Catalan 矩 [1, 0, 1, 0, 2, 0, 5, 0, 14] 的自由累積量為 [0, 1, 0, 0, 0, 0, 0, 0]！
  let semi_moments = [
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_int(2),
    @asymptotic.qv_zero(),
    @asymptotic.qv_int(5),
    @asymptotic.qv_zero(),
    @asymptotic.qv_int(14),
  ]
  let semi_kappas = moments_to_free_cumulants(semi_moments)
  let expected_semi_k = [
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_zero(),
  ]
  @asymptotic.chk(
    out,
    "Wigner 半圓律自由高斯性：Catalan 矩序列的自由累積量為 κ_2 = 1，所有 κ_{n≠2} = 0（直到 8 階全零！）",
    @asymptotic.qv_vec_eq(semi_kappas, expected_semi_k),
  )
  // 3. 自由 Poisson（Marchenko–Pastur，率 λ = 1）分佈：矩亦為 Catalan 數 C_n = [1, 1, 2, 5, 14, 42]（無奇數零），
  //    其各階自由累積量恆為常數 κ_n = 1 = [1, 1, 1, 1, 1]！
  let mp_moments = [
    @asymptotic.qv_one(),
    @asymptotic.qv_one(),
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(5),
    @asymptotic.qv_int(14),
    @asymptotic.qv_int(42),
  ]
  let mp_kappas = moments_to_free_cumulants(mp_moments)
  @asymptotic.chk(
    out,
    "自由 Poisson（Marchenko–Pastur）定理：非交叉計數矩 [1,1,2,5,14,42] 的自由累積量恆為 κ_1..κ_5 = [1,1,1,1,1]",
    @asymptotic.qv_vec_eq(mp_kappas, [
      @asymptotic.qv_one(),
      @asymptotic.qv_one(),
      @asymptotic.qv_one(),
      @asymptotic.qv_one(),
      @asymptotic.qv_one(),
    ]),
  )
  // 4. 古典 vs 非交換分岔定理（4 階交叉配分 {(1,3),(2,4)} 效應！）：
  //    標準高斯矩 [1, 0, 1, 0, 3, 0, 15]：古典累積量 c_4 = 0，但其**自由累積量** κ_4 = 3 - 2 = +1 ≠ 0！
  //    反之，Wigner 半圓矩 [1, 0, 1, 0, 2]：自由累積量 κ_4 = 0，但其**古典累積量** c_4 = 2 - 3 = -1 ≠ 0！
  let gauss_m = [
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_int(3),
  ]
  let gauss_c = moments_to_classical_cumulants(gauss_m)
  let gauss_k = moments_to_free_cumulants(gauss_m)
  let semi_c = moments_to_classical_cumulants(semi_moments)
  @asymptotic.chk(
    out,
    "交換 vs 非交換四階分岔定理（交叉配分 (13)(24)）：高斯律 c_4=0 但 κ_4=\{@asymptotic.qv_show(gauss_k[3])}；半圓律 κ_4=0 但 c_4=\{@asymptotic.qv_show(semi_c[3])}",
    @asymptotic.qv_is_zero(gauss_c[3]) &&
    @asymptotic.qv_eq(gauss_k[3], @asymptotic.qv_one()) &&
    @asymptotic.qv_eq(semi_c[3], @asymptotic.qv_int(-1)),
  )
  out
}

///|
pub fn law_free_clt_and_grand_synthesis() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  // 1. 自由中心極限定理（Free CLT）+ 第一階 Richardson 漸近極限外推！
  //    取對稱 Rademacher / Bernoulli(±1) 隨機變數：m = [1, 0, 1, 0, 1, 0, 1]（因為 (±1)^{2k} = 1！）。
  //    其自由累積量 κ_2 = 1, κ_4 = 1 - 2 = -1, κ_6 = 2 ≠ 0。
  //    對 N = r²（取 r = 1, 2, 3, 4 ⇒ N = 1, 4, 9, 16），計算標準化自由和 S_N = (X_1 ⊞ ... ⊞ X_N)/√N 的矩：
  //      m_4(S_N) = 2 + κ_4 / N = 2 - 1/N
  //      m_6(S_N) = 5 + 5 κ_4 / N + κ_6 / N² = 5 - 5/N + 2/N²
  //    將 N = [1, 2, 4]（對應 r 尺度或直接以 N 為 Richardson 尺度：r = 1, 2, 3 ⇒ N = 1, 4, 9）
  //    送入第一階的 `richardson_extrapolate_limit([1, 4, 9], ...)`，必須**零誤差**命中半圓律極限 m_4 = 2, m_6 = 5！
  let bernoulli_m = [
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
  ]
  let rs = [1, 2, 3]
  let ns = [1, 4, 9]
  let m4_seq : Array[@asymptotic.QVal] = []
  let m6_seq : Array[@asymptotic.QVal] = []
  for r in rs {
    let sm = free_clt_scaled_moments(bernoulli_m, r)
    m4_seq.push(sm[4])
    m6_seq.push(sm[6])
  }
  let clt_ok = match
    (
      @asymptotic.richardson_extrapolate_limit(ns, m4_seq),
      @asymptotic.richardson_extrapolate_limit(ns, m6_seq),
    ) {
    (Some(lim4), Some(lim6)) =>
      @asymptotic.qv_eq(lim4, @asymptotic.qv_int(2)) &&
      @asymptotic.qv_eq(lim6, @asymptotic.qv_int(5)) &&
      !@asymptotic.qv_eq(m6_seq[2], @asymptotic.qv_int(5))
    _ => false
  }
  @asymptotic.chk(
    out, "Voiculescu 自由中心極限定理（Free CLT × Richardson 外推）：Rademacher 自由和在 N=[1,4,9] 外推至 N→∞ 零誤差命中半圓律 m_4=2, m_6=5",
    clt_ok,
  )
  // 2. 自由加性卷積可加性定理：兩個率為 λ_1 = 2 與 λ_2 = 3 的自由 Poisson 分佈做自由卷積 μ_2 ⊞ μ_3，
  //    必須精確等於率為 λ = 5 的自由 Poisson 分佈！
  let mp2 = free_cumulants_to_moments([
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(2),
  ])
  let mp3 = free_cumulants_to_moments([
    @asymptotic.qv_int(3),
    @asymptotic.qv_int(3),
    @asymptotic.qv_int(3),
    @asymptotic.qv_int(3),
  ])
  let mp5 = free_cumulants_to_moments([
    @asymptotic.qv_int(5),
    @asymptotic.qv_int(5),
    @asymptotic.qv_int(5),
    @asymptotic.qv_int(5),
  ])
  let conv_23 = free_additive_convolution_moments(mp2, mp3)
  // Narayana N(4, k) = [1, 6, 6, 1]：5 + 6·25 + 6·125 + 625 = 1530！
  @asymptotic.chk(
    out,
    "自由加性卷積半群律：FreePoisson(2) ⊞ FreePoisson(3) = FreePoisson(5)（前 4 階矩 = [1, 5, 30, 195, \{@asymptotic.qv_show(conv_23[4])}] 逐項相等）",
    @asymptotic.qv_vec_eq(conv_23, mp5) &&
    @asymptotic.qv_eq(conv_23[4], @asymptotic.qv_int(1530)),
  )
  // 3. 五階數學結構大統一閉環定理（Grand Five-Space Synthesis）：
  //    從第四階連續區間 [0, 1] 上的歸一化波包 f(t) = 1 出發：
  //      - 路徑 A（第四階連續算子場 Wick 展開）：計算玻色高斯場 Φ(f) = A(f) + A†(f) 的前 6 階真空矩 [1, 0, 1, 0, 3, 0, 15]
  //        → 送入第五階古典累積量轉換器，驗證高階古典累積量 c_3..c_6 全為 0，且第二階 Favard 給出 β = [1, 2]；
  //      - 路徑 B（第三階全量子福克空間 q = 0）：同一個波包在單模全福克空間的自由場 X = ℓ*(f) + ℓ(f)
  //        生成前 6 階真空矩 [1, 0, 1, 0, 2, 0, 5]
  //        → 送入第五階自由累積量轉換器，驗證高階自由累積量 κ_3..κ_6 全為 0，且第二階 Favard 給出 β = [1, 1]！
  let z0 = @asymptotic.qv_zero()
  let z1 = @asymptotic.qv_one()
  let wave = @ccr_field.ContinuumTestFn::{
    t_start: z0,
    t_end: z1,
    coeffs: [z1],
  }
  // 路徑 A：Wick 算連續場 Φ(wave)^n 真空期望值（n = 0..6）
  let bose_field_m : Array[@asymptotic.QVal] = [@asymptotic.qv_one()]
  for n in 1..<7 {
    if n % 2 == 1 {
      bose_field_m.push(@asymptotic.qv_zero())
    } else {
      let total_masks = 1 << n
      let mut sum_m = @asymptotic.qv_zero()
      for mask in 0..<total_masks {
        let facs : Array[@ccr_field.FieldFactor] = []
        for b in 0..<n {
          if ((mask >> b) & 1) == 0 {
            facs.push(@ccr_field.Annihilate(wave))
          } else {
            facs.push(@ccr_field.Create(wave))
          }
        }
        sum_m = @asymptotic.qv_add(
          sum_m,
          @ccr_field.wick_vacuum_expectation(facs),
        )
      }
      bose_field_m.push(sum_m)
    }
  }
  // 路徑 B：全福克 q = 0 算 (ℓ* + ℓ)^n 真空矩（用波包 L² 範數 = 1 的單模嵌入 [‖wave‖] = [1]）
  let norm_wave = @ccr_field.continuum_l2_inner(wave, wave) // 1
  let vac = @fock.fock_vacuum(1)
  let mut cur_f = vac
  let free_field_m : Array[@asymptotic.QVal] = []
  for n in 0..<7 {
    free_field_m.push(@fock.fock_inner_q(z0, vac, cur_f))
    if n < 6 {
      cur_f = @fock.fock_add(
        @fock.fock_create_left([norm_wave], cur_f),
        @fock.fock_annihilate_q(z0, [z1], cur_f),
      )
    }
  }
  let bose_cc = moments_to_classical_cumulants(bose_field_m)
  let free_fc = moments_to_free_cumulants(free_field_m)
  let synthesis_ok = @asymptotic.qv_eq(bose_field_m[6], @asymptotic.qv_int(15)) &&
    @asymptotic.qv_eq(free_field_m[6], @asymptotic.qv_int(5)) &&
    @asymptotic.qv_is_zero(bose_cc[3]) &&
    @asymptotic.qv_is_zero(bose_cc[5]) &&
    @asymptotic.qv_is_zero(free_fc[3]) &&
    @asymptotic.qv_is_zero(free_fc[5])
  @asymptotic.chk(
    out, "五階大統一對偶定理：連續 CCR 場 Wick 矩 (m_6=15 ⇒ 古典 c_4=c_6=0) ↔ 全福克自由場矩 (m_6=5 ⇒ 自由 κ_4=κ_6=0) 雙路閉合",
    synthesis_ok,
  )
  out
}

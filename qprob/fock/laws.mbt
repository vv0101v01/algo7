// ---------------------------------------------------------------------------
// qprob/fock/laws.mbt — 第三階數學結構定律總表（全量子福克空間與 q-變形子空間）
// ---------------------------------------------------------------------------

///|
pub fn fock_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    (
      "全量子福克空間 ℱ_0(ℋ)：Cuntz–Toeplitz 等距恆等式與半圓律矩定理",
      law_full_fock_cuntz_toeplitz(),
    ),
    (
      "q-對易關係 [ℓ_q(g), ℓ*_q(f)]_q = ⟨g,f⟩ I 與 Bożejko–Speicher 伴隨性",
      law_q_commutation_and_adjoint(),
    ),
    (
      "三統計統一分裂定理：q = 0（Boltzmann d^n）、q = +1（玻色）、q = −1（費米 Pauli 核）",
      law_three_statistics_splitting(),
    ),
    (
      "二次量子化函子 Γ(A·B) = Γ(A)Γ(B) 與微分 Lie 同態 [dΓ(X), dΓ(Y)] = dΓ([X,Y])",
      law_second_quantization_functors(),
    ),
  ]
}

///|
pub fn law_full_fock_cuntz_toeplitz() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let d = 2
  let e0 = [@asymptotic.qv_one(), @asymptotic.qv_zero()]
  let e1 = [@asymptotic.qv_zero(), @asymptotic.qv_one()]
  let q0 = @asymptotic.qv_zero()
  let vac = fock_vacuum(d)
  let probes = [
    vac,
    fock_create_left(e0, vac),
    fock_create_left(e1, fock_create_left(e0, vac)),
    fock_add(
      fock_create_left(e0, fock_create_left(e0, vac)),
      fock_scale(@asymptotic.qv_int(-2), fock_create_left(e1, vac)),
    ),
  ]
  // Cuntz–Toeplitz 關係：ℓ_i ℓ*_j = δ_{ij} I（對 i, j ∈ {0, 1}）
  let mut ct_ok = true
  for psi in probes {
    if !fock_eq(fock_annihilate_q(q0, e0, fock_create_left(e0, psi)), psi) {
      ct_ok = false
    }
    if !fock_eq(fock_annihilate_q(q0, e1, fock_create_left(e1, psi)), psi) {
      ct_ok = false
    }
    if !fock_eq(
        fock_annihilate_q(q0, e0, fock_create_left(e1, psi)),
        fock_zero(d),
      ) {
      ct_ok = false
    }
    if !fock_eq(
        fock_annihilate_q(q0, e1, fock_create_left(e0, psi)),
        fock_zero(d),
      ) {
      ct_ok = false
    }
  }
  @asymptotic.chk(
    out,
    "Cuntz–Toeplitz 等距代數：ℓ_i ℓ*_j = δ_{ij} I 在 \{probes.length()} 個多粒子全福克態上精確成立",
    ct_ok,
  )
  // 投影恆等式：I - Σ_{i=0}^{d-1} ℓ*_i ℓ_i = |Ω⟩⟨Ω|（在真空上為 |Ω⟩，在所有 n ≥ 1 詞上精確為 0！）
  let mut vac_proj_ok = true
  for n in 1..<4 {
    for w in fock_sector_words(d, n) {
      let vec_w = FullFockVec::{
        single_dim: d,
        terms: [(w, @asymptotic.qv_one())],
      }
      let p0 = fock_create_left(e0, fock_annihilate_q(q0, e0, vec_w))
      let p1 = fock_create_left(e1, fock_annihilate_q(q0, e1, vec_w))
      let rem = fock_sub(vec_w, fock_add(p0, p1))
      if !fock_eq(rem, fock_zero(d)) {
        vac_proj_ok = false
      }
    }
  }
  let vac_rem = fock_sub(
    vac,
    fock_add(
      fock_create_left(e0, fock_annihilate_q(q0, e0, vac)),
      fock_create_left(e1, fock_annihilate_q(q0, e1, vac)),
    ),
  )
  @asymptotic.chk(
    out,
    "Cuntz–Toeplitz 真空餘投影定理：I − Σ_i ℓ*_i ℓ_i = |Ω⟩⟨Ω|（消滅全部 2+4+8 = 14 個非真空詞並保持 |Ω⟩）",
    vac_proj_ok && fock_eq(vac_rem, vac),
  )
  // Wigner 半圓律湧現定理：在全福克空間 q = 0 上，自伴自由場算子 X = ℓ*(e_0) + ℓ(e_0)
  // 關於真空態 ⟨Ω, X^{2k} Ω⟩_0 精確生成 Catalan 數 C_k = [1, 1, 2, 5, 14]（奇數矩全 0）！
  let step_x = (st : FullFockVec) => {
    fock_add(fock_create_left(e0, st), fock_annihilate_q(q0, e0, st))
  }
  let mut cur = vac
  let moments : Array[@asymptotic.QVal] = []
  for deg in 0..<9 {
    moments.push(fock_inner_q(q0, vac, cur))
    if deg < 8 {
      cur = step_x(cur)
    }
  }
  let expected_catalan = [
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
  // 再將此矩序列送入第二階的 Favard–Lanczos 重構器：必須給出常數 Jacobi 係數 β = [1, 1, 1]！
  let favard_free = match
    @unbounded.reconstruct_jacobi_from_moments(moments, 4) {
    None => false
    Some(rec) =>
      @asymptotic.qv_vec_eq(rec.betas, [
        @asymptotic.qv_one(),
        @asymptotic.qv_one(),
        @asymptotic.qv_one(),
      ])
  }
  @asymptotic.chk(
    out,
    "全福克真空半圓律定理：⟨Ω, (ℓ*+ℓ)^k Ω⟩_0 = [1,0,1,0,2,0,5,0,14]（Catalan 數），且 Favard 重構出自由常數權重 β=[1,1,1]",
    @asymptotic.qv_vec_eq(moments, expected_catalan) && favard_free,
  )
  // 負控制：全福克空間的左創生算子非可交換 ℓ*(e_0)ℓ*(e_1)|Ω⟩ ≠ ℓ*(e_1)ℓ*(e_0)|Ω⟩
  let w01 = fock_create_left(e0, fock_create_left(e1, vac))
  let w10 = fock_create_left(e1, fock_create_left(e0, vac))
  @asymptotic.chk(
    out,
    "負控制：全福克空間保存非交換張量詞序 e_0⊗e_1 ≠ e_1⊗e_0（⟨e_0⊗e_1, e_1⊗e_0⟩_0 = 0）",
    !fock_eq(w01, w10) && @asymptotic.qv_is_zero(fock_inner_q(q0, w01, w10)),
  )
  out
}

///|
pub fn law_q_commutation_and_adjoint() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let d = 2
  let f = [@asymptotic.qv_int(2), @asymptotic.qv_int(-1)]
  let g = [@asymptotic.qv_one(), @asymptotic.qv_int(3)]
  // ⟨g, f⟩ = 1*2 + 3*(-1) = -1
  let gf_inner = @asymptotic.qv_add(
    @asymptotic.qv_mul(g[0], f[0]),
    @asymptotic.qv_mul(g[1], f[1]),
  )
  let qs = [
    @asymptotic.qv_int(-1),
    @asymptotic.qv_frac(-1, 2),
    @asymptotic.qv_zero(),
    @asymptotic.qv_frac(1, 2),
    @asymptotic.qv_one(),
  ]
  let vac = fock_vacuum(d)
  let e0 = [@asymptotic.qv_one(), @asymptotic.qv_zero()]
  let e1 = [@asymptotic.qv_zero(), @asymptotic.qv_one()]
  let states = [
    vac,
    fock_create_left(e0, vac),
    fock_create_left(e1, fock_create_left(e0, vac)),
    fock_create_left(e0, fock_create_left(e1, fock_create_left(e0, vac))),
  ]
  let mut q_rel_ok = true
  let mut adj_ok = true
  for q in qs {
    for st in states {
      // 驗證 ℓ_q(g) ℓ*(f) st - q ℓ*(f) ℓ_q(g) st == ⟨g, f⟩ st
      let lhs1 = fock_annihilate_q(q, g, fock_create_left(f, st))
      let lhs2 = fock_scale(q, fock_create_left(f, fock_annihilate_q(q, g, st)))
      let lhs = fock_sub(lhs1, lhs2)
      let rhs = fock_scale(gf_inner, st)
      if !fock_eq(lhs, rhs) {
        q_rel_ok = false
      }
      // 驗證 Bożejko–Speicher 伴隨恆等式：⟨ℓ*(f) u, v⟩_q == ⟨u, ℓ_q(f) v⟩_q
      for v in states {
        let left_ip = fock_inner_q(q, fock_create_left(f, st), v)
        let right_ip = fock_inner_q(q, st, fock_annihilate_q(q, f, v))
        if !@asymptotic.qv_eq(left_ip, right_ip) {
          adj_ok = false
        }
      }
    }
  }
  @asymptotic.chk(
    out, "普適 q-對易關係：ℓ_q(g)ℓ*(f) − q ℓ*(f)ℓ_q(g) = ⟨g,f⟩ I 在 5 個變形參數 q ∈ {−1,−1/2,0,1/2,1} × 4 扇區全部成立",
    q_rel_ok,
  )
  @asymptotic.chk(
    out, "Bożejko–Speicher 伴隨定理：⟨ℓ*(f) u, v⟩_q = ⟨u, ℓ_q(f) v⟩_q（5 × 16 = 80 對多粒子態精確相等）",
    adj_ok,
  )
  out
}

///|
pub fn law_three_statistics_splitting() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let d = 2
  // 在 d = 2（雙模態量子系統）比較 n = 0, 1, 2, 3 粒子扇區的 Gram 核矩陣秩 = 商希爾伯特空間維度！
  // - 全福克 / q = 1/2：d^n = [1, 2, 4, 8]
  // - 玻色對稱子空間 q = +1：C(2+n-1, n) = n + 1 = [1, 2, 3, 4]
  // - 費米外代數子空間 q = -1：C(2, n) = [1, 2, 1, 0]（n = 3 時 Pauli 不相容使整個 8×8 Gram 矩陣恆為 0！）
  let ranks_free : Array[Int32] = []
  let ranks_half : Array[Int32] = []
  let ranks_bose : Array[Int32] = []
  let ranks_fermi : Array[Int32] = []
  for n in 0..<4 {
    let (m0, g0) = fock_q_gram_matrix(@asymptotic.qv_zero(), d, n)
    ranks_free.push(@asymptotic.qmat_rank(g0, m0, m0))
    let (mh, gh) = fock_q_gram_matrix(@asymptotic.qv_frac(1, 2), d, n)
    ranks_half.push(@asymptotic.qmat_rank(gh, mh, mh))
    let (mb, gb) = fock_q_gram_matrix(@asymptotic.qv_one(), d, n)
    ranks_bose.push(@asymptotic.qmat_rank(gb, mb, mb))
    let (mf, gf) = fock_q_gram_matrix(@asymptotic.qv_int(-1), d, n)
    ranks_fermi.push(@asymptotic.qmat_rank(gf, mf, mf))
  }
  @asymptotic.chk(
    out,
    "全福克與嚴格插值正定性（q = 0, 1/2）：扇區維度 = \{@asymptotic.ints_show(ranks_free)} = \{@asymptotic.ints_show(ranks_half)} = [1, 2, 4, 8]（Bożejko–Speicher 無零空間定理）",
    ranks_free == [1, 2, 4, 8] && ranks_half == [1, 2, 4, 8],
  )
  @asymptotic.chk(
    out,
    "玻色對稱福克商空間（q = +1）：Sym^n(ℚ²) 維度由 Gram 秩實算為 \{@asymptotic.ints_show(ranks_bose)} = [1, 2, 3, 4] = C(n+1, n)",
    ranks_bose == [1, 2, 3, 4],
  )
  @asymptotic.chk(
    out,
    "費米反對稱福克商空間與 Pauli 不相容定理（q = −1）：Λ^n(ℚ²) 秩實算為 \{@asymptotic.ints_show(ranks_fermi)} = [1, 2, 1, 0]（3 粒子扇區維度坍縮為 0！）",
    ranks_fermi == [1, 2, 1, 0],
  )
  // 負控制：|q| > 1（例如 q = 2）破壞 Gram 正定性！在 n = 2 扇區，反對稱態 |01⟩ - |10⟩ 的 2-範數平方 = 2(1 - q) = -2 < 0！
  let vac = fock_vacuum(d)
  let e0 = [@asymptotic.qv_one(), @asymptotic.qv_zero()]
  let e1 = [@asymptotic.qv_zero(), @asymptotic.qv_one()]
  let sing = fock_sub(
    fock_create_left(e0, fock_create_left(e1, vac)),
    fock_create_left(e1, fock_create_left(e0, vac)),
  )
  let bad_norm = fock_inner_q(@asymptotic.qv_int(2), sing, sing)
  @asymptotic.chk(
    out,
    "負控制：超界變形 q = 2 時單重態 ⟨01−10 | 01−10⟩_{q=2} = \{@asymptotic.qv_show(bad_norm)} < 0（驗證 Bożejko–Speicher 界 |q| ≤ 1 不可放寬）",
    @asymptotic.qv_eq(bad_norm, @asymptotic.qv_int(-2)),
  )
  out
}

///|
pub fn law_second_quantization_functors() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let d = 2
  // 單粒子算子 A, B ∈ M_2(ℚ)
  let a_mat = [
    @asymptotic.qv_one(),
    @asymptotic.qv_int(2),
    @asymptotic.qv_zero(),
    @asymptotic.qv_int(-1),
  ]
  let b_mat = [
    @asymptotic.qv_int(2),
    @asymptotic.qv_int(-1),
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
  ]
  let ab_mat = @asymptotic.qmat_mul(a_mat, d, d, b_mat, d)
  let ba_mat = @asymptotic.qmat_mul(b_mat, d, d, a_mat, d)
  let comm_ab = [
    for k in 0..<(d * d) => @asymptotic.qv_sub(ab_mat[k], ba_mat[k])
  ]
  let vac = fock_vacuum(d)
  let e0 = [@asymptotic.qv_one(), @asymptotic.qv_zero()]
  let e1 = [@asymptotic.qv_zero(), @asymptotic.qv_one()]
  let psi = fock_add(
    vac,
    fock_add(
      fock_create_left(e0, fock_create_left(e1, vac)),
      fock_scale(
        @asymptotic.qv_int(-3),
        fock_create_left(e1, fock_create_left(e0, fock_create_left(e1, vac))),
      ),
    ),
  )
  // 1. 函子律 Γ(A·B) = Γ(A) ∘ Γ(B) 與 Γ(I) = I
  let id_mat = [
    @asymptotic.qv_one(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_zero(),
    @asymptotic.qv_one(),
  ]
  let gamma_hom = fock_eq(
      fock_gamma(ab_mat, d, psi),
      fock_gamma(a_mat, d, fock_gamma(b_mat, d, psi)),
    ) &&
    fock_eq(fock_gamma(id_mat, d, psi), psi)
  @asymptotic.chk(
    out, "乘法二次量子化函子定理：Γ(A·B)|Ψ⟩ = Γ(A)(Γ(B)|Ψ⟩) 且 Γ(I)|Ψ⟩ = |Ψ⟩（含 0、2、3 粒子疊加態）",
    gamma_hom,
  )
  // 2. 微分二次量子化 Lie 代數同態定理：[dΓ(A), dΓ(B)] = dΓ([A, B])！
  let lhs = fock_sub(
    fock_dgamma(a_mat, d, fock_dgamma(b_mat, d, psi)),
    fock_dgamma(b_mat, d, fock_dgamma(a_mat, d, psi)),
  )
  let rhs = fock_dgamma(comm_ab, d, psi)
  @asymptotic.chk(
    out,
    "微商二次量子化 Lie 同態定理：[dΓ(A), dΓ(B)]|Ψ⟩ = dΓ([A, B])|Ψ⟩（且 [A,B] ≠ 0 非平凡交換子）",
    fock_eq(lhs, rhs) && !fock_eq(rhs, fock_zero(d)),
  )
  // 3. dΓ(I) 在 n 粒子齊次態上恆等於純量乘法 n · I
  let psi3 = fock_create_left(
    e1,
    fock_create_left(e0, fock_create_left(e1, vac)),
  )
  @asymptotic.chk(
    out,
    "粒子數算子表現：dΓ(I) 在 3 粒子態上精確等於 3·|Ψ_3⟩，在真空 |Ω⟩ 上為 0",
    fock_eq(
      fock_dgamma(id_mat, d, psi3),
      fock_scale(@asymptotic.qv_int(3), psi3),
    ) &&
    fock_eq(fock_dgamma(id_mat, d, vac), fock_zero(d)),
  )
  out
}

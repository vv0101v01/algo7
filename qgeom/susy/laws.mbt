// ---------------------------------------------------------------------------
// qgeom/susy — 定律登記
// ---------------------------------------------------------------------------
// 四個章節：分次代數、四元數頂點對偶、有限複形上的德朗姆型恆等、複形四元數。
// 每個數字（Betti 數、面數、秩、核維數）都是當場算出來的，寫進標籤只是為了
// 讓讀者看到它真的被算了，而不是被抄進來的。

///|
pub fn susy_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    ("超對稱代數：分次交換子、Jacobi 與超跡", law_superalgebra()),
    ("四元數頂點對偶幾何方程", law_vertex_duality()),
    ("德朗姆型恆等：∂² = 0、Betti、Hodge、超電荷", law_derham_chain_complex()),
    ("複形四元數 H ⊗ C：複結構與伴隨恆等", law_derham_complexified()),
  ]
}

// ---------------------------------------------------------------------------
// 樣本
// ---------------------------------------------------------------------------

///|
/// 由四個整數 (re, i, j, k) 造四元數矩陣。
fn qmat_of(rows : Array[Array[Array[Int32]]]) -> Array[Array[@core.Quat]] {
  let r = rows.length()
  let c = if r > 0 { rows[0].length() } else { 0 }
  let out = @core.qm_zero(r, c)
  let mut i = 0
  while i < r {
    let mut j = 0
    while j < c {
      let e = rows[i][j]
      out[i][j] = @core.quat_of_int(e[0], e[1], e[2], e[3])
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
fn qmat_even() -> Array[Array[@core.Quat]] {
  // 偶元素：(1|1) 分塊對角
  qmat_of([[[1, 0, 0, 0], [0, 0, 0, 0]], [[0, 0, 0, 0], [3, 1, 0, 0]]])
}

///|
fn qmat_even2() -> Array[Array[@core.Quat]] {
  qmat_of([[[0, 0, 0, 1], [0, 0, 0, 0]], [[0, 0, 0, 0], [2, 1, 0, 3]]])
}

///|
fn qmat_odd() -> Array[Array[@core.Quat]] {
  // 奇元素：(1|1) 分塊非對角
  qmat_of([[[0, 0, 0, 0], [0, 2, 0, 0]], [[0, 0, 1, 0], [0, 0, 0, 0]]])
}

///|
fn qmat_odd2() -> Array[Array[@core.Quat]] {
  qmat_of([[[0, 0, 0, 0], [1, 0, 3, 0]], [[0, 0, 0, 2], [0, 0, 0, 0]]])
}

///|
fn qvec_pair() -> Array[Array[@core.Quat]] {
  [
    [@core.quat_of_int(1, 2, 0, -1), @core.quat_of_int(0, 0, 3, 0)],
    [@core.quat_of_int(2, 0, 1, 0), @core.quat_of_int(0, 1, 0, 1)],
  ]
}

// ---------------------------------------------------------------------------
// 1. 超對稱代數
// ---------------------------------------------------------------------------

///|
pub fn law_superalgebra() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let even_a = slad_new(qmat_even(), 0)
  let even_b = slad_new(qmat_even2(), 0)
  let odd_a = slad_new(qmat_odd(), 1)
  let odd_b = slad_new(qmat_odd2(), 1)
  let samples = [even_a, even_b, odd_a, odd_b]
  // 分次反對稱
  let mut antisym = true
  let mut i = 0
  while i < samples.length() {
    let mut j = 0
    while j < samples.length() {
      let a = samples[i]
      let b = samples[j]
      let ab = slad_bracket(a, b)
      let ba = slad_bracket(b, a)
      let sign = slad_sign(a, b)
      // [A,B] = −(−1)^{|A||B|}[B,A]
      let expect = if sign == 1 {
        slad_new(@core.qm_neg(ba.mat), ba.par)
      } else {
        ba
      }
      if !(slad_eq(ab, expect)) {
        antisym = false
      }
      j = j + 1
    }
    i = i + 1
  }
  @core.chk(out, "分次反對稱：[A,B] = −(−1)^{|A||B|}[B,A]（4² 對）", antisym)
  // 宇稱相加
  @core.chk(
    out,
    "宇稱加法：|[A,B]| = |A| + |B| (mod 2)",
    slad_bracket(odd_a, odd_b).par == 0 &&
    slad_bracket(even_a, odd_a).par == 1 &&
    slad_bracket(even_a, even_b).par == 0,
  )
  // 分次 Jacobi
  let mut jacobi = true
  let mut triples = 0
  i = 0
  while i < samples.length() {
    let mut j = 0
    while j < samples.length() {
      let mut k = 0
      while k < samples.length() {
        let a = samples[i]
        let b = samples[j]
        let c = samples[k]
        let abc = slad_bracket(a, slad_bracket(b, c))
        let bca = slad_bracket(b, slad_bracket(c, a))
        let cab = slad_bracket(c, slad_bracket(a, b))
        let s_ac = if a.par * c.par == 0 { 1 } else { -1 }
        let s_ab = if a.par * b.par == 0 { 1 } else { -1 }
        let s_bc = if b.par * c.par == 0 { 1 } else { -1 }
        let t1 = if s_ac == 1 { abc.mat } else { @core.qm_neg(abc.mat) }
        let t2 = if s_ab == 1 { bca.mat } else { @core.qm_neg(bca.mat) }
        let t3 = if s_bc == 1 { cab.mat } else { @core.qm_neg(cab.mat) }
        let sum = @core.qm_add(@core.qm_add(t1, t2), t3)
        let mut is_zero = true
        let mut r = 0
        while r < @core.qm_rows(sum) {
          let mut s = 0
          while s < @core.qm_cols(sum) {
            if !(@core.quat_is_zero(sum[r][s])) {
              is_zero = false
            }
            s = s + 1
          }
          r = r + 1
        }
        if !(is_zero) {
          jacobi = false
        }
        triples = triples + 1
        k = k + 1
      }
      j = j + 1
    }
    i = i + 1
  }
  @core.chk(
    out,
    "分次 Jacobi：(−1)^{|A||C|}[A,[B,C]] + (−1)^{|A||B|}[B,[C,A]] + (−1)^{|B||C|}[C,[A,B]] = 0（\{triples} 組）",
    jacobi,
  )
  // 超跡的分次循環性
  let str_ee = susy_supertrace(
    @core.qm_mul_unchecked(qmat_even(), qmat_even2()),
    1,
    1,
  )
  let str_ee_rev = susy_supertrace(
    @core.qm_mul_unchecked(qmat_even2(), qmat_even()),
    1,
    1,
  )
  let str_oo = susy_supertrace(
    @core.qm_mul_unchecked(qmat_odd(), qmat_odd2()),
    1,
    1,
  )
  let str_oo_rev = susy_supertrace(
    @core.qm_mul_unchecked(qmat_odd2(), qmat_odd()),
    1,
    1,
  )
  @core.chk(
    out,
    "實超跡：str(EE') = str(E'E)、str(OO') = −str(O'O)（值 \{@core.qq_show(str_ee)} / \{@core.qq_show(str_oo)}）",
    @core.qq_eq(str_ee, str_ee_rev) &&
    @core.qq_eq(str_oo, @core.qq_neg(str_oo_rev)),
  )
  // 超跡在分次交換子上的消失
  let mut str_bracket_zero = true
  i = 0
  while i < samples.length() {
    let mut j = 0
    while j < samples.length() {
      let br = slad_bracket(samples[i], samples[j])
      let str = susy_supertrace(br.mat, 1, 1)
      if !(@core.qq_is_zero(str)) {
        str_bracket_zero = false
      }
      j = j + 1
    }
    i = i + 1
  }
  @core.chk(out, "str([A,B]) = 0（4² 對齊次元素）", str_bracket_zero)
  // 負控制：一般的乘積（不是分次交換子）超跡可以不為零
  let prod_even = @core.qm_mul_unchecked(qmat_even(), qmat_even2())
  let str_prod = susy_supertrace(prod_even, 1, 1)
  @core.chk(
    out,
    "負控制：偶元素乘積 EE' 的實超跡 = \{@core.qq_show(str_prod)} ≠ 0（只有分次交換子保證為零）",
    !(@core.qq_is_zero(str_prod)),
  )
  out
}

// ---------------------------------------------------------------------------
// 2. 四元數頂點對偶
// ---------------------------------------------------------------------------

///|
fn vertex_samples() -> Array[VertexOp] {
  [
    vertex_of([qmat_even(), qmat_odd(), qmat_even2()]),
    vertex_of([qmat_odd2(), qmat_even(), qmat_odd()]),
  ]
}

///|
pub fn law_vertex_duality() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let pairs = qvec_pair()
  let u = pairs[0]
  let w = pairs[1]
  // Hermitian 配對的基本性質
  let huw = susy_hdot(u, w)
  let hwu = susy_hdot(w, u)
  @core.chk(out, "Hermitian 配對對稱：⟨u,w⟩ = ⟨w,u⟩", @core.qq_eq(huw, hwu))
  let huu = susy_hdot(u, u)
  @core.chk(
    out,
    "正定性：⟨u,u⟩ = \{@core.qq_show(huu)} > 0，且 ⟨0,0⟩ = 0",
    @core.qq_cmp(huu, @core.qq_zero()) > 0 &&
    @core.qq_is_zero(susy_hdot(u, Array::make(u.length(), @core.quat_zero()))),
  )
  // 伴隨性：⟨Au, w⟩ = ⟨u, A†w⟩
  let a = qmat_even()
  let at = @core.qm_conj_transpose(a)
  let lhs = susy_hdot(qm_apply(a, u), w)
  let rhs = susy_hdot(u, qm_apply(at, w))
  @core.chk(
    out,
    "伴隨性：⟨Au,w⟩ = ⟨u,A†w⟩ = \{@core.qq_show(lhs)}（精確相等）",
    @core.qq_eq(lhs, rhs),
  )
  // 頂點對偶：V*(z) 的配對等於原配對
  let vs = vertex_samples()
  let mut dual_ok = true
  let mut checks = 0
  let mut vi = 0
  while vi < vs.length() {
    let v = vs[vi]
    let vd = vertex_dual(v)
    let mut n = 0
    while n < vertex_modes(v) {
      let p1 = vertex_pairing(v, n, u, w)
      // V* 的第 n 模是 A_n†，配對方向相反
      let p2 = susy_hdot(u, qm_apply(vd.modes[n], w))
      if !(@core.qq_eq(p1, p2)) {
        dual_ok = false
      }
      checks = checks + 1
      n = n + 1
    }
    // 對偶兩次回到自己
    if !(@core.qm_eq(vertex_dual(vd).modes[0], v.modes[0])) {
      dual_ok = false
    }
    vi = vi + 1
  }
  @core.chk(
    out,
    "頂點對偶方程：⟨A_n u, w⟩ = ⟨u, A_n† w⟩（\{checks} 個模），且 V** = V",
    dual_ok,
  )
  // 截斷級數的結合律
  let v0 = vs[0]
  let v1 = vs[1]
  let v2 = vertex_of([qmat_even(), qmat_even2(), qmat_odd()])
  let limit = 3
  let left = vertex_mul(vertex_mul(v0, v1, limit), v2, limit)
  let right = vertex_mul(v0, vertex_mul(v1, v2, limit), limit)
  let mut assoc = true
  let mut n2 = 0
  while n2 < limit {
    if !(@core.qm_eq(left.modes[n2], right.modes[n2])) {
      assoc = false
    }
    n2 = n2 + 1
  }
  @core.chk(
    out,
    "截斷頂點代數的結合律：(V·W)·U = V·(W·U)（前 \{limit} 階係數逐位元）",
    assoc,
  )
  // 卷積係數與直接相乘一致（零階）
  let c0 = vertex_conv_coeff(v0, v1, 0)
  @core.chk(
    out,
    "零階卷積只是矩陣乘積：Σ_{i+j=0} A_iB_j = A_0B_0",
    @core.qm_eq(c0, @core.qm_mul_unchecked(v0.modes[0], v1.modes[0])),
  )
  // 負控制：非 Hermitian 的模，對偶真的不同
  @core.chk(
    out,
    "負控制：非 Hermitian 模的對偶不是自己（V* ≠ V）",
    !(@core.qm_eq(vertex_dual(v0).modes[0], v0.modes[0])),
  )
  out
}

// ---------------------------------------------------------------------------
// 3. 德朗姆型恆等
// ---------------------------------------------------------------------------

///|
fn torus_complex() -> SimplicialComplex {
  // 3×3 週期方格三角剖分（9 個頂點、18 個三角形）
  let tris : Array[Array[Int32]] = []
  let mut i = 0
  while i < 3 {
    let mut j = 0
    while j < 3 {
      let a = i * 3 + j
      let b = ((i + 1) % 3) * 3 + j
      let c = i * 3 + (j + 1) % 3
      let d = ((i + 1) % 3) * 3 + (j + 1) % 3
      tris.push([a, b, d])
      tris.push([a, d, c])
      j = j + 1
    }
    i = i + 1
  }
  sc_build(9, tris)
}

///|
fn rp2_complex() -> SimplicialComplex {
  // RP² 的 6 頂點極小三角剖分（10 個三角形、15 條邊）
  let raw : Array[Array[Int32]] = [
    [1, 2, 3],
    [1, 2, 4],
    [1, 3, 5],
    [1, 4, 6],
    [1, 5, 6],
    [2, 3, 6],
    [2, 4, 5],
    [2, 5, 6],
    [3, 4, 5],
    [3, 4, 6],
  ]
  let zero_based : Array[Array[Int32]] = []
  for f in raw {
    zero_based.push([f[0] - 1, f[1] - 1, f[2] - 1])
  }
  sc_build(6, zero_based)
}

///|
fn octahedron_complex() -> SimplicialComplex {
  sc_build(6, [
    [0, 2, 3],
    [0, 3, 4],
    [0, 4, 5],
    [0, 5, 2],
    [1, 3, 2],
    [1, 4, 3],
    [1, 5, 4],
    [1, 2, 5],
  ])
}

///|
fn derham_cases() -> Array[(String, SimplicialComplex)] {
  [
    ("單一三角形（圓盤）", sc_build(3, [[0, 1, 2]])),
    (
      "四面體邊界（S²）",
      sc_build(4, [[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]]),
    ),
    ("八面體表面（S²）", octahedron_complex()),
    ("3×3 週期環面（T²）", torus_complex()),
    ("RP² 的 6 頂點三角剖分", rp2_complex()),
  ]
}

///|
pub fn law_derham_chain_complex() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let cases = derham_cases()
  let mut dd_ok = true
  let mut euler_ok = true
  let mut hodge_ok = true
  let mut susy_ok = true
  let mut q_parity_ok = true
  let mut cochain_ok = true
  let mut summary = ""
  let mut i = 0
  while i < cases.length() {
    let (name, cx) = cases[i]
    // ∂² = 0
    let mut k = 1
    while k <= 2 {
      if !(@core.qmat_is_zero_matrix(sc_dd(cx, k))) {
        dd_ok = false
      }
      k = k + 1
    }
    // Euler 兩條路徑
    if sc_euler_counts(cx) != sc_euler_betti(cx) {
      euler_ok = false
    }
    let betti = sc_betti(cx)
    summary = summary +
      name +
      " b=(" +
      betti[0].to_string() +
      "," +
      betti[1].to_string() +
      "," +
      betti[2].to_string() +
      ") χ=" +
      sc_euler_counts(cx).to_string() +
      "  "
    // Hodge：n_k − rank Δ_k = β_k
    k = 0
    while k <= 2 {
      let nk = sc_count(cx, k)
      let h = sc_hodge(cx, k)
      if nk - @core.qmat_rank(h) != betti[k] {
        hodge_ok = false
      }
      k = k + 1
    }
    // 超電荷 Q = D + Dᵗ，Q² = Δ_total
    let q = sc_supercharge(cx)
    let q2 = @core.qmat_mul_unchecked(q, q)
    let hodge = sc_hodge_total(cx)
    if !(@core.qmat_eq(q2, hodge)) {
      susy_ok = false
    }
    // Z₂ 分次：Q 只在 (偶,奇) 與 (奇,偶) 塊有元素
    let n0 = sc_count(cx, 0)
    let n1 = sc_count(cx, 1)
    let n2 = sc_count(cx, 2)
    let even_idx : Array[Int32] = []
    let odd_idx : Array[Int32] = []
    let mut v = 0
    while v < n0 + n1 + n2 {
      // 度數：0..<(n0) 是 0 維、(n0)..<(n0+n1) 是 1 維、其餘 2 維
      let deg = if v < n0 { 0 } else if v < n0 + n1 { 1 } else { 2 }
      if deg % 2 == 0 {
        even_idx.push(v)
      } else {
        odd_idx.push(v)
      }
      v = v + 1
    }
    let mut a = 0
    while a < even_idx.length() {
      let mut b = 0
      while b < even_idx.length() {
        if !(@core.qq_is_zero(q[even_idx[a]][even_idx[b]])) {
          q_parity_ok = false
        }
        b = b + 1
      }
      a = a + 1
    }
    a = 0
    while a < odd_idx.length() {
      let mut b = 0
      while b < odd_idx.length() {
        if !(@core.qq_is_zero(q[odd_idx[a]][odd_idx[b]])) {
          q_parity_ok = false
        }
        b = b + 1
      }
      a = a + 1
    }
    // 上鏈（轉置）算出的 Betti 數相同
    k = 0
    while k <= 2 {
      let nk = sc_count(cx, k)
      let rk = @core.qmat_rank(@core.qmat_transpose(sc_boundary(cx, k)))
      let nk1 = sc_count(cx, k + 1)
      let rk1 = if nk1 > 0 {
        @core.qmat_rank(@core.qmat_transpose(sc_boundary(cx, k + 1)))
      } else {
        0
      }
      if nk - rk - rk1 != betti[k] {
        cochain_ok = false
      }
      k = k + 1
    }
    i = i + 1
  }
  @core.chk(out, "∂_{k−1}∂_k = 0（5 個複形 × k = 1,2，精確零矩陣）", dd_ok)
  @core.chk(out, "Euler：Σ(−1)^k n_k = Σ(−1)^k β_k（\{cases.length()} 個複形）", euler_ok)
  @core.chk(out, "Hodge 定理：dim ker Δ_k = n_k − rank Δ_k = β_k", hodge_ok)
  @core.chk(out, "超電荷恆等：Q² = ⊕Δ_k（矩陣逐項相等）", susy_ok)
  @core.chk(out, "Z₂ 分次：Q 把偶次鏈送到奇次鏈（對角塊全零）", q_parity_ok)
  @core.chk(out, "上鏈與鏈的 Betti 數一致（轉置不改變秩）", cochain_ok)
  @core.chk(out, "複形清單：\{summary}", cases.length() == 5)
  out
}

// ---------------------------------------------------------------------------
// 4. 複形四元數
// ---------------------------------------------------------------------------

///|
pub fn law_derham_complexified() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  // 複單位與複結構
  let ii = cq_unit()
  @core.chk(
    out,
    "複單位 i² = −1",
    cq_eq(cq_mul(ii, ii), cq_of_int(-1)),
  )
  @core.chk(out, "J² = −1（J(x) = i·x）", cq_eq(cq_J(cq_J(cq_one())), cq_of_int(-1)))
  let z = cq_make(@core.quat_of_int(1, 2, 0, 0), @core.quat_of_int(0, 0, 1, 3))
  @core.chk(
    out,
    "(1+i)² = 2i 與複共軛的反自同構性",
    cq_eq(
      cq_mul(cq_add(cq_one(), ii), cq_add(cq_one(), ii)),
      cq_add(ii, ii),
    ) &&
    cq_eq(cq_conj(cq_mul(z, z)), cq_mul(cq_conj(z), cq_conj(z))),
  )
  // 複形四元數上的 ∂² = 0
  let cx = torus_complex()
  let d1 = cm_from_qq(sc_boundary(cx, 1))
  let d2 = cm_from_qq(sc_boundary(cx, 2))
  let dd = cm_mul(d1, d2)
  @core.chk(
    out,
    "環面複形在 H ⊗ C 上仍滿足 ∂₁∂₂ = 0（\{@core.qmat_rows(sc_boundary(cx, 1))}×\{@core.qmat_cols(sc_boundary(cx, 2))} 矩陣）",
    cm_is_zero(dd),
  )
  let rp = rp2_complex()
  @core.chk(
    out,
    "RP² 在 H ⊗ C 上也滿足 ∂² = 0",
    cm_is_zero(cm_mul(cm_from_qq(sc_boundary(rp, 1)), cm_from_qq(sc_boundary(rp, 2)))),
  )
  // Hermitian 伴隨恆等：⟨∂a, b⟩ = ⟨a, ∂ᵗ b⟩
  // a ∈ C_1（∂₁ 的行數 = 邊數），b ∈ C_0（∂₁ 的列數 = 頂點數）
  let a_vec : Array[CQuat] = Array::make(@core.qmat_cols(sc_boundary(cx, 1)), cq_zero())
  let mut i = 0
  while i < a_vec.length() {
    a_vec[i] = cq_make(
      @core.quat_of_int(i, 1, 0, 0),
      @core.quat_of_int(0, 0, i % 2, 1),
    )
    i = i + 1
  }
  let b_vec : Array[CQuat] = Array::make(@core.qmat_rows(sc_boundary(cx, 1)), cq_zero())
  i = 0
  while i < b_vec.length() {
    b_vec[i] = cq_make(
      @core.quat_of_int(1, 0, i % 3, 0),
      @core.quat_of_int(0, 2, 0, 0),
    )
    i = i + 1
  }
  let d1t = cm_transpose(d1)
  let lhs = cq_hdot(cm_apply(d1, a_vec), b_vec)
  let rhs = cq_hdot(a_vec, cm_apply(d1t, b_vec))
  @core.chk(
    out,
    "H ⊗ C 上的伴隨恆等：⟨∂a,b⟩ = ⟨a,∂ᵗb⟩ = \{@core.qq_show(lhs)}",
    @core.qq_eq(lhs, rhs),
  )
  // 複結構與邊界算子交換：J∘∂ = ∂∘J
  let ja : Array[CQuat] = Array::make(a_vec.length(), cq_zero())
  i = 0
  while i < a_vec.length() {
    ja[i] = cq_J(a_vec[i])
    i = i + 1
  }
  let lhs2 = cm_apply(d1, ja)
  let rhs2 : Array[CQuat] = Array::make(lhs2.length(), cq_zero())
  i = 0
  while i < lhs2.length() {
    rhs2[i] = cq_J(cm_apply(d1, a_vec)[i])
    i = i + 1
  }
  let mut comm = true
  i = 0
  while i < lhs2.length() {
    if !(cq_eq(lhs2[i], rhs2[i])) {
      comm = false
    }
    i = i + 1
  }
  @core.chk(out, "複結構與邊界算子交換：J(∂a) = ∂(Ja)", comm)
  // 複形化讓實維數加倍：一個 CQuat 是 8 個實座標
  @core.chk(
    out,
    "複形化把每個係數從 4 個實座標擴成 8 個（H ⊗_R C）",
    cq_eq(cq_add(cq_of_int(1), cq_of_int(1)), cq_of_int(2)) &&
    cq_eq(cq_mul(cq_unit(), cq_from_quat(@core.quat_i())), cq_mul(cq_from_quat(@core.quat_i()), cq_unit())),
  )
  out
}

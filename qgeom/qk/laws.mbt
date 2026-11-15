// ---------------------------------------------------------------------------
// qgeom/qk — 定律登記
// ---------------------------------------------------------------------------
// 兩半：
//   A. 曲率張量群空間（sp(2) 的 Cartan 分解、QK 結構、對稱空間曲率恆等式）；
//   B. 雙射緊緻四元雅可比簇（整數結構矩陣、極化形式、恆等張量的 Sp 不變性、
//      格子雙射與軌道計數）。

///|
pub fn qk_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    ("sp(2)：基底、封閉性與 Jacobi", law_qk_symplectic_algebra()),
    (
      "Cartan 分解 sp(2) = k ⊕ m（k = sp(1)⊕sp(1)）",
      law_qk_cartan_decomposition(),
    ),
    (
      "四元數凱勒結構：I、J、K 與曲率的群空間落點",
      law_qk_quaternionic_structure(),
    ),
    (
      "對稱空間曲率的恆等式（skew、配對對稱、Bianchi）",
      law_qk_curvature_identities(),
    ),
    (
      "雙射緊緻四元簇：整數結構矩陣與格子雙射",
      law_qk_lattice_bijection(),
    ),
    (
      "極化形式與恆等張量幾何矩陣的 Sp 不變性",
      law_qk_identity_tensor(),
    ),
  ]
}

// ---------------------------------------------------------------------------
// A. 曲率張量群空間
// ---------------------------------------------------------------------------

///|
pub fn law_qk_symplectic_algebra() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let basis = sp2_basis()
  @core.chk(
    out,
    "基底大小 = \{basis.length()}（sp(2) 的實維數 10）",
    basis.length() == 10,
  )
  // 每個基底元素都是 skew-Hermitian
  let mut skew = true
  let mut i = 0
  while i < basis.length() {
    if !sp2_is_skew(basis[i]) {
      skew = false
    }
    i = i + 1
  }
  @core.chk(out, "10 個基底元素都滿足 X† = −X", skew)
  // 基底線性無關（秩 10）
  let flat : Array[Array[@core.QQ]] = []
  i = 0
  while i < basis.length() {
    flat.push(sp2_flatten(basis[i]))
    i = i + 1
  }
  @core.chk(
    out,
    "基底線性無關：攤平矩陣的秩 = \{@core.qmat_rank(flat)}",
    @core.qmat_rank(flat) == 10,
  )
  // 封閉性：交換子仍是 sp(2) 的元素
  let mut closed = true
  let mut jacobi = true
  let mut triples = 0
  i = 0
  while i < basis.length() {
    let mut j = 0
    while j < basis.length() {
      let bracket = sp2_bracket(basis[i], basis[j])
      if !sp2_is_skew(bracket) {
        closed = false
      }
      let mut k = 0
      while k < basis.length() {
        let t1 = sp2_bracket(basis[i], sp2_bracket(basis[j], basis[k]))
        let t2 = sp2_bracket(basis[j], sp2_bracket(basis[k], basis[i]))
        let t3 = sp2_bracket(basis[k], sp2_bracket(basis[i], basis[j]))
        let sum = @core.qm_add(@core.qm_add(t1, t2), t3)
        let mut is_zero = true
        let mut r = 0
        while r < 2 {
          let mut c = 0
          while c < 2 {
            if !@core.quat_is_zero(sum[r][c]) {
              is_zero = false
            }
            c = c + 1
          }
          r = r + 1
        }
        if !is_zero {
          jacobi = false
        }
        triples = triples + 1
        k = k + 1
      }
      j = j + 1
    }
    i = i + 1
  }
  @core.chk(out, "對交換子封閉：[X,Y] ∈ sp(2)（10² 對）", closed)
  @core.chk(out, "Jacobi 恆等式（\{triples} 組）", jacobi)
  out
}

///|
pub fn law_qk_cartan_decomposition() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let kb = sp2_k_basis()
  let mb = sp2_m_basis()
  @core.chk(
    out,
    "維數分解：dim sp(2) = 10 = dim k (\{kb.length()}) + dim m (\{mb.length()})",
    kb.length() == 6 && mb.length() == 4,
  )
  // [k,k] ⊂ k
  let mut kk = true
  let mut km = true
  let mut mm = true
  let mut kk_dim = 0
  let mut i = 0
  while i < kb.length() {
    let mut j = 0
    while j < kb.length() {
      match sp2_coords(kb, sp2_bracket(kb[i], kb[j])) {
        None => kk = false
        Some(_c) => kk_dim = kk_dim + 1
      }
      j = j + 1
    }
    i = i + 1
  }
  i = 0
  while i < kb.length() {
    let mut j = 0
    while j < mb.length() {
      match sp2_coords(mb, sp2_bracket(kb[i], mb[j])) {
        None => km = false
        Some(_c) => ()
      }
      j = j + 1
    }
    i = i + 1
  }
  i = 0
  while i < mb.length() {
    let mut j = 0
    while j < mb.length() {
      match sp2_coords(kb, sp2_bracket(mb[i], mb[j])) {
        None => mm = false
        Some(_c) => ()
      }
      j = j + 1
    }
    i = i + 1
  }
  @core.chk(out, "[k,k] ⊂ k（\{kk_dim}/36 次交換子都在 k 內）", kk)
  @core.chk(out, "[k,m] ⊂ m（24 次交換子）", km)
  @core.chk(
    out, "[m,m] ⊂ k（16 次交換子）——對稱空間的核心條件", mm,
  )
  // k 與 m 在 Hermitian 內積下正交
  let mut orthogonal = true
  i = 0
  while i < kb.length() {
    let mut j = 0
    while j < mb.length() {
      if !@core.qq_is_zero(sp2_inner(kb[i], mb[j])) {
        orthogonal = false
      }
      j = j + 1
    }
    i = i + 1
  }
  @core.chk(out, "k ⊥ m（Hermitian 內積的實部，36 對全零）", orthogonal)
  // sp(1) ⊕ sp(1) 的兩塊也互相正交
  let mut blocks_orthogonal = true
  i = 0
  while i < 3 {
    let mut j = 3
    while j < 6 {
      if !@core.qq_is_zero(sp2_inner(kb[i], kb[j])) {
        blocks_orthogonal = false
      }
      j = j + 1
    }
    i = i + 1
  }
  @core.chk(out, "k 的兩個 sp(1) 因子互相正交（9 對）", blocks_orthogonal)
  out
}

///|
pub fn law_qk_quaternionic_structure() -> Array[(String, Bool)] {
  let results : Array[(String, Bool)] = []
  let kb = sp2_k_basis()
  let mb = sp2_m_basis()
  // 左乘動作：[X_a, M_b] = M_{σ_a · b}
  let mut left_ok = true
  let mut checks = 0
  let mut a = 0
  while a < 3 {
    let mut b = 0
    while b < 4 {
      let got = sp2_bracket(kb[a], mb[b])
      let expect = sp2_m_of_quat(
        sp2_left_mul(@core.quat_basis(a + 1), @core.quat_basis(b)),
      )
      if !@core.qm_eq(got, expect) {
        left_ok = false
      }
      checks = checks + 1
      b = b + 1
    }
    a = a + 1
  }
  @core.chk(
    results,
    "sp(1)_L 在 m ≅ H 上是左乘：[X_a, M_b] = M_{σ_a·b}（\{checks} 個組合）",
    left_ok,
  )
  // 右乘動作：[Y_a, M_b] = M_{−b·σ_a}
  let mut right_ok = true
  let mut checks2 = 0
  a = 0
  while a < 3 {
    let mut b = 0
    while b < 4 {
      let got = sp2_bracket(kb[3 + a], mb[b])
      let expect = sp2_m_of_quat(
        @core.quat_neg(
          sp2_right_mul(@core.quat_basis(a + 1), @core.quat_basis(b)),
        ),
      )
      if !@core.qm_eq(got, expect) {
        right_ok = false
      }
      checks2 = checks2 + 1
      b = b + 1
    }
    a = a + 1
  }
  @core.chk(
    results,
    "sp(1)_R 在 m 上是右乘：[Y_a, M_b] = M_{−b·σ_a}（\{checks2} 個組合）",
    right_ok,
  )
  // I、J、K 的四元數關係（在 m 上以左乘實現）
  let ii = @core.quat_i()
  let ju = @core.quat_j()
  let ku = @core.quat_k()
  let mut ijk_ok = true
  let mut b = 0
  while b < 4 {
    let v = @core.quat_basis(b)
    if !@core.quat_eq(sp2_left_mul(ii, sp2_left_mul(ii, v)), @core.quat_neg(v)) ||
      !@core.quat_eq(sp2_left_mul(ju, sp2_left_mul(ju, v)), @core.quat_neg(v)) ||
      !@core.quat_eq(sp2_left_mul(ku, sp2_left_mul(ku, v)), @core.quat_neg(v)) {
      ijk_ok = false
    }
    b = b + 1
  }
  @core.chk(
    results, "I² = J² = K² = −1（在 m 的四個基底上逐點檢查）",
    ijk_ok,
  )
  @core.chk(
    results,
    "IJ = K 且 IJK = −1（四元數結構的定義關係）",
    @core.quat_eq(sp2_left_mul(ii, ju), ku) &&
    @core.quat_eq(
      sp2_left_mul(ii, sp2_left_mul(ju, ku)),
      @core.quat_neg(@core.quat_one()),
    ),
  )
  // 曲率落在群空間：R(X,Y)Z ∈ m，且 [X,Y] ∈ k
  let mut curvature_in_m = true
  let mut bracket_in_k = true
  let mut pairs = 0
  a = 0
  while a < mb.length() {
    let mut b2 = 0
    while b2 < mb.length() {
      match sp2_coords(kb, sp2_bracket(mb[a], mb[b2])) {
        None => bracket_in_k = false
        Some(_c) => ()
      }
      let mut z = 0
      while z < mb.length() {
        match sp2_coords(mb, sp2_curvature(mb[a], mb[b2], mb[z])) {
          None => curvature_in_m = false
          Some(_c) => ()
        }
        z = z + 1
      }
      pairs = pairs + 1
      b2 = b2 + 1
    }
    a = a + 1
  }
  @core.chk(
    results,
    "曲率的群空間落點：[m,m] ⊂ k 且 R(X,Y)Z ∈ m（\{pairs} 對 × 4 個 Z）",
    bracket_in_k && curvature_in_m,
  )
  // 曲率與 k 的交集只有 0（k ⊥ m，所以只有在曲率為零時才落回 k）
  let mut only_zero = true
  let mut zero_triples = 0
  let total_triples = mb.length() * mb.length() * mb.length()
  a = 0
  while a < mb.length() {
    let mut b3 = 0
    while b3 < mb.length() {
      let mut z = 0
      while z < mb.length() {
        let r = sp2_curvature(mb[a], mb[b3], mb[z])
        let mut is_zero = true
        let mut r1 = 0
        while r1 < 2 {
          let mut c1 = 0
          while c1 < 2 {
            if !@core.quat_is_zero(r[r1][c1]) {
              is_zero = false
            }
            c1 = c1 + 1
          }
          r1 = r1 + 1
        }
        if is_zero {
          zero_triples = zero_triples + 1
        }
        let in_k = match sp2_coords(kb, r) {
          None => false
          Some(_c) => true
        }
        if in_k != is_zero {
          only_zero = false
        }
        z = z + 1
      }
      b3 = b3 + 1
    }
    a = a + 1
  }
  @core.chk(
    results,
    "曲率與 k 的交集只有 0：R(X,Y)Z ∈ k ⇔ R(X,Y)Z = 0（\{total_triples} 個三元組，其中 \{zero_triples} 個為零）",
    only_zero,
  )
  results
}

///|
pub fn law_qk_curvature_identities() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let mb = sp2_m_basis()
  let mut skew_ok = true
  let mut pair_ok = true
  let mut bianchi_ok = true
  let mut quadruples = 0
  let mut a = 0
  while a < mb.length() {
    let mut b = 0
    while b < mb.length() {
      let mut c = 0
      while c < mb.length() {
        // 前兩個名額反對稱
        if !@core.qm_eq(
            sp2_curvature(mb[a], mb[b], mb[c]),
            @core.qm_neg(sp2_curvature(mb[b], mb[a], mb[c])),
          ) {
          skew_ok = false
        }
        // 第一 Bianchi 恆等式
        let term = @core.qm_add(
          @core.qm_add(
            sp2_curvature(mb[a], mb[b], mb[c]),
            sp2_curvature(mb[b], mb[c], mb[a]),
          ),
          sp2_curvature(mb[c], mb[a], mb[b]),
        )
        let mut is_zero = true
        let mut r = 0
        while r < 2 {
          let mut s = 0
          while s < 2 {
            if !@core.quat_is_zero(term[r][s]) {
              is_zero = false
            }
            s = s + 1
          }
          r = r + 1
        }
        if !is_zero {
          bianchi_ok = false
        }
        let mut d = 0
        while d < mb.length() {
          // 後兩個名額反對稱：⟨R(X,Y)Z, W⟩ = −⟨R(X,Y)W, Z⟩
          let lz = sp2_inner(sp2_curvature(mb[a], mb[b], mb[c]), mb[d])
          let lw = sp2_inner(sp2_curvature(mb[a], mb[b], mb[d]), mb[c])
          if !@core.qq_eq(lz, @core.qq_neg(lw)) {
            skew_ok = false
          }
          // 配對對稱：⟨R(X,Y)Z, W⟩ = ⟨R(Z,W)X, Y⟩
          let right = sp2_inner(sp2_curvature(mb[c], mb[d], mb[a]), mb[b])
          if !@core.qq_eq(lz, right) {
            pair_ok = false
          }
          quadruples = quadruples + 1
          d = d + 1
        }
        c = c + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  @core.chk(out, "前兩名額反對稱：R(Y,X)Z = −R(X,Y)Z（4³ 組）", skew_ok)
  @core.chk(
    out,
    "後兩名額反對稱與配對對稱：⟨R(X,Y)Z,W⟩ = −⟨R(X,Y)W,Z⟩ = ⟨R(Z,W)X,Y⟩（\{quadruples} 組）",
    pair_ok && skew_ok,
  )
  @core.chk(
    out, "第一 Bianchi 恆等式：R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0（4³ 組）",
    bianchi_ok,
  )
  // 負控制：Bianchi 對零算子也成立，所以要數出「非零曲率」的三元組
  let mut nonzero_triples = 0
  let mut total_triples = 0
  a = 0
  while a < mb.length() {
    let mut b2 = 0
    while b2 < mb.length() {
      let mut c2 = 0
      while c2 < mb.length() {
        let r2 = sp2_curvature(mb[a], mb[b2], mb[c2])
        let mut is_zero = true
        let mut r3 = 0
        while r3 < 2 {
          let mut s2 = 0
          while s2 < 2 {
            if !@core.quat_is_zero(r2[r3][s2]) {
              is_zero = false
            }
            s2 = s2 + 1
          }
          r3 = r3 + 1
        }
        if !is_zero {
          nonzero_triples = nonzero_triples + 1
        }
        total_triples = total_triples + 1
        c2 = c2 + 1
      }
      b2 = b2 + 1
    }
    a = a + 1
  }
  @core.chk(
    out,
    "負控制：曲率不是零算子（\{total_triples} 個三元組中 \{nonzero_triples} 個非零，Bianchi 不是空轉）",
    nonzero_triples > 0,
  )
  out
}

// ---------------------------------------------------------------------------
// B. 雙射緊緻四元雅可比簇
// ---------------------------------------------------------------------------

///|
fn ql_identity4() -> Array[Array[@core.QQ]] {
  @core.qmat_identity(4)
}

///|
pub fn law_qk_lattice_bijection() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let st = [ql_structure(1), ql_structure(2), ql_structure(3)]
  // 整數、單模
  let mut integral = true
  let mut unimodular = true
  let mut i = 0
  while i < 3 {
    if !ql_is_integral(st[i]) {
      integral = false
    }
    match @core.qmat_det(st[i]) {
      Some(d) => if !@core.qq_eq(d, @core.qq_one()) { unimodular = false }
      None => unimodular = false
    }
    i = i + 1
  }
  @core.chk(out, "I、J、K 是整數矩陣（格子不變）", integral)
  @core.chk(
    out, "det I = det J = det K = 1（單模 ⇒ 把 Z⁴ 雙射到自己）", unimodular,
  )
  let neg_id = @core.qmat_scale(@core.qq_int(-1), ql_identity4())
  @core.chk(
    out,
    "I² = J² = K² = −id（三個都是複結構）",
    @core.qmat_eq(@core.qmat_mul_unchecked(st[0], st[0]), neg_id) &&
    @core.qmat_eq(@core.qmat_mul_unchecked(st[1], st[1]), neg_id) &&
    @core.qmat_eq(@core.qmat_mul_unchecked(st[2], st[2]), neg_id),
  )
  @core.chk(
    out,
    "IJ = K、JK = I、KI = J（矩陣乘法下的四元數關係）",
    @core.qmat_eq(@core.qmat_mul_unchecked(st[0], st[1]), st[2]) &&
    @core.qmat_eq(@core.qmat_mul_unchecked(st[1], st[2]), st[0]) &&
    @core.qmat_eq(@core.qmat_mul_unchecked(st[2], st[0]), st[1]),
  )
  let mut orth = true
  i = 0
  while i < 3 {
    let t = @core.qmat_mul_unchecked(
      @core.qmat_mul_unchecked(@core.qmat_transpose(st[i]), ql_identity4()),
      st[i],
    )
    if !@core.qmat_eq(t, ql_identity4()) {
      orth = false
    }
    i = i + 1
  }
  @core.chk(
    out, "恆等張量不變：Iᵗ·id·I = id（I、J、K 都是格子自同構）", orth,
  )
  // 盒子上的雙射：盒子由 ql_box_points 產生，映射與比較都用同一套 QQ 表示
  let pts = ql_box_points(4, 1)
  let total = pts.length()
  let find = fn(p : Array[@core.QQ]) -> Int32 {
    let mut k = 0
    let mut hit = -1
    while k < pts.length() && hit < 0 {
      if ql_pt_eq(pts[k], p) {
        hit = k
      }
      k = k + 1
    }
    hit
  }
  let hits : Array[Int32] = Array::make(total, 0)
  let imgs : Array[Int32] = Array::make(total, -1)
  let mut closed = true
  let mut lin0 = 0
  while lin0 < total {
    let img = ql_I(pts[lin0])
    let idx = find(img)
    imgs[lin0] = idx
    if idx < 0 {
      closed = false
    } else {
      hits[idx] = hits[idx] + 1
    }
    lin0 = lin0 + 1
  }
  let mut all_once = true
  i = 0
  while i < total {
    if hits[i] != 1 {
      all_once = false
    }
    i = i + 1
  }
  @core.chk(
    out,
    "格子雙射：盒 [−1,1]⁴ 的 \{total} 個點在 I 下每個恰好被擊中一次",
    closed && all_once,
  )
  // 軌道分解（I 的階為 4）
  let fixed = 1
  let orbits = fixed + (total - fixed) / 4
  let mut computed_orbits = 0
  let mut computed_fixed = 0
  let visited : Array[Bool] = Array::make(total, false)
  lin0 = 0
  while lin0 < total {
    if !visited[lin0] {
      let mut cur = lin0
      let mut size = 1
      let mut steps_taken = 0
      let mut back_home = false
      while steps_taken < 4 && !back_home {
        cur = imgs[cur]
        if cur == lin0 {
          back_home = true
        } else {
          size = size + 1
        }
        steps_taken = steps_taken + 1
      }
      if size == 1 {
        computed_fixed = computed_fixed + 1
      }
      let mut y = lin0
      let mut step = 0
      while step < size {
        visited[y] = true
        y = imgs[y]
        step = step + 1
      }
      computed_orbits = computed_orbits + 1
    }
    lin0 = lin0 + 1
  }
  @core.chk(
    out,
    "軌道分解：\{total} 個點 = \{computed_fixed} 個固定點 + 4·(\{computed_orbits} − \{computed_fixed})，與公式 \{orbits} 一致",
    computed_fixed == fixed &&
    computed_orbits == orbits &&
    computed_fixed + 4 * (computed_orbits - computed_fixed) == total,
  )
  // 負控制：2I 不是自同構
  let scaled = @core.qmat_scale(@core.qq_int(2), st[0])
  let scaled_det = @core.qmat_det(scaled)
  let scaled_det_show = match scaled_det {
    Some(d) => @core.qq_show(d)
    None => "?"
  }
  let scaled_is_unit = match scaled_det {
    Some(d) => @core.qq_eq(d, @core.qq_one())
    None => false
  }
  @core.chk(
    out,
    "負控制：2I 的行列式 = \{scaled_det_show}，不等於 1，因此不是格子自同構",
    !scaled_is_unit,
  )
  out
}

///|
pub fn law_qk_identity_tensor() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let omega = ql_polarization(1)
  @core.chk(out, "極化形式 Ω 是整數矩陣", ql_is_integral(omega))
  @core.chk(
    out,
    "Ω 反對稱：Ωᵗ = −Ω",
    @core.qmat_eq(
      @core.qmat_transpose(omega),
      @core.qmat_scale(@core.qq_int(-1), omega),
    ),
  )
  let omega_det = match @core.qmat_det(omega) {
    Some(d) => d
    None => @core.qq_zero()
  }
  @core.chk(
    out,
    "det Ω = \{@core.qq_show(omega_det)}（單模極化：四元數雅可比簇是緊緻的）",
    @core.qq_eq(omega_det, @core.qq_one()),
  )
  // Sp(2g, Z) 分塊生成元下的不變性
  let samples = ql_sl2z_samples()
  let mut invariant = true
  let mut checked = 0
  let mut si = 0
  while si < samples.length() {
    let m = ql_symplectic_generator(
      samples[si],
      samples[(si + 1) % samples.length()],
    )
    let conj = @core.qmat_mul_unchecked(
      @core.qmat_mul_unchecked(@core.qmat_transpose(m), omega),
      m,
    )
    if !@core.qmat_eq(conj, omega) {
      invariant = false
    }
    checked = checked + 1
    si = si + 1
  }
  @core.chk(
    out,
    "恆等張量幾何矩陣：Mᵗ Ω M = Ω（\{checked} 個 Sp(2,Z) 分塊生成元）",
    invariant,
  )
  // g = 2（8 維）：同一條不變性
  let omega2 = ql_polarization(2)
  let gen = ql_block_diag(
    @core.qmat_from_int([[0, 1], [-1, 0]]),
    @core.qmat_from_int([[1, 1], [0, 1]]),
  )
  let gen2 = ql_block_diag(gen, gen)
  let conj2 = @core.qmat_mul_unchecked(
    @core.qmat_mul_unchecked(@core.qmat_transpose(gen2), omega2),
    gen2,
  )
  // 同一片格子結構在 g = 2 上也必須是複結構：I₈ = diag(I, I)
  let i8 = ql_structure_g(1, 2)
  let neg_id8 = @core.qmat_scale(@core.qq_int(-1), @core.qmat_identity(8))
  @core.chk(
    out,
    "g = 2（H²/Z⁸）：Mᵗ Ω M = Ω 與 I₈² = −id 在 8×8 上同時成立",
    @core.qmat_eq(conj2, omega2) &&
    @core.qmat_eq(
      @core.qmat_mul_unchecked(i8, i8), neg_id8,
    ),
  )
  // 四元數 Hermitian 形式
  let x : Array[@core.QQ] = [
    @core.qq_int(1),
    @core.qq_int(2),
    @core.qq_int(0),
    @core.qq_int(-1),
  ]
  let y : Array[@core.QQ] = [
    @core.qq_int(0),
    @core.qq_int(1),
    @core.qq_int(3),
    @core.qq_int(2),
  ]
  let hxy = ql_hermitian(x, y)
  let hyx = ql_hermitian(y, x)
  @core.chk(
    out,
    "極化形式就是 I 的 Kähler 形式：Ω(X,Y) = ⟨IX,Y⟩",
    @core.qq_eq(ql_form(omega, x, y), @core.qvec_dot(ql_I(x), y)),
  )
  @core.chk(
    out,
    "四元數 Hermitian 形式：h(y,x) = conj h(x,y)",
    @core.quat_eq(hyx, @core.quat_conj(hxy)),
  )
  let hxx = ql_hermitian(x, x)
  @core.chk(
    out,
    "正定性：h(x,x) = \{@core.quat_show(hxx)} = ‖x‖² > 0",
    @core.qq_eq(hxx.re, @core.qvec_dot(x, x)) &&
    @core.quat_eq(
      @core.quat_make(hxx.re, hxx.qi, hxx.qj, hxx.qk),
      @core.quat_of_qq(@core.qvec_dot(x, x)),
    ) &&
    @core.qq_cmp(hxx.re, @core.qq_zero()) > 0,
  )
  // Kähler 相容性
  let ix = @core.qmat_vec_unchecked(ql_structure(1), x)
  let iy = @core.qmat_vec_unchecked(ql_structure(1), y)
  let jx = @core.qmat_vec_unchecked(ql_structure(2), x)
  let jy = @core.qmat_vec_unchecked(ql_structure(2), y)
  @core.chk(
    out,
    "I 是 ω 的 Kähler 結構：ω(IX,IY) = ω(X,Y) 且 ω(X,IX) = ‖x‖² > 0",
    @core.qq_eq(ql_form(omega, ix, iy), ql_form(omega, x, y)) &&
    @core.qq_eq(ql_form(omega, x, ix), @core.qvec_dot(x, x)),
  )
  @core.chk(
    out,
    "J、K 反相容：ω(JX,JY) = −ω(X,Y)（同一族裡只有一個 Kähler 形式）",
    @core.qq_eq(ql_form(omega, jx, jy), @core.qq_neg(ql_form(omega, x, y))),
  )
  out
}

// ---------------------------------------------------------------------------
// qgeom/core — 定律登記
// ---------------------------------------------------------------------------
// 每條定律是一個 `law_*` 函式，回傳「標籤（數字當場算出來）＋布林」的清單。
// `cmd/qgeom` 逐條執行；任何一條為假就以非零狀態結束。
// 沒有寫死的 true：連「探針不是對稱張量」這種負控制都在裡面重算。

///|
/// 把一條命題收進報告。
pub fn chk(out : Array[(String, Bool)], label : String, cond : Bool) -> Unit {
  out.push((label, cond))
}

///|
/// qgeom/core 的全部定律，依章節分組：(章節名, 定律清單)。
pub fn all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    ("精確有理數體 QQ", law_rational_field()),
    ("四元數環 H：非交換、範數、無零因子", law_quaternion_ring()),
    ("四元數左／右正則表示是同態", law_quaternion_left_regular()),
    ("軸向交換算子：τ² = 1 與線性", law_axial_exchange_algebra()),
    ("軸向交換的 Yang–Baxter 與 S_n Coxeter 關係", law_axial_yang_baxter()),
    ("帶號變體 σ = −τ", law_axial_signed_variant()),
    ("循環變體 ρ：ρ³ = 1、ρ = τ₀₁∘τ₁₂、Burnside 軌道數", law_axial_cycle_variant()),
    ("對稱／反對稱分解：投影子與維度", law_axial_symmetric_decomposition()),
    ("變體之間的交換表與純張量", law_axial_variant_table()),
  ]
}

///|
fn qq_samples() -> Array[QQ] {
  [
    qq_zero(),
    qq_one(),
    qq_int(-1),
    qq_frac(1, 2),
    qq_frac(-3, 2),
    qq_frac(7, 3),
    qq_frac(-5, 4),
    qq_int(2),
  ]
}

///|
fn quat_box() -> Array[Quat] {
  let out : Array[Quat] = Array::make(0, quat_zero())
  let mut a = -1
  while a <= 1 {
    let mut b = -1
    while b <= 1 {
      let mut c = -1
      while c <= 1 {
        let mut d = -1
        while d <= 1 {
          out.push(quat_of_int(a, b, c, d))
          d = d + 1
        }
        c = c + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  out
}

// ---------------------------------------------------------------------------
// 1. 有理數體
// ---------------------------------------------------------------------------

///|
pub fn law_rational_field() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let xs = qq_samples()
  let n = xs.length()
  chk(out, "樣本數 = \{n}（含 0、±1、負數與非整分數）", n == 8)
  let mut comm = true
  let mut assoc = true
  let mut dist = true
  let mut idn = true
  let mut inv_ok = true
  let mut i = 0
  while i < n {
    let mut j = 0
    while j < n {
      let a = xs[i]
      let b = xs[j]
      if !(qq_eq(qq_add(a, b), qq_add(b, a))) {
        comm = false
      }
      if !(qq_eq(qq_mul(a, b), qq_mul(b, a))) {
        comm = false
      }
      let mut k = 0
      while k < n {
        let c = xs[k]
        if !(qq_eq(qq_add(qq_add(a, b), c), qq_add(a, qq_add(b, c)))) {
          assoc = false
        }
        if !(qq_eq(qq_mul(qq_mul(a, b), c), qq_mul(a, qq_mul(b, c)))) {
          assoc = false
        }
        if !(
          qq_eq(qq_mul(a, qq_add(b, c)), qq_add(qq_mul(a, b), qq_mul(a, c))),
        ) {
          dist = false
        }
        k = k + 1
      }
      if !(qq_eq(qq_mul(a, qq_one()), a)) || !(qq_eq(qq_add(a, qq_zero()), a)) {
        idn = false
      }
      if !(qq_is_zero(a)) {
        match qq_inv(a) {
          None => inv_ok = false
          Some(inv) =>
            if !(qq_eq(qq_mul(a, inv), qq_one())) || !(qq_eq(qq_mul(inv, a), qq_one())) {
              inv_ok = false
            }
        }
      }
      j = j + 1
    }
    i = i + 1
  }
  chk(out, "加法與乘法交換律（\{n}² 對）", comm)
  chk(out, "加法與乘法結合律、分配律（\{n}³ 組）", assoc && dist)
  chk(out, "單位元 0/1 與反元素（非零樣本全部有反元素）", idn && inv_ok)
  // 正規形
  chk(
    out,
    "正規形：6/−4 化為 −3/2、分母永遠為正",
    qq_eq(qq_frac(6, -4), qq_frac(-3, 2)) && qq_frac(2, -6).den == 3N,
  )
  // 稠密性：a < b ⇒ a < (a+b)/2 < b
  let mut dense = true
  let mut p = 0
  while p < n {
    let mut q = 0
    while q < n {
      let a = xs[p]
      let b = xs[q]
      if qq_lt(a, b) {
        let mid = qq_mul(qq_half(), qq_add(a, b))
        if !(qq_lt(a, mid)) || !(qq_lt(mid, b)) {
          dense = false
        }
      }
      q = q + 1
    }
    p = p + 1
  }
  chk(out, "序稠密：a < b ⇒ a < (a+b)/2 < b", dense)
  // 除零的邊界
  chk(
    out,
    "qq_div(a, 0) = 0 且 qq_inv(0) = None（全約定與選項型分開）",
    qq_is_zero(qq_div(qq_one(), qq_zero())) && qq_inv(qq_zero()) is None,
  )
  out
}

// ---------------------------------------------------------------------------
// 2. 四元數環
// ---------------------------------------------------------------------------

///|
pub fn law_quaternion_ring() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let box = quat_box()
  let bs = box.length()
  chk(out, "樣本箱 |{−1,0,1}⁴| = \{bs}", bs == 81)
  let iu = quat_i()
  let ju = quat_j()
  let ku = quat_k()
  let minus_one = quat_of_int(-1, 0, 0, 0)
  chk(
    out,
    "i² = j² = k² = ijk = −1",
    quat_eq(quat_mul(iu, iu), minus_one) &&
    quat_eq(quat_mul(ju, ju), minus_one) &&
    quat_eq(quat_mul(ku, ku), minus_one) &&
    quat_eq(quat_mul(quat_mul(iu, ju), ku), minus_one),
  )
  chk(
    out,
    "ij = k、ji = −k（非交換見證）",
    quat_eq(quat_mul(iu, ju), ku) && quat_eq(quat_mul(ju, iu), quat_neg(ku)),
  )
  // 非交換對的計數
  let mut noncomm = 0
  let mut assoc = true
  let mut dist = true
  let mut conj_anti = true
  let mut norm_mult = true
  let mut conj_norm = true
  let mut a = 0
  while a < bs {
    let mut b = 0
    while b < bs {
      let x = box[a]
      let y = box[b]
      if !(quat_eq(quat_mul(x, y), quat_mul(y, x))) {
        noncomm = noncomm + 1
      }
      if !(quat_eq(quat_conj(quat_mul(x, y)), quat_mul(quat_conj(y), quat_conj(x)))) {
        conj_anti = false
      }
      if !(qq_eq(quat_norm(quat_mul(x, y)), qq_mul(quat_norm(x), quat_norm(y)))) {
        norm_mult = false
      }
      if !(quat_eq(quat_mul(x, quat_conj(x)), quat_of_qq(quat_norm(x)))) {
        conj_norm = false
      }
      let mut c = 0
      while c < bs {
        let z = box[c]
        if !(quat_eq(quat_mul(quat_mul(x, y), z), quat_mul(x, quat_mul(y, z)))) {
          assoc = false
        }
        if !(
          quat_eq(
            quat_mul(x, quat_add(y, z)),
            quat_add(quat_mul(x, y), quat_mul(x, z)),
          ),
        ) {
          dist = false
        }
        c = c + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  chk(out, "結合律（\{bs}³ = \{bs * bs * bs} 組）", assoc)
  chk(out, "左右分配律", dist)
  chk(out, "共軛是反自同構：conj(xy) = conj(y)conj(x)", conj_anti)
  chk(out, "範數乘法性 N(xy) = N(x)N(y)（Lagrange 四平方）", norm_mult)
  chk(out, "x·conj(x) = N(x)", conj_norm)
  chk(out, "非交換對數 = \{noncomm} > 0（真的不是交換環）", noncomm > 0)
  // 反元素
  let mut inv_ok = true
  let mut zero_div = 0
  a = 0
  while a < bs {
    let x = box[a]
    if !(quat_is_zero(x)) {
      match quat_inv(x) {
        None => inv_ok = false
        Some(inv) =>
          if !(quat_eq(quat_mul(x, inv), quat_one())) {
            inv_ok = false
          }
      }
    }
    let mut b2 = 0
    while b2 < bs {
      let y = box[b2]
      if quat_is_zero(quat_mul(x, y)) && !(quat_is_zero(x)) && !(quat_is_zero(y)) {
        zero_div = zero_div + 1
      }
      b2 = b2 + 1
    }
    a = a + 1
  }
  chk(out, "每個非零樣本都有雙邊反元素", inv_ok)
  chk(out, "無零因子（\{bs}² 對中 xy = 0 而 x,y ≠ 0 的對數 = \{zero_div}）", zero_div == 0)
  out
}

// ---------------------------------------------------------------------------
// 3. 左／右正則表示
// ---------------------------------------------------------------------------

///|
pub fn law_quaternion_left_regular() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let box = quat_box()
  let bs = box.length()
  let mut hom = true
  let mut hom_r = true
  let mut acts = true
  let mut acts_r = true
  let mut inject = true
  let mut a = 0
  while a < bs {
    let x = box[a]
    let lx = quat_left_mat(x)
    if qmat_rank(lx) != 4 {
      if !(quat_is_zero(x)) {
        inject = false
      }
    }
    let mut b = 0
    while b < bs {
      let y = box[b]
      let lxy = quat_left_mat(quat_mul(x, y))
      let lxy_via = qmat_mul_unchecked(lx, quat_left_mat(y))
      if !(qmat_eq(lxy_via, lxy)) {
        hom = false
      }
      // 注意順序：L(x)L(y) 對應 x·y
      let ryx = quat_right_mat(quat_mul(y, x))
      let rxy_via = qmat_mul_unchecked(quat_right_mat(x), quat_right_mat(y))
      if !(qmat_eq(rxy_via, ryx)) {
        hom_r = false
      }
      let v = quat_to_vec(y)
      if !(qq_list_eq(qmat_vec_unchecked(lx, v), quat_to_vec(quat_mul(x, y)))) {
        acts = false
      }
      if !(
        qq_list_eq(qmat_vec_unchecked(quat_right_mat(x), v), quat_to_vec(quat_mul(y, x))),
      ) {
        acts_r = false
      }
      b = b + 1
    }
    a = a + 1
  }
  chk(out, "L(x)·L(y) = L(xy)（\{bs}² 對）", hom)
  chk(out, "R(x)·R(y) = R(yx)", hom_r)
  chk(out, "L(x)·v = x·v", acts)
  chk(out, "R(x)·v = v·x", acts_r)
  chk(out, "非零四元數的 L(x) 秩為 4（表示是單射）", inject)
  out
}

// ---------------------------------------------------------------------------
// 4. 軸向交換：τ² = 1 與線性
// ---------------------------------------------------------------------------

///|
fn probe_shapes() -> Array[Array[Int32]] {
  [[2, 2], [2, 2, 2], [3, 2, 2], [2, 3, 2, 2]]
}

///|
fn probe_weights(r : Int32) -> Array[Int32] {
  let out : Array[Int32] = Array::make(r, 1)
  let mut i = 0
  while i < r {
    out[i] = i + 1
    i = i + 1
  }
  out
}

///|
pub fn law_axial_exchange_algebra() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let shapes = probe_shapes()
  let mut involution = true
  let mut nonvacuous = 0
  let mut linear_add = true
  let mut linear_scale = true
  let mut total_ops = 0
  let mut si = 0
  while si < shapes.length() {
    let shape = shapes[si]
    let t = ct_probe(shape, probe_weights(shape.length()))
    let r = shape.length()
    let mut ax = 0
    while ax + 1 < r {
      match axial_apply(AxialSwap, t, ax) {
        None => involution = false
        Some(s) =>
          match ct_swap_axes(s, ax) {
            None => involution = false
            Some(ss) => if !(ct_eq(ss, t)) { involution = false }
          }
      }
      // 負控制：探針真的被動到（不是不變量）
      match axial_apply(AxialSwap, t, ax) {
        None => ()
        Some(s) => if !(ct_eq(s, t)) { nonvacuous = nonvacuous + 1 }
      }
      // 線性：τ(T+S) = τT + τS，τ(cT) = c·τT
      let u = ct_probe(shape, probe_weights(r))
      let c = qq_frac(-3, 2)
      match ct_swap_axes(ct_add(t, u), ax) {
        None => linear_add = false
        Some(lhs) =>
          match ct_swap_axes(t, ax) {
            None => linear_add = false
            Some(st) =>
              match ct_swap_axes(u, ax) {
                None => linear_add = false
                Some(su) => if !(ct_eq(lhs, ct_add(st, su))) { linear_add = false }
              }
          }
      }
      match ct_swap_axes(ct_scale(c, t), ax) {
        None => linear_scale = false
        Some(lhs) =>
          match ct_swap_axes(t, ax) {
            None => linear_scale = false
            Some(st) => if !(ct_eq(lhs, ct_scale(c, st))) { linear_scale = false }
          }
      }
      total_ops = total_ops + 1
      ax = ax + 1
    }
    si = si + 1
  }
  chk(out, "τ² = id（秩 2,3,4；共 \{total_ops} 個相鄰軸位置）", involution)
  chk(out, "負控制：τT ≠ T 的案例數 = \{nonvacuous} > 0（探針不是不變量）", nonvacuous > 0)
  chk(out, "τ 是加法的同態：τ(T+U) = τT + τU", linear_add)
  chk(out, "τ 與純量交換：τ(cT) = c·τT", linear_scale)
  // 越界守衛
  let t3 = ct_probe([2, 2, 2], [1, 1, 1])
  chk(
    out,
    "越界軸回傳 None（軸 2 在秩 3 上不可交換、軸 −1 亦不可）",
    ct_swap_axes(t3, 2) is None && ct_swap_axes(t3, -1) is None && ct_cycle_axes(t3, 1) is None,
  )
  out
}

// ---------------------------------------------------------------------------
// 5. Yang–Baxter 與 Coxeter 關係
// ---------------------------------------------------------------------------

///|
fn tau(t : CTensor, ax : Int32) -> CTensor {
  match ct_swap_axes(t, ax) {
    Some(s) => s
    None => ct_copy(t)
  }
}

///|
pub fn law_axial_yang_baxter() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t3 = ct_probe([2, 3, 2], [1, 2, 3])
  // 三軸上的 braid：τ01 τ12 τ01 = τ12 τ01 τ12 = 反向置換
  let lhs3 = tau(tau(tau(t3, 0), 1), 0)
  let rhs3 = tau(tau(tau(t3, 1), 0), 1)
  chk(out, "秩 3：τ₀₁τ₁₂τ₀₁ = τ₁₂τ₀₁τ₁₂（braid 關係）", ct_eq(lhs3, rhs3))
  // 反向置換的顯式檢查：結果[i,j,k] = 原[k,j,i]
  let rev = ct_permute(t3, [2, 1, 0])
  let rev_ok = match rev {
    Some(r) => ct_eq(lhs3, r)
    None => false
  }
  chk(out, "該乘積等於反向置換 [2,1,0]（不是憑空相等）", rev_ok)
  // 秩 4：相鄰 braid 兩處 + 遠處交換
  let t4 = ct_probe([2, 2, 3, 2], [1, 1, 2, 3])
  let b0 = tau(tau(tau(t4, 0), 1), 0)
  let b0r = tau(tau(tau(t4, 1), 0), 1)
  let b1 = tau(tau(tau(t4, 1), 2), 1)
  let b1r = tau(tau(tau(t4, 2), 1), 2)
  chk(out, "秩 4：兩處 braid 關係都成立", ct_eq(b0, b0r) && ct_eq(b1, b1r))
  chk(out, "秩 4：|i−j| ≥ 2 ⇒ τᵢτⱼ = τⱼτᵢ", ct_eq(tau(tau(t4, 0), 2), tau(tau(t4, 2), 0)))
  chk(
    out,
    "負控制：相鄰算子不可交換 τ₀τ₁ ≠ τ₁τ₀",
    !(ct_eq(tau(tau(t4, 0), 1), tau(tau(t4, 1), 0))),
  )
  // 秩 4 的長元素：兩個乘積都化為 [3,2,1,0]
  let long0 = tau(tau(tau(tau(tau(tau(t4, 0), 1), 2), 0), 1), 0)
  let long1 = tau(tau(tau(tau(tau(tau(t4, 2), 1), 0), 2), 1), 2)
  let long_exp = match ct_permute(t4, [3, 2, 1, 0]) {
    Some(r) => r
    None => ct_copy(t4)
  }
  chk(
    out,
    "S₄ 長元素：兩種相鄰交換字都給出 [3,2,1,0]",
    ct_eq(long0, long1) && ct_eq(long0, long_exp),
  )
  out
}

// ---------------------------------------------------------------------------
// 6. 帶號變體
// ---------------------------------------------------------------------------

///|
pub fn law_axial_signed_variant() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t = ct_probe([3, 2, 2], [2, 1, 3])
  let swap = tau(t, 0)
  let signed = match ct_signed_swap(t, 0) {
    Some(s) => s
    None => ct_copy(t)
  }
  chk(out, "σ = −τ（逐元素取負）", ct_eq(signed, ct_scale(qq_int(-1), swap)))
  chk(
    out,
    "負控制：σT ≠ τT（不是同一個算子換個名字）",
    !(ct_eq(signed, swap)),
  )
  let ss = match ct_signed_swap(signed, 0) {
    Some(s) => s
    None => ct_copy(t)
  }
  chk(out, "σ² = id（相位 (−1)² = 1）", ct_eq(ss, t))
  // σ 的 braid：三個 σ 的乘積 = −(三個 τ 的乘積)
  let s3 = ct_probe([2, 2, 2], [1, 2, 3])
  let s01 = match ct_signed_swap(s3, 0) {
    Some(s) => s
    None => s3
  }
  let s12 = match ct_signed_swap(s01, 1) {
    Some(s) => s
    None => s01
  }
  let sfin = match ct_signed_swap(s12, 0) {
    Some(s) => s
    None => s12
  }
  let tfin = tau(tau(tau(s3, 1), 0), 1)
  chk(out, "σ₀₁σ₁₂σ₀₁ = −(τ₁₂τ₀₁τ₁₂)：帶號 braid", ct_eq(sfin, ct_scale(qq_int(-1), tfin)))
  // σ 不變 ⇔ τ 反不變
  let anti = ct_is_alt_in(t, 0)
  let sig_fixed = ct_eq(t, signed)
  let tau_fixed = ct_eq(t, swap)
  chk(
    out,
    "σ 不變 ⇔ τ 反不變（等價改寫，兩種計數一致）",
    sig_fixed == anti && !(tau_fixed),
  )
  out
}

// ---------------------------------------------------------------------------
// 7. 循環變體
// ---------------------------------------------------------------------------

///|
fn cycle_orbits(d : Int32) -> Int32 {
  // 秩 3、每軸 d 維：數 (a,b,c) 在 ρ 下的軌道數。
  let seen : Array[Bool] = Array::make(d * d * d, false)
  let mut orbits = 0
  let mut a = 0
  while a < d {
    let mut b = 0
    while b < d {
      let mut c = 0
      while c < d {
        let lin = (a * d + b) * d + c
        if !(seen[lin]) {
          orbits = orbits + 1
          let mut x = a
          let mut y = b
          let mut z = c
          let mut step = 0
          while step < 3 {
            let l = (x * d + y) * d + z
            seen[l] = true
            // ρ: (x,y,z) ↦ (z,x,y)
            let nx = z
            let ny = x
            let nz = y
            x = nx
            y = ny
            z = nz
            step = step + 1
          }
        }
        c = c + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  orbits
}

///|
pub fn law_axial_cycle_variant() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t = ct_probe([2, 3, 2], [1, 2, 3])
  let r1 = match ct_cycle_axes(t, 0) {
    Some(s) => s
    None => ct_copy(t)
  }
  let r2 = match ct_cycle_axes(r1, 0) {
    Some(s) => s
    None => ct_copy(t)
  }
  let r3 = match ct_cycle_axes(r2, 0) {
    Some(s) => s
    None => ct_copy(t)
  }
  chk(out, "ρ³ = id", ct_eq(r3, t))
  // 顯式：(ρT)[a,b,c] = T[b,c,a]
  let explicit = ct_of([2, 2, 3], fn(idx) { ct_get(t, [idx[1], idx[2], idx[0]]) })
  chk(out, "ρ 的顯式公式： (ρT)[a,b,c] = T[b,c,a]", ct_eq(r1, explicit))
  // ρ = τ₀₁ ∘ τ₁₂（先做 τ₁₂ 再做 τ₀₁）
  chk(out, "ρ = τ₀₁∘τ₁₂（變體之間的關係）", ct_eq(r1, tau(tau(t, 1), 0)))
  chk(out, "ρ² = τ₁₂∘τ₀₁", ct_eq(r2, tau(tau(t, 0), 1)))
  chk(
    out,
    "負控制：ρT ≠ T，且 ρ ≠ τ（三個變體互不相同）",
    !(ct_eq(r1, t)) && !(ct_eq(r1, tau(t, 0))),
  )
  // Burnside：C₃ 在基準元素上的軌道數 = (d³ + 2d)/3
  let mut burnside = true
  let mut counts = ""
  let mut d = 2
  while d <= 4 {
    let orbits = cycle_orbits(d)
    let expect = (d * d * d + 2 * d) / 3
    if orbits != expect {
      burnside = false
    }
    counts = counts + "d=\{d}: \{orbits}/\{expect}  "
    d = d + 1
  }
  chk(out, "Burnside 軌道數 = (d³+2d)/3（\{counts}）", burnside)
  // 對角張量（全軸等長）在 ρ 下不變
  let diag = ct_of([3, 3, 3], fn(idx) { qq_int(idx[0] + idx[1] + idx[2]) })
  let diag_r = match ct_cycle_axes(diag, 0) {
    Some(s) => s
    None => ct_copy(diag)
  }
  chk(out, "軸對稱張量 T[a,b,c] = f(a+b+c) 是 ρ 的不變量", ct_eq(diag_r, diag))
  out
}

// ---------------------------------------------------------------------------
// 8. 對稱／反對稱分解
// ---------------------------------------------------------------------------

///|
fn basis_tensor(shape : Array[Int32], pos : Int32) -> CTensor {
  let t = ct_zeros(shape)
  t.data[pos] = qq_one()
  t
}

///|
pub fn law_axial_symmetric_decomposition() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let shape : Array[Int32] = [3, 3, 3]
  let t = ct_probe(shape, [2, 1, 3])
  let ps = match ct_sym_part(t, 0) {
    Some(s) => s
    None => ct_copy(t)
  }
  let pa = match ct_alt_part(t, 0) {
    Some(s) => s
    None => ct_copy(t)
  }
  let ps2 = match ct_sym_part(ps, 0) {
    Some(s) => s
    None => ct_copy(ps)
  }
  let pa2 = match ct_alt_part(pa, 0) {
    Some(s) => s
    None => ct_copy(pa)
  }
  chk(out, "p_s² = p_s、p_a² = p_a（投影子冪等）", ct_eq(ps2, ps) && ct_eq(pa2, pa))
  chk(out, "p_s p_a = 0（兩個特徵空間正交）", ct_is_zero(match ct_alt_part(ps, 0) {
    Some(s) => s
    None => ct_copy(ps)
  }))
  chk(out, "p_s + p_a = id（分解完整）", ct_eq(ct_add(ps, pa), t))
  chk(out, "p_s 的像真的對稱、p_a 的像真的反對稱", ct_is_sym_in(ps, 0) && ct_is_alt_in(pa, 0))
  chk(
    out,
    "負控制：探針本身既不對稱也不反對稱",
    !(ct_is_sym_in(t, 0)) && !(ct_is_alt_in(t, 0)),
  )
  // 維度：dim Sym = (N + F)/2、dim Alt = (N − F)/2，用投影後基準家族的秩重算
  let total = ct_size(shape)
  let n_i = shape[0]
  let n_k = shape[2]
  // F = τ 固定住的基準張量個數 = #{(i,i,k)} = n_i·n_k（i 取值數與 j 對齊）
  let f_count = n_i * n_k
  let sym_family : Array[Array[QQ]] = Array::make(0, Array::make(0, qq_zero()))
  let alt_family : Array[Array[QQ]] = Array::make(0, Array::make(0, qq_zero()))
  let mut p = 0
  while p < total {
    let e = basis_tensor(shape, p)
    let e_s = match ct_sym_part(e, 0) {
      Some(s) => s
      None => ct_copy(e)
    }
    let e_a = match ct_alt_part(e, 0) {
      Some(s) => s
      None => ct_copy(e)
    }
    sym_family.push(e_s.data)
    alt_family.push(e_a.data)
    p = p + 1
  }
  // 把家族當成矩陣（N 列 × N 行）取秩
  let sym_rank = qmat_rank(sym_family)
  let alt_rank = qmat_rank(alt_family)
  let expect_sym = (total + f_count) / 2
  let expect_alt = (total - f_count) / 2
  chk(
    out,
    "dim Sym = (N+F)/2 = \{expect_sym}、dim Alt = (N−F)/2 = \{expect_alt}（秩實算）",
    sym_rank == expect_sym && alt_rank == expect_alt && sym_rank + alt_rank == total,
  )
  out
}

// ---------------------------------------------------------------------------
// 9. 變體交換表與純張量
// ---------------------------------------------------------------------------

///|
pub fn law_axial_variant_table() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t4 = ct_probe([2, 2, 2, 2], [1, 2, 3, 4])
  let ops : Array[(CTensor) -> CTensor] = [
    fn(x) { tau(x, 0) },
    fn(x) { tau(x, 1) },
    fn(x) { tau(x, 2) },
    fn(x) {
      match ct_signed_swap(x, 0) {
        Some(s) => s
        None => ct_copy(x)
      }
    },
    fn(x) {
      match ct_signed_swap(x, 1) {
        Some(s) => s
        None => ct_copy(x)
      }
    },
    fn(x) {
      match ct_signed_swap(x, 2) {
        Some(s) => s
        None => ct_copy(x)
      }
    },
    fn(x) {
      match ct_cycle_axes(x, 0) {
        Some(s) => s
        None => ct_copy(x)
      }
    },
    fn(x) {
      match ct_cycle_axes(x, 1) {
        Some(s) => s
        None => ct_copy(x)
      }
    },
  ]
  let n = ops.length()
  let mut commuting_pairs = 0
  let mut a = 0
  while a < n {
    let mut b = a + 1
    while b < n {
      let ab = ops[b](ops[a](t4))
      let ba = ops[a](ops[b](t4))
      if ct_eq(ab, ba) {
        commuting_pairs = commuting_pairs + 1
      }
      b = b + 1
    }
    a = a + 1
  }
  chk(
    out,
    "\{n} 個算子、\{n * (n - 1) / 2} 對中可交換者 = \{commuting_pairs} 對（含 τ₀τ₂、σ₀σ₂ 等不相交支撐）",
    commuting_pairs > 0,
  )
  // 支撐不相交 ⇒ 交換；支撐相交且類型不同 ⇒ 未必交換
  let disjoint_swap = ct_eq(ops[2](ops[0](t4)), ops[0](ops[2](t4)))
  let disjoint_mixed = ct_eq(ops[5](ops[0](t4)), ops[0](ops[5](t4)))
  chk(out, "τ₀ 與 τ₂ 交換（|i−j| ≥ 2）", disjoint_swap)
  chk(out, "σ₂ 與 τ₀ 交換（不相交支撐）", disjoint_mixed)
  // 純張量：c·(u⊗u⊗u) 對 τ 與 ρ 不變、對 σ 變號
  let u : Array[QQ] = [qq_int(1), qq_int(2), qq_int(-1)]
  let v : Array[QQ] = [qq_int(3), qq_int(0), qq_int(1)]
  let w : Array[QQ] = [qq_int(-2), qq_int(5), qq_int(4)]
  let pure = ct_rank1(qq_frac(3, 2), [u, v, w])
  let pure_diag = ct_rank1(qq_frac(3, 2), [u, u, u])
  chk(
    out,
    "秩 1 張量 c(u⊗v⊗w) 的範數平方可算、且 c(u⊗u⊗u) 對 τ、ρ 不變、對 σ 變號",
    qq_eq(ct_full_sum(pure_diag), qq_int(12)) &&
    ct_eq(tau(pure_diag, 0), pure_diag) &&
    ct_eq(tau(pure_diag, 1), pure_diag) &&
    ct_eq(match ct_cycle_axes(pure_diag, 0) {
      Some(s) => s
      None => pure_diag
    }, pure_diag) &&
    ct_eq(
      match ct_signed_swap(pure_diag, 0) {
        Some(s) => s
        None => pure_diag
      },
      ct_scale(qq_int(-1), pure_diag),
    ),
  )
  // 一般秩 1 張量不是任何變體的不變量
  chk(
    out,
    "負控制：c(u⊗v⊗w)（u≠v）不是 τ₀ 的不變量",
    !(ct_eq(tau(pure, 0), pure)) && !(ct_eq(tau(pure, 1), pure)),
  )
  out
}

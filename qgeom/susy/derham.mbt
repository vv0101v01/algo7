// ---------------------------------------------------------------------------
// qgeom/susy/derham — 有限複形上的德朗姆型恆等（複形四元數幾何）
// ---------------------------------------------------------------------------
// 目標不是「∂² = 0 這句話」，而是它推出的三件事在具體複形上全部重算：
//
//   * `∂_{k−1}∂_k = 0`（精確零矩陣，不是浮點零）；
//   * Betti 數 `β_k = n_k − rank ∂_k − rank ∂_{k+1}` 與 Euler 特徵
//     `Σ(−1)^k n_k = Σ(−1)^k β_k` 兩條路徑對得上；
//   * Hodge 拉普拉斯 `Δ_k = ∂_kᵗ∂_k + ∂_{k+1}∂_{k+1}ᵗ` 的核維數等於 `β_k`，
//     而超電荷 `Q = D + Dᵗ`（`D = ⊕∂_k`）滿足 `Q² = ⊕Δ_k`——這是
//     「超對稱 × 德拉姆」在這裡的**唯一**內容，並不宣稱任何物理對偶。
//
// 係數環換成複形四元數 `H ⊗_R C` 之後，`∂² = 0` 與複結構 `J` 的交換性
// 仍然逐位元成立（`law_derham_complexified`）。

///|
/// 有限單純複形：`faces[k]` 是 `k` 維面的升序頂點表。
pub(all) struct SimplicialComplex {
  n_vertices : Int32
  faces : Array[Array[Array[Int32]]]
}

///|
fn face_cmp_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut i = 0
  while i < a.length() {
    if a[i] != b[i] {
      return false
    }
    i = i + 1
  }
  true
}

///|
fn face_in(list : Array[Array[Int32]], f : Array[Int32]) -> Bool {
  let mut i = 0
  while i < list.length() {
    if face_cmp_eq(list[i], f) {
      return true
    }
    i = i + 1
  }
  false
}

///|
fn face_index(list : Array[Array[Int32]], f : Array[Int32]) -> Int32 {
  let mut i = 0
  while i < list.length() {
    if face_cmp_eq(list[i], f) {
      return i
    }
    i = i + 1
  }
  -1
}

///|
/// 把一個面排序（升序）。
pub fn face_sorted(f : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = Array::make(f.length(), 0)
  let mut i = 0
  while i < f.length() {
    out[i] = f[i]
    i = i + 1
  }
  let mut a = 0
  while a < out.length() {
    let mut b = a + 1
    while b < out.length() {
      if out[b] < out[a] {
        let t = out[a]
        out[a] = out[b]
        out[b] = t
      }
      b = b + 1
    }
    a = a + 1
  }
  out
}

///|
/// 由「極大面」（通常是三角形）建出完整面格：所有子集都補齊、去重、排序。
pub fn sc_build(
  n_vertices : Int32,
  maximal : Array[Array[Int32]],
) -> SimplicialComplex {
  // 2 維面
  let f2 : Array[Array[Int32]] = []
  let mut i = 0
  while i < maximal.length() {
    let f = face_sorted(maximal[i])
    if !(face_in(f2, f)) {
      f2.push(f)
    }
    i = i + 1
  }
  // 1 維面
  let f1 : Array[Array[Int32]] = []
  i = 0
  while i < f2.length() {
    let f = f2[i]
    let mut drop = 0
    while drop < f.length() {
      let sub : Array[Int32] = []
      let mut k = 0
      while k < f.length() {
        if k != drop {
          sub.push(f[k])
        }
        k = k + 1
      }
      let s = face_sorted(sub)
      if !(face_in(f1, s)) {
        f1.push(s)
      }
      drop = drop + 1
    }
    i = i + 1
  }
  // 0 維面
  let f0 : Array[Array[Int32]] = []
  i = 0
  while i < f1.length() {
    let e = f1[i]
    let mut k = 0
    while k < e.length() {
      let v : Array[Int32] = [e[k]]
      if !(face_in(f0, v)) {
        f0.push(v)
      }
      k = k + 1
    }
    i = i + 1
  }
  SimplicialComplex::{
    n_vertices: n_vertices,
    faces: [f0, f1, f2],
  }
}

///|
/// `k` 維面的個數。
pub fn sc_count(cx : SimplicialComplex, k : Int32) -> Int32 {
  if k < 0 || k >= cx.faces.length() {
    0
  } else {
    cx.faces[k].length()
  }
}

///|
/// 邊界算子 `∂_k : C_k → C_{k−1}`（`n_{k−1} × n_k`）。
/// `k = 0` 時是 `1 × n_0` 的零矩陣（增廣鏈複形的 `C_{−1} = Q`）。
pub fn sc_boundary(cx : SimplicialComplex, k : Int32) -> Array[Array[@core.QQ]] {
  if k == 0 {
    return @core.qmat_zero(1, sc_count(cx, 0))
  }
  let rows = sc_count(cx, k - 1)
  let cols = sc_count(cx, k)
  let out = @core.qmat_zero(rows, cols)
  let mut j = 0
  while j < cols {
    let f = cx.faces[k][j]
    let mut drop = 0
    while drop < f.length() {
      let sub : Array[Int32] = []
      let mut t = 0
      while t < f.length() {
        if t != drop {
          sub.push(f[t])
        }
        t = t + 1
      }
      let idx = face_index(cx.faces[k - 1], face_sorted(sub))
      if idx >= 0 {
        let sign = if drop % 2 == 0 { 1 } else { -1 }
        out[idx][j] = @core.qq_int(sign)
      }
      drop = drop + 1
    }
    j = j + 1
  }
  out
}

///|
/// `∂_{k−1} · ∂_k`（應該恆為零矩陣）。
pub fn sc_dd(cx : SimplicialComplex, k : Int32) -> Array[Array[@core.QQ]] {
  if k <= 0 {
    return @core.qmat_zero(1, sc_count(cx, 0))
  }
  let dk = sc_boundary(cx, k)
  let dprev = sc_boundary(cx, k - 1)
  @core.qmat_mul_unchecked(dprev, dk)
}

///|
/// Betti 數 `β_k = n_k − rank ∂_k − rank ∂_{k+1}`（`k = 0, 1, 2`）。
pub fn sc_betti(cx : SimplicialComplex) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut k = 0
  while k <= 2 {
    let nk = sc_count(cx, k)
    let rk = @core.qmat_rank(sc_boundary(cx, k))
    let nk1 = sc_count(cx, k + 1)
    let rk1 = if nk1 > 0 {
      @core.qmat_rank(sc_boundary(cx, k + 1))
    } else {
      0
    }
    out.push(nk - rk - rk1)
    k = k + 1
  }
  out
}

///|
/// 由面數算 Euler 特徵 `Σ(−1)^k n_k`。
pub fn sc_euler_counts(cx : SimplicialComplex) -> Int32 {
  sc_count(cx, 0) - sc_count(cx, 1) + sc_count(cx, 2)
}

///|
/// 由 Betti 數算 Euler 特徵 `Σ(−1)^k β_k`。
pub fn sc_euler_betti(cx : SimplicialComplex) -> Int32 {
  let b = sc_betti(cx)
  b[0] - b[1] + b[2]
}

///|
/// 總鏈群上的邊界算子 `D = ⊕_{k≥1} ∂_k`（`∂_0` 以零塊代替）。
pub fn sc_d_total(cx : SimplicialComplex) -> Array[Array[@core.QQ]] {
  let n0 = sc_count(cx, 0)
  let n1 = sc_count(cx, 1)
  let n2 = sc_count(cx, 2)
  let total = n0 + n1 + n2
  let d = @core.qmat_zero(total, total)
  // C_1 → C_0
  let d1 = sc_boundary(cx, 1)
  let mut i = 0
  while i < n0 {
    let mut j = 0
    while j < n1 {
      d[i][n0 + j] = d1[i][j]
      j = j + 1
    }
    i = i + 1
  }
  // C_2 → C_1
  let d2 = sc_boundary(cx, 2)
  i = 0
  while i < n1 {
    let mut j = 0
    while j < n2 {
      d[n0 + i][n0 + n1 + j] = d2[i][j]
      j = j + 1
    }
    i = i + 1
  }
  d
}

///|
/// Hodge 拉普拉斯 `Δ_k = ∂_kᵗ∂_k + ∂_{k+1}∂_{k+1}ᵗ`（`n_k × n_k`）。
pub fn sc_hodge(cx : SimplicialComplex, k : Int32) -> Array[Array[@core.QQ]] {
  let nk = sc_count(cx, k)
  let dk = sc_boundary(cx, k)
  let dkt = @core.qmat_transpose(dk)
  let left = @core.qmat_mul_unchecked(dkt, dk)
  let nk1 = sc_count(cx, k + 1)
  let right = if nk1 > 0 {
    let dk1 = sc_boundary(cx, k + 1)
    let dk1t = @core.qmat_transpose(dk1)
    @core.qmat_mul_unchecked(dk1, dk1t)
  } else {
    @core.qmat_zero(nk, nk)
  }
  @core.qmat_add(left, right)
}

///|
/// 超電荷 `Q = D + Dᵗ`。
pub fn sc_supercharge(cx : SimplicialComplex) -> Array[Array[@core.QQ]] {
  let d = sc_d_total(cx)
  let dt = @core.qmat_transpose(d)
  @core.qmat_add(d, dt)
}

///|
/// 總 Hodge 拉普拉斯 `⊕_k Δ_k`（作為同一個矩陣）。
pub fn sc_hodge_total(cx : SimplicialComplex) -> Array[Array[@core.QQ]] {
  let n0 = sc_count(cx, 0)
  let n1 = sc_count(cx, 1)
  let n2 = sc_count(cx, 2)
  let total = n0 + n1 + n2
  let out = @core.qmat_zero(total, total)
  let offsets : Array[Int32] = [0, n0, n0 + n1]
  let mut k = 0
  while k <= 2 {
    let h = sc_hodge(cx, k)
    let off = offsets[k]
    let mut i = 0
    while i < sc_count(cx, k) {
      let mut j = 0
      while j < sc_count(cx, k) {
        out[off + i][off + j] = h[i][j]
        j = j + 1
      }
      i = i + 1
    }
    k = k + 1
  }
  out
}

// ---------------------------------------------------------------------------
// 複形四元數係數：H ⊗_R C 上的鏈複形
// ---------------------------------------------------------------------------

///|
/// 把 QQ 矩陣嵌入 CQuat（純實部）。
pub fn cm_from_qq(
  m : Array[Array[@core.QQ]],
) -> Array[Array[CQuat]] {
  let out : Array[Array[CQuat]] = Array::make(
    @core.qmat_rows(m),
    Array::make(0, cq_zero()),
  )
  let mut i = 0
  while i < @core.qmat_rows(m) {
    let row : Array[CQuat] = Array::make(@core.qmat_cols(m), cq_zero())
    let mut j = 0
    while j < @core.qmat_cols(m) {
      row[j] = cq_from_quat(@core.quat_of_qq(m[i][j]))
      j = j + 1
    }
    out[i] = row
    i = i + 1
  }
  out
}

///|
/// CQuat 矩陣乘法（維度需相符）。
pub fn cm_mul(a : Array[Array[CQuat]], b : Array[Array[CQuat]]) -> Array[Array[CQuat]] {
  let r = a.length()
  let c = if b.length() > 0 { b[0].length() } else { 0 }
  let out : Array[Array[CQuat]] = Array::make(r, Array::make(0, cq_zero()))
  let mut i = 0
  while i < r {
    let row : Array[CQuat] = Array::make(c, cq_zero())
    let mut j = 0
    while j < c {
      let mut acc = cq_zero()
      let mut k = 0
      while k < a[i].length() {
        acc = cq_add(acc, cq_mul(a[i][k], b[k][j]))
        k = k + 1
      }
      row[j] = acc
      j = j + 1
    }
    out[i] = row
    i = i + 1
  }
  out
}

///|
/// CQuat 矩陣作用在 CQuat 向量上。
pub fn cm_apply(
  m : Array[Array[CQuat]],
  v : Array[CQuat],
) -> Array[CQuat] {
  let out : Array[CQuat] = Array::make(m.length(), cq_zero())
  let mut i = 0
  while i < m.length() {
    let mut acc = cq_zero()
    let mut j = 0
    while j < m[i].length() {
      acc = cq_add(acc, cq_mul(m[i][j], v[j]))
      j = j + 1
    }
    out[i] = acc
    i = i + 1
  }
  out
}

///|
pub fn cm_is_zero(m : Array[Array[CQuat]]) -> Bool {
  let mut i = 0
  while i < m.length() {
    let mut j = 0
    while j < m[i].length() {
      if !(cq_eq(m[i][j], cq_zero())) {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
pub fn cm_transpose(
  m : Array[Array[CQuat]],
) -> Array[Array[CQuat]] {
  let r = m.length()
  let c = if r > 0 { m[0].length() } else { 0 }
  let out : Array[Array[CQuat]] = Array::make(c, Array::make(0, cq_zero()))
  let mut i = 0
  while i < c {
    let row : Array[CQuat] = Array::make(r, cq_zero())
    let mut j = 0
    while j < r {
      row[j] = m[j][i]
      j = j + 1
    }
    out[i] = row
    i = i + 1
  }
  out
}

///|
/// CQuat 版的 Hermitian 內積實部 `Σ Re(conj(x_i)·y_i)`。
pub fn cq_hdot(x : Array[CQuat], y : Array[CQuat]) -> @core.QQ {
  let mut acc = @core.qq_zero()
  let mut i = 0
  while i < x.length() {
    acc = @core.qq_add(acc, @core.quat_re(cq_mul(cq_conj(x[i]), y[i]).ca))
    i = i + 1
  }
  acc
}

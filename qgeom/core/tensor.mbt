// ---------------------------------------------------------------------------
// qgeom/core — 任意秩張量與「軸向交換」（axial exchange）變體
// ---------------------------------------------------------------------------
// 一個秩 r 的張量是 `shape : Array[Int32]` 加上一段 row-major 的 QQ 資料。
// 「軸向交換」是只動軸、不動值的重排：交換相鄰兩軸 τ_ax（τ² = 1）、
// 把它取負號的帶號變體 σ_ax = −τ_ax、以及三軸循環 ρ_ax（ρ³ = 1）。
//
// 三個變體不是三份複製的程式，而是同一個「軸置換算子」的三個元素：
//   * τ_ax  — 交換變體（Yang–Baxter 算子，`law_axial_exchange_yang_baxter`）
//   * σ_ax  — 帶號變體（σ² = 1 但值是反對稱，`law_axial_signed_variant`）
//   * ρ_ax  — 循環變體（ρ = τ_{ax+1}∘τ_ax 的乘積，`law_axial_cycle_variant`）
// 高維「合體運算」則由 `ct_contract_axis`（沿一軸收縮）＋軸向交換組合而成，
// 硬體抽象層在 `qgeom/hal` 用同一個型別做後端模擬。

///|
/// 秩 `r`、形狀 `shape` 的 QQ 張量。`data` 是 row-major 展平。
pub(all) struct CTensor {
  shape : Array[Int32]
  data : Array[QQ]
}

///|
/// 形狀的維度乘積（元素個數）。
pub fn ct_size(shape : Array[Int32]) -> Int32 {
  let mut s = 1
  let mut i = 0
  while i < shape.length() {
    s = s * shape[i]
    i = i + 1
  }
  s
}

///|
/// 秩（軸的個數）。
pub fn ct_rank(t : CTensor) -> Int32 {
  t.shape.length()
}

///|
/// 複製形狀（避免多個張量共用同一個可變 `Array`）。
pub fn ct_shape_copy(shape : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = Array::make(shape.length(), 0)
  let mut i = 0
  while i < shape.length() {
    out[i] = shape[i]
    i = i + 1
  }
  out
}

///|
/// row-major 步長。
pub fn ct_strides(shape : Array[Int32]) -> Array[Int32] {
  let r = shape.length()
  let out : Array[Int32] = Array::make(r, 1)
  let mut i = r - 1
  while i > 0 {
    out[i - 1] = out[i] * shape[i]
    i = i - 1
  }
  out
}

///|
/// 由多維索引算線性位置。
pub fn ct_lin(t : CTensor, idx : Array[Int32]) -> Int32 {
  let strides = ct_strides(t.shape)
  let mut lin = 0
  let mut a = 0
  while a < idx.length() {
    lin = lin + idx[a] * strides[a]
    a = a + 1
  }
  lin
}

///|
pub fn ct_zeros(shape : Array[Int32]) -> CTensor {
  let n = ct_size(shape)
  let data : Array[QQ] = Array::make(n, qq_zero())
  let mut i = 0
  while i < n {
    data[i] = qq_zero()
    i = i + 1
  }
  CTensor::{ shape: ct_shape_copy(shape), data: data }
}

///|
pub fn ct_get(t : CTensor, idx : Array[Int32]) -> QQ {
  t.data[ct_lin(t, idx)]
}

///|
/// 用「索引 ↦ 值」的函式造張量。
pub fn ct_of(shape : Array[Int32], f : (Array[Int32]) -> QQ) -> CTensor {
  let t = ct_zeros(shape)
  let idxs = ct_all_indices(shape)
  let mut i = 0
  while i < idxs.length() {
    t.data[i] = f(idxs[i])
    i = i + 1
  }
  t
}

///|
/// 形狀的所有索引（row-major 順序）。
pub fn ct_all_indices(shape : Array[Int32]) -> Array[Array[Int32]] {
  let total = ct_size(shape)
  let r = shape.length()
  let strides = ct_strides(shape)
  let out : Array[Array[Int32]] = Array::make(total, Array::make(0, 0))
  let mut lin = 0
  while lin < total {
    let idx : Array[Int32] = Array::make(r, 0)
    let mut a = 0
    while a < r {
      idx[a] = (lin / strides[a]) % shape[a]
      a = a + 1
    }
    out[lin] = idx
    lin = lin + 1
  }
  out
}

///|
pub fn ct_copy(t : CTensor) -> CTensor {
  let data : Array[QQ] = Array::make(t.data.length(), qq_zero())
  let mut i = 0
  while i < t.data.length() {
    data[i] = t.data[i]
    i = i + 1
  }
  CTensor::{ shape: ct_shape_copy(t.shape), data: data }
}

///|
pub fn ct_eq(a : CTensor, b : CTensor) -> Bool {
  if a.shape.length() != b.shape.length() {
    return false
  }
  let mut i = 0
  while i < a.shape.length() {
    if a.shape[i] != b.shape[i] {
      return false
    }
    i = i + 1
  }
  qq_list_eq(a.data, b.data)
}

///|
pub fn ct_add(a : CTensor, b : CTensor) -> CTensor {
  let out = ct_zeros(a.shape)
  let mut i = 0
  while i < a.data.length() {
    out.data[i] = qq_add(a.data[i], b.data[i])
    i = i + 1
  }
  out
}

///|
pub fn ct_sub(a : CTensor, b : CTensor) -> CTensor {
  let out = ct_zeros(a.shape)
  let mut i = 0
  while i < a.data.length() {
    out.data[i] = qq_sub(a.data[i], b.data[i])
    i = i + 1
  }
  out
}

///|
pub fn ct_scale(s : QQ, a : CTensor) -> CTensor {
  let out = ct_zeros(a.shape)
  let mut i = 0
  while i < a.data.length() {
    out.data[i] = qq_mul(s, a.data[i])
    i = i + 1
  }
  out
}

///|
pub fn ct_is_zero(a : CTensor) -> Bool {
  let mut i = 0
  while i < a.data.length() {
    if !(qq_is_zero(a.data[i])) {
      return false
    }
    i = i + 1
  }
  true
}

// ---------------------------------------------------------------------------
// 軸置換算子（三個變體共用同一個引擎）
// ---------------------------------------------------------------------------

///|
/// 一般軸置換：`perm[新軸] = 舊軸`。`perm` 必須是 `0..<r` 的排列，否則 `None`。
pub fn ct_permute(t : CTensor, perm : Array[Int32]) -> CTensor? {
  let r = ct_rank(t)
  if perm.length() != r {
    return None
  }
  let seen : Array[Bool] = Array::make(r, false)
  let mut ok = true
  let mut a = 0
  while a < r {
    let p = perm[a]
    if p < 0 || p >= r || seen[p] {
      ok = false
    } else {
      seen[p] = true
    }
    a = a + 1
  }
  if !(ok) {
    return None
  }
  let new_shape : Array[Int32] = Array::make(r, 0)
  let mut b = 0
  while b < r {
    new_shape[b] = t.shape[perm[b]]
    b = b + 1
  }
  let out = ct_zeros(new_shape)
  let idxs = ct_all_indices(new_shape)
  let mut i = 0
  while i < idxs.length() {
    let idx = idxs[i]
    let old_idx : Array[Int32] = Array::make(r, 0)
    let mut a2 = 0
    while a2 < r {
      old_idx[perm[a2]] = idx[a2]
      a2 = a2 + 1
    }
    out.data[i] = t.data[ct_lin(t, old_idx)]
    i = i + 1
  }
  Some(out)
}

///|
/// 交換相鄰兩軸 `ax` 與 `ax+1`（交換變體 τ）。
pub fn ct_swap_axes(t : CTensor, ax : Int32) -> CTensor? {
  let r = ct_rank(t)
  if ax < 0 || ax + 1 >= r {
    return None
  }
  let perm : Array[Int32] = Array::make(r, 0)
  let mut i = 0
  while i < r {
    perm[i] = i
    i = i + 1
  }
  perm[ax] = ax + 1
  perm[ax + 1] = ax
  ct_permute(t, perm)
}

///|
/// 三軸循環 `ρ`：`(ρT)[… a, b, c …] = T[… b, c, a …]`（循環變體，左移一位）。
/// 它與交換變體的關係是 `ρ = τ₀₁∘τ₁₂`（先做右邊的 τ₁₂）。
pub fn ct_cycle_axes(t : CTensor, ax : Int32) -> CTensor? {
  let r = ct_rank(t)
  if ax < 0 || ax + 2 >= r {
    return None
  }
  let perm : Array[Int32] = Array::make(r, 0)
  let mut i = 0
  while i < r {
    perm[i] = i
    i = i + 1
  }
  perm[ax] = ax + 2
  perm[ax + 1] = ax
  perm[ax + 2] = ax + 1
  ct_permute(t, perm)
}

///|
/// 帶號交換變體 σ = −（交換）：交換軸並整張取負。
pub fn ct_signed_swap(t : CTensor, ax : Int32) -> CTensor? {
  match ct_swap_axes(t, ax) {
    None => None
    Some(s) => Some(ct_scale(qq_int(-1), s))
  }
}

///|
/// 對稱部分 `(T + τT)/2`（交換軸的 +1 特徵空間投影）。
pub fn ct_sym_part(t : CTensor, ax : Int32) -> CTensor? {
  match ct_swap_axes(t, ax) {
    None => None
    Some(s) => Some(ct_scale(qq_half(), ct_add(t, s)))
  }
}

///|
/// 反對稱部分 `(T − τT)/2`（−1 特徵空間投影）。
pub fn ct_alt_part(t : CTensor, ax : Int32) -> CTensor? {
  match ct_swap_axes(t, ax) {
    None => None
    Some(s) => Some(ct_scale(qq_half(), ct_sub(t, s)))
  }
}

///|
/// 三個「軸向交換張量變體」。
pub(all) enum AxialVariant {
  /// 交換變體 τ（Yang–Baxter 算子）
  AxialSwap
  /// 帶號變體 σ = −τ
  AxialSigned
  /// 循環變體 ρ（三軸循環，ρ³ = 1）
  AxialCycle
}

///|
/// 把變體套用在某個軸位置上。
pub fn axial_apply(v : AxialVariant, t : CTensor, ax : Int32) -> CTensor? {
  match v {
    AxialSwap => ct_swap_axes(t, ax)
    AxialSigned => ct_signed_swap(t, ax)
    AxialCycle => ct_cycle_axes(t, ax)
  }
}

///|
/// 沿一軸收縮（對該軸求和，秩 −1）。
pub fn ct_contract_axis(t : CTensor, ax : Int32) -> CTensor? {
  let r = ct_rank(t)
  if ax < 0 || ax >= r {
    return None
  }
  let new_shape : Array[Int32] = Array::make(r - 1, 0)
  let mut a = 0
  let mut b = 0
  while a < r {
    if a != ax {
      new_shape[b] = t.shape[a]
      b = b + 1
    }
    a = a + 1
  }
  let out = ct_zeros(new_shape)
  let idxs = ct_all_indices(t.shape)
  let mut i = 0
  while i < idxs.length() {
    let idx = idxs[i]
    let red : Array[Int32] = Array::make(r - 1, 0)
    let mut a2 = 0
    let mut b2 = 0
    while a2 < r {
      if a2 != ax {
        red[b2] = idx[a2]
        b2 = b2 + 1
      }
      a2 = a2 + 1
    }
    let lin = ct_lin(out, red)
    out.data[lin] = qq_add(out.data[lin], t.data[i])
    i = i + 1
  }
  Some(out)
}

///|
/// 全收縮：所有軸求和成一個純量（秩 0 的張量就是 QQ）。
pub fn ct_full_sum(t : CTensor) -> QQ {
  let mut acc = qq_zero()
  let mut i = 0
  while i < t.data.length() {
    acc = qq_add(acc, t.data[i])
    i = i + 1
  }
  acc
}

///|
/// 這一對相鄰軸是否對稱（`τT = T`）。
pub fn ct_is_sym_in(t : CTensor, ax : Int32) -> Bool {
  match ct_swap_axes(t, ax) {
    None => false
    Some(s) => ct_eq(t, s)
  }
}

///|
/// 這一對相鄰軸是否反對稱（`τT = −T`）。
pub fn ct_is_alt_in(t : CTensor, ax : Int32) -> Bool {
  match ct_swap_axes(t, ax) {
    None => false
    Some(s) => ct_eq(ct_scale(qq_int(-1), t), s)
  }
}

///|
/// 純秩 1 張量 `c · (u ⊗ v ⊗ w)`（秩 3）與其推廣的建構子：給每個軸一個向量。
pub fn ct_rank1(c : QQ, cols : Array[Array[QQ]]) -> CTensor {
  let shape : Array[Int32] = Array::make(cols.length(), 0)
  let mut a = 0
  while a < cols.length() {
    shape[a] = cols[a].length()
    a = a + 1
  }
  ct_of(shape, fn(idx) {
    let mut acc = c
    let mut k = 0
    while k < idx.length() {
      acc = qq_mul(acc, cols[k][idx[k]])
      k = k + 1
    }
    acc
  })
}

///|
/// 固定模式的測試張量：`T[idx] = Σ_a w_a · idx[a] + idx[0]·idx[1] − idx[last−1]·idx[last] + rank²`。
/// 它既不對稱、也不反對稱、對任何軸都不是不變量——正好用來證明「變體真的有做事」，
/// 而不是在一張對稱張量上空轉。
pub fn ct_probe(shape : Array[Int32], w : Array[Int32]) -> CTensor {
  let r = shape.length()
  ct_of(shape, fn(idx) {
    let mut acc = qq_int(r * r)
    let mut a = 0
    while a < idx.length() {
      acc = qq_add(acc, qq_int(w[a] * idx[a]))
      a = a + 1
    }
    if r >= 2 {
      acc = qq_add(acc, qq_int(idx[0] * idx[1]))
      acc = qq_sub(acc, qq_int(idx[r - 2] * idx[r - 1]))
    }
    acc
  })
}

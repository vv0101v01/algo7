// ---------------------------------------------------------------------------
// qprob/fock/full_fock.mbt — 全量子福克空間與 q-變形子空間投影分解
// ---------------------------------------------------------------------------
// 數學結構演變（第三階）：
//   在第二階的 Favard 重構中，我們發現高斯矩產生 `β_k = k`（玻色子），而自由半圓矩將產生 `β_k = 1`！
//   為了在單一希爾伯特結構內統一古典、費米與自由非交換激發，我們構造单粒子空間 `ℋ`（維度 `d`）上的
//   **全量子福克空間（Full / Boltzmann Fock Space）**：
//     `ℱ_full(ℋ) = ⨁_{n ≥ 0} ℋ^{⊗ n}`，真空態 `Ω = 1 ∈ ℋ^{⊗ 0}`。
//   對任意變形參數 `q ∈ [-1, 1] ∩ ℚ`，在 `ℋ^{⊗ n}` 上定義 Bożejko–Speicher `q`-內積核：
//     `⟨e_{i_1} ⊗ ... ⊗ e_{i_n} | P^{(n)}_q | e_{j_1} ⊗ ... ⊗ e_{j_n}⟩`
//     `= Σ_{π ∈ S_n} q^{inv(π)} ∏_{r=1}^n ⟨e_{i_r}, e_{j_{π(r)}}⟩`
//   由此自然分裂出三大典範量子子空間與算子代數：
//     1. `q = 0`（全福克空間 `ℱ_0`）：`P^{(n)}_0 = I`，左創生 `ℓ*(f)` 與左湮滅 `ℓ(g)` 滿足
//        **Cuntz–Toeplitz 關係** `ℓ(g) ℓ*(f) = ⟨g, f⟩ I`（無 `n!` 因子，天然有界！）；
//     2. `q = +1`（對稱／玻色福克子空間 `ℱ_+ = Sym(ℋ)`）：維度 `C(d + n - 1, n)`，滿足 CCR；
//     3. `q = -1`（反對稱／費米福克子空間 `ℱ_- = Λ(ℋ)`）：維度 `C(d, n)`（`n > d` 時 Pauli 不相容恆為 0），滿足 CAR；
//     4. `-1 < q < 1`（Bożejko–Speicher `q`-福克空間）：`P^{(n)}_q` 嚴格正定（滿秩 `d^n`），且行列式滿足
//        Zagier 閉形式，插值連接費米、自由與玻色量子統計！
//   同時實作二次量子化函子 `Γ(T) = ⨁ T^{⊗ n}` 與微商二次量子化 `dΓ(H)`！

///|
/// 單粒子標準正交基底 `{e_0, ..., e_{d-1}}` 上的全福克字（長度 `n` 的詞表示 `e_{w_0} ⊗ ... ⊗ e_{w_{n-1}}`，空陣列為真空 `Ω`）。
pub(all) struct FockWord {
  letters : Array[Int32]
}

///|
/// 全福克空間有限線性組合（代數福克核 `ℱ_alg(ℋ)`，正是第二階無界算子的共同不變稠密核 `𝒟`！）。
pub(all) struct FullFockVec {
  single_dim : Int32
  terms : Array[(FockWord, @asymptotic.QVal)]
}

///|
pub fn word_eq(a : FockWord, b : FockWord) -> Bool {
  if a.letters.length() != b.letters.length() {
    return false
  }
  for i in 0..<a.letters.length() {
    if a.letters[i] != b.letters[i] {
      return false
    }
  }
  true
}

///|
/// 正規化全福克態：合併相同基底詞的係數並剃除零項。
pub fn fock_normalize(
  single_dim : Int32,
  raw : Array[(FockWord, @asymptotic.QVal)],
) -> FullFockVec {
  let merged : Array[(FockWord, @asymptotic.QVal)] = []
  for pair in raw {
    let (w, c) = pair
    if !@asymptotic.qv_is_zero(c) {
      let mut found = false
      for idx in 0..<merged.length() {
        if word_eq(merged[idx].0, w) {
          let nc = @asymptotic.qv_add(merged[idx].1, c)
          merged[idx] = (w, nc)
          found = true
          break
        }
      }
      if !found {
        merged.push((w, c))
      }
    }
  }
  let clean : Array[(FockWord, @asymptotic.QVal)] = []
  for pair in merged {
    if !@asymptotic.qv_is_zero(pair.1) {
      clean.push(pair)
    }
  }
  FullFockVec::{ single_dim, terms: clean, }
}

///|
/// 真空態 `|Ω⟩ ∈ ℋ^{⊗ 0}`。
pub fn fock_vacuum(single_dim : Int32) -> FullFockVec {
  FullFockVec::{
    single_dim,
    terms: [(FockWord::{ letters: [], }, @asymptotic.qv_one())],
  }
}

///|
pub fn fock_zero(single_dim : Int32) -> FullFockVec {
  FullFockVec::{ single_dim, terms: [], }
}

///|
pub fn fock_add(u : FullFockVec, v : FullFockVec) -> FullFockVec {
  guard u.single_dim == v.single_dim else {
    abort("fock_add: single_dim mismatch")
  }
  let raw : Array[(FockWord, @asymptotic.QVal)] = []
  for p in u.terms {
    raw.push(p)
  }
  for p in v.terms {
    raw.push(p)
  }
  fock_normalize(u.single_dim, raw)
}

///|
pub fn fock_sub(u : FullFockVec, v : FullFockVec) -> FullFockVec {
  guard u.single_dim == v.single_dim else {
    abort("fock_sub: single_dim mismatch")
  }
  fock_add(u, fock_scale(@asymptotic.qv_int(-1), v))
}

///|
pub fn fock_scale(c : @asymptotic.QVal, u : FullFockVec) -> FullFockVec {
  if @asymptotic.qv_is_zero(c) {
    return fock_zero(u.single_dim)
  }
  FullFockVec::{
    single_dim: u.single_dim,
    terms: [
      for p in u.terms => (p.0, @asymptotic.qv_mul(c, p.1))
    ],
  }
}

///|
pub fn fock_eq(u : FullFockVec, v : FullFockVec) -> Bool {
  fock_sub(u, v).terms.length() == 0
}

// ---------------------------------------------------------------------------
// 全福克空間與 q-變形創生／湮滅算子：
//   ℓ*_q(e_i) |e_{j_1} ... e_{j_n}⟩ = |e_i e_{j_1} ... e_{j_n}⟩
//   ℓ_q(e_i)  |Ω⟩ = 0
//   ℓ_q(e_i)  |e_{j_0} ... e_{j_{n-1}}⟩ = Σ_{r=0}^{n-1} q^r δ_{i, j_r} |e_{j_0} ... ê_{j_r} ... e_{j_{n-1}}⟩
// 滿足 q-對易關係：ℓ_q(e_i) ℓ*_q(e_j) − q ℓ*_q(e_j) ℓ_q(e_i) = δ_{ij} I ！
// ---------------------------------------------------------------------------

///|
/// 左創生算子 `ℓ*(f)`：對單粒子向量 `f ∈ ℚ^d` 在最左側張量乘入 `f`。
pub fn fock_create_left(
  f : Array[@asymptotic.QVal],
  state : FullFockVec,
) -> FullFockVec {
  guard f.length() == state.single_dim else {
    abort("fock_create_left: vector dimension mismatch")
  }
  let raw : Array[(FockWord, @asymptotic.QVal)] = []
  for i in 0..<f.length() {
    if !@asymptotic.qv_is_zero(f[i]) {
      for pair in state.terms {
        let (w, c) = pair
        let nw : Array[Int32] = [i]
        for l in w.letters {
          nw.push(l)
        }
        raw.push((FockWord::{ letters: nw, }, @asymptotic.qv_mul(f[i], c)))
      }
    }
  }
  fock_normalize(state.single_dim, raw)
}

///|
/// `q`-變形左湮滅算子 `ℓ_q(g)`：
///   - `q = 0`：自由左湮滅（只消去最左側字母，Cuntz–Toeplitz 算子）；
///   - `q = 1`：玻色湮滅導子（滿足 Leibniz 律與 `[a(g), a*(f)] = ⟨g,f⟩ I`）；
///   - `q = -1`：費米超導子（帶 Koszul 交替符號 `(-1)^r`，滿足 `{c(g), c*(f)} = ⟨g,f⟩ I`）。
pub fn fock_annihilate_q(
  q : @asymptotic.QVal,
  g : Array[@asymptotic.QVal],
  state : FullFockVec,
) -> FullFockVec {
  guard g.length() == state.single_dim else {
    abort("fock_annihilate_q: vector dimension mismatch")
  }
  let raw : Array[(FockWord, @asymptotic.QVal)] = []
  let is_free = @asymptotic.qv_is_zero(q)
  for pair in state.terms {
    let (w, c) = pair
    let n = w.letters.length()
    if n > 0 {
      let max_r = if is_free { 1 } else { n }
      for r in 0..<max_r {
        let letter = w.letters[r]
        if letter >= 0 &&
          letter < g.length() &&
          !@asymptotic.qv_is_zero(g[letter]) {
          let q_r = @asymptotic.qv_pow(q, r)
          let coeff = @asymptotic.qv_mul(c, @asymptotic.qv_mul(g[letter], q_r))
          let rem : Array[Int32] = []
          for idx in 0..<n {
            if idx != r {
              rem.push(w.letters[idx])
            }
          }
          raw.push((FockWord::{ letters: rem, }, coeff))
        }
      }
    }
  }
  fock_normalize(state.single_dim, raw)
}

// ---------------------------------------------------------------------------
// Bożejko–Speicher 置換逆序數與 q-內積 ⟨u, v⟩_q（使 ℓ*_q(f) 精確成為 ℓ_q(f) 的伴隨！）
// ---------------------------------------------------------------------------

///|
/// 計算置換 `perm` 的逆序數 `inv(π) = #{ (a < b) | π(a) > π(b) }`。
pub fn perm_inversions(perm : Array[Int32]) -> Int32 {
  let mut inv = 0
  let n = perm.length()
  for i in 0..<n {
    for j in (i + 1)..<n {
      if perm[i] > perm[j] {
        inv = inv + 1
      }
    }
  }
  inv
}

///|
/// 產生 `0 .. n-1` 的全部 `n!` 個置換（`n ≤ 6`）。
pub fn symmetric_group_perms(n : Int32) -> Array[Array[Int32]] {
  if n <= 0 {
    return [[]]
  }
  let res : Array[Array[Int32]] = []
  let used = Array::make(n, false)
  let cur : Array[Int32] = []
  letrec backtrack = () => {
    if cur.length() == n {
      res.push([ for x in cur => x ])
      return
    }
    for v in 0..<n {
      if !used[v] {
        used[v] = true
        cur.push(v)
        backtrack()
        let _ = cur.pop()
        used[v] = false
      }
    }
  }
  backtrack()
  res
}

///|
/// 兩個同長度福克字在變形參數 `q` 下的 Bożejko–Speicher 內積：
/// `⟨w_1, w_2⟩_q = Σ_{π ∈ S_n} q^{inv(π)} ∏_{r=0}^{n-1} δ_{w_1[r], w_2[π(r)]}`。
pub fn word_inner_q(
  q : @asymptotic.QVal,
  w1 : FockWord,
  w2 : FockWord,
) -> @asymptotic.QVal {
  let n = w1.letters.length()
  if n != w2.letters.length() {
    return @asymptotic.qv_zero()
  }
  if n == 0 {
    return @asymptotic.qv_one()
  }
  if @asymptotic.qv_is_zero(q) {
    return if word_eq(w1, w2) {
      @asymptotic.qv_one()
    } else {
      @asymptotic.qv_zero()
    }
  }
  let perms = symmetric_group_perms(n)
  let mut acc = @asymptotic.qv_zero()
  for pi in perms {
    let mut match_all = true
    for r in 0..<n {
      if w1.letters[r] != w2.letters[pi[r]] {
        match_all = false
        break
      }
    }
    if match_all {
      acc = @asymptotic.qv_add(acc, @asymptotic.qv_pow(q, perm_inversions(pi)))
    }
  }
  acc
}

///|
/// 全福克空間上的 `q`-變形內積 `⟨u, v⟩_q`。
pub fn fock_inner_q(
  q : @asymptotic.QVal,
  u : FullFockVec,
  v : FullFockVec,
) -> @asymptotic.QVal {
  let mut sum = @asymptotic.qv_zero()
  for p1 in u.terms {
    for p2 in v.terms {
      if p1.0.letters.length() == p2.0.letters.length() {
        let wi = word_inner_q(q, p1.0, p2.0)
        if !@asymptotic.qv_is_zero(wi) {
          sum = @asymptotic.qv_add(
            sum,
            @asymptotic.qv_mul(@asymptotic.qv_mul(p1.1, p2.1), wi),
          )
        }
      }
    }
  }
  sum
}

///|
/// 列舉 `n` 粒子扇區 `ℋ^{⊗ n}` 的全部 `d^n` 個標準基底詞，並構造 `q`-Gram 內積核矩陣 `P^{(n)}_q`（大小 `d^n × d^n`）。
/// 其矩陣秩即為商希爾伯特空間 `ℱ_q^{(n)}(ℋ) = ℋ^{⊗ n} / ker P^{(n)}_q` 的精確維度！
pub fn fock_sector_words(single_dim : Int32, n : Int32) -> Array[FockWord] {
  if n <= 0 {
    return [FockWord::{ letters: [], }]
  }
  let out : Array[FockWord] = []
  let cur : Array[Int32] = []
  letrec gen = () => {
    if cur.length() == n {
      out.push(FockWord::{ letters: [ for x in cur => x ], })
      return
    }
    for a in 0..<single_dim {
      cur.push(a)
      gen()
      let _ = cur.pop()
    }
  }
  gen()
  out
}

///|
pub fn fock_q_gram_matrix(
  q : @asymptotic.QVal,
  single_dim : Int32,
  n : Int32,
) -> (Int32, Array[@asymptotic.QVal]) {
  let words = fock_sector_words(single_dim, n)
  let m = words.length()
  let mat = Array::make(m * m, @asymptotic.qv_zero())
  for i in 0..<m {
    for j in i..<m {
      let g = word_inner_q(q, words[i], words[j])
      mat[i * m + j] = g
      mat[j * m + i] = g
    }
  }
  (m, mat)
}

// ---------------------------------------------------------------------------
// 二次量子化函子 Γ(T) 與微分二次量子化 dΓ(H)
// ---------------------------------------------------------------------------

///|
/// 微商二次量子化 `dΓ(H)`：單粒子算子 `H`（`d × d` row-major）提升為多粒子加性觀測量
/// `dΓ(H) (u_1 ⊗ ... ⊗ u_n) = Σ_{r=0}^{n-1} u_1 ⊗ ... ⊗ (H u_r) ⊗ ... ⊗ u_n`；`dΓ(H)|Ω⟩ = 0`。
/// 特別地，`dΓ(I)` 即為總粒子數算子 `N`！
pub fn fock_dgamma(
  h_mat : Array[@asymptotic.QVal],
  d : Int32,
  state : FullFockVec,
) -> FullFockVec {
  let raw : Array[(FockWord, @asymptotic.QVal)] = []
  for pair in state.terms {
    let (w, coeff) = pair
    let n = w.letters.length()
    for pos in 0..<n {
      let col = w.letters[pos]
      for row in 0..<d {
        let h_rc = h_mat[row * d + col]
        if !@asymptotic.qv_is_zero(h_rc) {
          let nw = [
            for idx in 0..<n => if idx == pos { row } else { w.letters[idx] }
          ]
          raw.push(
            (FockWord::{ letters: nw, }, @asymptotic.qv_mul(coeff, h_rc)),
          )
        }
      }
    }
  }
  fock_normalize(d, raw)
}

///|
/// 乘法二次量子化 `Γ(T)`：將單粒子收縮／么正算子 `T`（`d × d`）提升為張量積態射
/// `Γ(T)(u_1 ⊗ ... ⊗ u_n) = (T u_1) ⊗ ... ⊗ (T u_n)`，且 `Γ(T)|Ω⟩ = |Ω⟩`。
pub fn fock_gamma(
  t_mat : Array[@asymptotic.QVal],
  d : Int32,
  state : FullFockVec,
) -> FullFockVec {
  let raw : Array[(FockWord, @asymptotic.QVal)] = []
  for pair in state.terms {
    let (w, coeff) = pair
    let n = w.letters.length()
    if n == 0 {
      raw.push((w, coeff))
    } else {
      let mut partial : Array[(Array[Int32], @asymptotic.QVal)] = [([], coeff)]
      for pos in 0..<n {
        let col = w.letters[pos]
        let next_p : Array[(Array[Int32], @asymptotic.QVal)] = []
        for item in partial {
          let (prefix, pc) = item
          for row in 0..<d {
            let t_rc = t_mat[row * d + col]
            if !@asymptotic.qv_is_zero(t_rc) {
              let np = [ for x in prefix => x ]
              np.push(row)
              next_p.push((np, @asymptotic.qv_mul(pc, t_rc)))
            }
          }
        }
        partial = next_p
      }
      for item in partial {
        raw.push((FockWord::{ letters: item.0, }, item.1))
      }
    }
  }
  fock_normalize(d, raw)
}

// ---------------------------------------------------------------------------
// qgeom/geom — 多項式映射的雅可比矩陣、張量積與「全射」性質
// ---------------------------------------------------------------------------
// 這一支要證的不是「雅可比是偏導數排成的矩陣」這句定義，而是兩件事：
//
//   1. 雅可比真的是函子：`J(g∘f)(x) = J_g(f(x)) · J_f(x)`（鏈鎖律，精確等式）；
//   2. 「全射」在張量積下被保存：`rank(A ⊗ B) = rank(A)·rank(B)`，因此
//      A、B 都行滿秩（全射）時 `A ⊗ B` 也行滿秩，且核的維數由
//      `(列數乘積) − rank(A)·rank(B)` 精確給出。
//
// 所有秩都是 QQ 上的精確秩（`@core.qmat_rank`），沒有浮點容差。

///|
/// `n` 變數的單項式係數表：每個項是（指數向量, 係數）。同一個指數可以重複，
/// 讀值時會相加，因此「相等」是函式層面的相等，不是字面相等。
pub(all) struct MPoly {
  nvars : Int32
  terms : Array[(Array[Int32], @core.QQ)]
}

///|
pub fn mpoly_const(nvars : Int32, c : @core.QQ) -> MPoly {
  let exps : Array[Int32] = Array::make(nvars, 0)
  MPoly::{ nvars: nvars, terms: [(exps, c)] }
}

///|
pub fn mpoly_var(nvars : Int32, k : Int32) -> MPoly {
  let exps : Array[Int32] = Array::make(nvars, 0)
  exps[k] = 1
  MPoly::{ nvars: nvars, terms: [(exps, @core.qq_one())] }
}

///|
pub fn mpoly_zero(nvars : Int32) -> MPoly {
  MPoly::{ nvars: nvars, terms: [] }
}

///|
pub fn mpoly_add(a : MPoly, b : MPoly) -> MPoly {
  let terms : Array[(Array[Int32], @core.QQ)] = []
  let mut i = 0
  while i < a.terms.length() {
    terms.push(a.terms[i])
    i = i + 1
  }
  let mut j = 0
  while j < b.terms.length() {
    terms.push(b.terms[j])
    j = j + 1
  }
  MPoly::{ nvars: a.nvars, terms: terms }
}

///|
pub fn mpoly_neg(a : MPoly) -> MPoly {
  let terms : Array[(Array[Int32], @core.QQ)] = []
  let mut i = 0
  while i < a.terms.length() {
    let (e, c) = a.terms[i]
    terms.push((e, @core.qq_neg(c)))
    i = i + 1
  }
  MPoly::{ nvars: a.nvars, terms: terms }
}

///|
pub fn mpoly_sub(a : MPoly, b : MPoly) -> MPoly {
  mpoly_add(a, mpoly_neg(b))
}

///|
pub fn mpoly_mul(a : MPoly, b : MPoly) -> MPoly {
  let terms : Array[(Array[Int32], @core.QQ)] = []
  let mut i = 0
  while i < a.terms.length() {
    let (ea, ca) = a.terms[i]
    let mut j = 0
    while j < b.terms.length() {
      let (eb, cb) = b.terms[j]
      let exps : Array[Int32] = Array::make(a.nvars, 0)
      let mut k = 0
      while k < a.nvars {
        exps[k] = ea[k] + eb[k]
        k = k + 1
      }
      terms.push((exps, @core.qq_mul(ca, cb)))
      j = j + 1
    }
    i = i + 1
  }
  MPoly::{ nvars: a.nvars, terms: terms }
}

///|
pub fn mpoly_scale(c : @core.QQ, a : MPoly) -> MPoly {
  let terms : Array[(Array[Int32], @core.QQ)] = []
  let mut i = 0
  while i < a.terms.length() {
    let (e, c0) = a.terms[i]
    terms.push((e, @core.qq_mul(c, c0)))
    i = i + 1
  }
  MPoly::{ nvars: a.nvars, terms: terms }
}

///|
/// 在點 `x` 上求值。
pub fn mpoly_eval(a : MPoly, x : Array[@core.QQ]) -> @core.QQ {
  let mut acc = @core.qq_zero()
  let mut i = 0
  while i < a.terms.length() {
    let (e, c) = a.terms[i]
    let mut term = c
    let mut k = 0
    while k < e.length() {
      let mut p = 0
      while p < e[k] {
        term = @core.qq_mul(term, x[k])
        p = p + 1
      }
      k = k + 1
    }
    acc = @core.qq_add(acc, term)
    i = i + 1
  }
  acc
}

///|
/// 對第 `k` 個變數的偏導數（多項式的形式微分，逐項做）。
pub fn mpoly_partial(a : MPoly, k : Int32) -> MPoly {
  let terms : Array[(Array[Int32], @core.QQ)] = []
  let mut i = 0
  while i < a.terms.length() {
    let (e, c) = a.terms[i]
    if e[k] > 0 {
      let new_exp : Array[Int32] = Array::make(e.length(), 0)
      let mut j = 0
      while j < e.length() {
        new_exp[j] = e[j]
        j = j + 1
      }
      new_exp[k] = e[k] - 1
      terms.push((new_exp, @core.qq_mul(c, @core.qq_int(e[k]))))
    }
    i = i + 1
  }
  MPoly::{ nvars: a.nvars, terms: terms }
}

///|
/// **同時**代換：`a(x_0, …, x_{n−1})` 中的每個變數 `x_j` 換成 `subs[j]`。
/// 必須同時做：先代換 `x_0` 再代換 `x_1` 會把先前代換進來的 `x_1` 再代換一次，
/// 這是多項式複合最常見的錯誤（本檔的舊版正是這樣，`law_jacobian_chain_rule`
/// 的代值核對把它抓出來）。
pub fn mpoly_substitute_all(a : MPoly, subs : Array[MPoly]) -> MPoly {
  let mut acc = mpoly_zero(a.nvars)
  let mut i = 0
  while i < a.terms.length() {
    let (e, c) = a.terms[i]
    let mut term = mpoly_const(a.nvars, c)
    let mut j = 0
    while j < a.nvars {
      let mut p = 0
      while p < e[j] {
        term = mpoly_mul(term, subs[j])
        p = p + 1
      }
      j = j + 1
    }
    acc = mpoly_add(acc, term)
    i = i + 1
  }
  acc
}

///|
/// 映射的雅可比矩陣 `J[i][j] = ∂f_i/∂x_j`，在點 `x` 上求值。
pub fn map_jacobian(maps : Array[MPoly], x : Array[@core.QQ]) -> Array[Array[@core.QQ]] {
  let m = maps.length()
  let n = x.length()
  let out = @core.qmat_zero(m, n)
  let mut i = 0
  while i < m {
    let mut j = 0
    while j < n {
      out[i][j] = mpoly_eval(mpoly_partial(maps[i], j), x)
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
/// 複合 `g ∘ f`（`f`、`g` 都是多項式映射，變數個數相同）。
pub fn map_compose(g : Array[MPoly], f : Array[MPoly]) -> Array[MPoly] {
  let out : Array[MPoly] = []
  let mut i = 0
  while i < g.length() {
    out.push(mpoly_substitute_all(g[i], f))
    i = i + 1
  }
  out
}

///|
/// 映射在點 `x` 上的值。
pub fn map_eval(maps : Array[MPoly], x : Array[@core.QQ]) -> Array[@core.QQ] {
  let out : Array[@core.QQ] = @core.qvec_zero(maps.length())
  let mut i = 0
  while i < maps.length() {
    out[i] = mpoly_eval(maps[i], x)
    i = i + 1
  }
  out
}

///|
/// Kronecker（張量）積 `A ⊗ B`：`(r_A·r_B) × (c_A·c_B)`。
pub fn mat_kronecker(
  a : Array[Array[@core.QQ]],
  b : Array[Array[@core.QQ]],
) -> Array[Array[@core.QQ]] {
  let ra = @core.qmat_rows(a)
  let ca = @core.qmat_cols(a)
  let rb = @core.qmat_rows(b)
  let cb = @core.qmat_cols(b)
  let out = @core.qmat_zero(ra * rb, ca * cb)
  let mut i = 0
  while i < ra {
    let mut j = 0
    while j < ca {
      let mul = a[i][j]
      let mut p = 0
      while p < rb {
        let mut q = 0
        while q < cb {
          out[i * rb + p][j * cb + q] = @core.qq_mul(mul, b[p][q])
          q = q + 1
        }
        p = p + 1
      }
      j = j + 1
    }
    i = i + 1
  }
  out
}

///|
/// 行滿秩 ⟺ 線性映射全射。
pub fn mat_is_surjective(a : Array[Array[@core.QQ]]) -> Bool {
  @core.qmat_rank(a) == @core.qmat_rows(a)
}

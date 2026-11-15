// ---------------------------------------------------------------------------
// qgeom/hal — 定律登記
// ---------------------------------------------------------------------------
// 硬體抽象層要證的三件事，沒有一件是「跑起來不崩」：
//   1. 每一步的語意與 `qgeom/core` 的算子一致（含交換＋收縮的合併恆等）；
//   2. 後端只是排程，換後端不改結果（同一條計畫 × 五個後端逐位元比較）；
//   3. 合併（fusion）是語意保存的改寫，且真的少掃記憶體；分塊與道確實覆蓋。

///|
pub fn hal_all_laws() -> Array[(String, Array[(String, Bool)])] {
  [
    ("單步語意與「交換＋收縮」合併恆等", law_hal_stage_semantics()),
    ("後端等價：排程不改變結果", law_hal_backend_equivalence()),
    ("合併代數、正規化與記憶體流量", law_hal_fusion_algebra()),
    ("分塊覆蓋與向量道計數", law_hal_tiling_partition()),
    ("決定性、純度與無別名", law_hal_determinism_and_purity()),
  ]
}

///|
fn hal_probe_tensors() -> Array[@core.CTensor] {
  [
    @core.ct_probe([2, 3, 2], [1, 2, 3]),
    @core.ct_probe([3, 2, 2], [2, 1, 4]),
    @core.ct_probe([2, 2, 2, 2], [1, 1, 2, 3]),
  ]
}

///|
fn q1() -> @core.QQ {
  @core.qq_frac(3, 2)
}

///|
fn q2() -> @core.QQ {
  @core.qq_int(-1)
}

///|
fn q3() -> @core.QQ {
  @core.qq_int(4)
}

///|
/// 有混合步的計畫（都用秩 3 的探針可執行）。
fn hal_plans() -> Array[Plan] {
  [
    plan_new([StScale(q1()), StAdd(q2()), StScale(q3())]),
    plan_new([StSwap(0), StScale(@core.qq_int(2)), StSwap(0)]),
    plan_new([StSwap(1), StContract(0)]),
    plan_new([StContract(2), StSwap(0)]),
    plan_new([StSwap(0), StSwap(1), StScale(@core.qq_half()), StAdd(@core.qq_int(3)), StContract(1)]),
    plan_new([StSwap(0), StSwap(0), StScale(@core.qq_one()), StAdd(@core.qq_zero())]),
  ]
}

///|
/// 後端全家桶：純量 + 4 個向量道 + 2 個分塊。
fn hal_backends() -> Array[&FusedBackend] {
  [
    ScalarCore::{ tag: 0 },
    LaneCore::{ lanes: 2 },
    LaneCore::{ lanes: 3 },
    LaneCore::{ lanes: 4 },
    BlockedCore::{ lanes: 2, block: 2 },
    BlockedCore::{ lanes: 4, block: 3 },
    BlockedCore::{ lanes: 3, block: 1 },
  ]
}

///|
fn hal_backends_typed() -> Array[(&FusedBackend, String)] {
  let raw = hal_backends()
  let out : Array[(&FusedBackend, String)] = []
  let mut i = 0
  while i < raw.length() {
    out.push((raw[i], raw[i].backend_label()))
    i = i + 1
  }
  out
}

// ---------------------------------------------------------------------------
// 1. 單步語意
// ---------------------------------------------------------------------------

///|
pub fn law_hal_stage_semantics() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t = @core.ct_probe([2, 3, 2], [1, 2, 3])
  let mut stage_ok = true
  let mut checked = 0
  // 逐個步驟與 core 的算子對照
  match @core.ct_swap_axes(t, 0) {
    None => stage_ok = false
    Some(reference) =>
      match hal_stage_apply(t, StSwap(0)) {
        None => stage_ok = false
        Some(actual) => if !(@core.ct_eq(reference, actual)) { stage_ok = false }
      }
  }
  checked = checked + 1
  if !(@core.ct_eq(@core.ct_scale(q1(), t), match hal_stage_apply(t, StScale(q1())) {
    Some(x) => x
    None => @core.ct_copy(t)
  })) {
    stage_ok = false
  }
  checked = checked + 1
  let add_ref = @core.ct_add(t, @core.ct_of(t.shape, fn(_i) { q2() }))
  if !(
    @core.ct_eq(add_ref, match hal_stage_apply(t, StAdd(q2())) {
      Some(x) => x
      None => @core.ct_copy(t)
    })
  ) {
    stage_ok = false
  }
  checked = checked + 1
  match @core.ct_contract_axis(t, 1) {
    None => stage_ok = false
    Some(reference) =>
      match hal_stage_apply(t, StContract(1)) {
        None => stage_ok = false
        Some(actual) => if !(@core.ct_eq(reference, actual)) { stage_ok = false }
      }
  }
  checked = checked + 1
  @core.chk(out, "\{checked} 個步驟與 qgeom/core 的算子逐位元一致", stage_ok)
  // 高維合體恆等：contract(τ₀₁T, 0) = contract(T, 1)
  let lhs = match hal_stage_apply(t, StSwap(0)) {
    Some(s) =>
      match hal_stage_apply(s, StContract(0)) {
        Some(c) => c
        None => @core.ct_copy(t)
      }
    None => @core.ct_copy(t)
  }
  let rhs = match hal_stage_apply(t, StContract(1)) {
    Some(c) => c
    None => @core.ct_copy(t)
  }
  @core.chk(
    out,
    "合體恆等：contract(τ₀₁T, 0) = contract(T, 1)（形狀 (\{rhs.shape[0]},\{rhs.shape[1]})）",
    @core.ct_eq(lhs, rhs),
  )
  // 全收縮在軸向交換下不變
  let sum_t = @core.ct_full_sum(t)
  let sum_swap = match hal_stage_apply(t, StSwap(0)) {
    Some(s) => @core.ct_full_sum(s)
    None => @core.qq_zero()
  }
  let sum_swap2 = match hal_stage_apply(t, StSwap(1)) {
    Some(s) => @core.ct_full_sum(s)
    None => @core.qq_zero()
  }
  @core.chk(out, "全收縮不變量：sum(τT) = sum(T)（值 \{@core.qq_show(sum_t)}）", @core.qq_eq(sum_t, sum_swap) && @core.qq_eq(sum_t, sum_swap2))
  let c = q1()
  let sum_scaled = match hal_stage_apply(t, StScale(c)) {
    Some(s) => @core.ct_full_sum(s)
    None => @core.qq_zero()
  }
  @core.chk(
    out,
    "全收縮對純量線性：sum(cT) = c·sum(T)，c = \{@core.qq_show(c)}",
    @core.qq_eq(sum_scaled, @core.qq_mul(c, sum_t)),
  )
  out
}

// ---------------------------------------------------------------------------
// 2. 後端等價
// ---------------------------------------------------------------------------

///|
pub fn law_hal_backend_equivalence() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let tensors = hal_probe_tensors()
  let plans = hal_plans()
  let backends = hal_backends()
  let mut agree = true
  let mut comparisons = 0
  let mut executed = 0
  let mut ti = 0
  while ti < tensors.length() {
    let t = tensors[ti]
    let mut pi = 0
    while pi < plans.length() {
      let p = plans[pi]
      // 只有秩 3 的探針能跑所有計畫；秩 4 的探針跳過收縮步以保持形狀可比
      let reference = hal_exec(p, t)
      match reference {
        None => ()
        Some(refv) => {
          executed = executed + 1
          let mut bi = 0
          while bi < backends.length() {
            let be = backends[bi]
            let got = hal_exec_backend(be, p, t)
            comparisons = comparisons + 1
            match got {
              None => agree = false
              Some(g) => if !(@core.ct_eq(g, refv)) { agree = false }
            }
            bi = bi + 1
          }
        }
      }
      pi = pi + 1
    }
    ti = ti + 1
  }
  @core.chk(
    out,
    "\{executed} 條可執行計畫 × 7 個後端 = \{comparisons} 次比較，結果全部相同",
    agree && comparisons > 0,
  )
  // 負控制：非法軸在參考實作與所有後端都回傳 None
  let bad = plan_new([StContract(9)])
  let bad2 = plan_new([StSwap(5)])
  let t0 = @core.ct_probe([2, 2], [1, 1])
  let mut all_none = hal_exec(bad, t0) is None && hal_exec(bad2, t0) is None
  let mut bi2 = 0
  while bi2 < backends.length() {
    let be = backends[bi2]
    if !(hal_exec_backend(be, bad, t0) is None && hal_exec_backend(be, bad2, t0) is None) {
      all_none = false
    }
    bi2 = bi2 + 1
  }
  @core.chk(out, "負控制：非法收縮／交換軸在所有後端都回傳 None", all_none)
  out
}

// ---------------------------------------------------------------------------
// 3. 合併代數、正規化、流量
// ---------------------------------------------------------------------------

///|
fn stages_eq(a : Array[Stage], b : Array[Stage]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  let mut i = 0
  while i < a.length() {
    let same = match (a[i], b[i]) {
      (StSwap(x), StSwap(y)) => x == y
      (StScale(x), StScale(y)) => @core.qq_eq(x, y)
      (StAdd(x), StAdd(y)) => @core.qq_eq(x, y)
      (StContract(x), StContract(y)) => x == y
      _ => false
    }
    if !(same) {
      return false
    }
    i = i + 1
  }
  true
}

///|
pub fn law_hal_fusion_algebra() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let plans = hal_plans()
  let t = @core.ct_probe([2, 3, 2], [1, 2, 3])
  let a = plans[0]
  let b = plans[2]
  let c = plans[4]
  @core.chk(
    out,
    "計畫連接的結合律： (p∘q)∘r = p∘(q∘r)",
    stages_eq(
      plan_concat(plan_concat(a, b), c).stages,
      plan_concat(a, plan_concat(b, c)).stages,
    ),
  )
  // exec(p∘q) = exec(q) ∘ exec(p)
  let mut compose_ok = true
  let lhs = hal_exec(plan_concat(a, b), t)
  let rhs = match hal_exec(a, t) {
    None => None
    Some(mid) => hal_exec(b, mid)
  }
  match (lhs, rhs) {
    (Some(x), Some(y)) => if !(@core.ct_eq(x, y)) { compose_ok = false }
    _ => compose_ok = false
  }
  @core.chk(out, "exec(p∘q) = exec(q)∘exec(p)（逐步與一次跑完等價）", compose_ok)
  // 正規化保存語意、冪等、不變長
  let mut simplify_ok = true
  let mut idem_ok = true
  let mut shorter = true
  let mut saved = 0
  let mut pi = 0
  while pi < plans.length() {
    let p = plans[pi]
    let s = plan_simplify(p)
    let s2 = plan_simplify(s)
    if !(stages_eq(s.stages, s2.stages)) {
      idem_ok = false
    }
    if s.stages.length() > p.stages.length() {
      shorter = false
    }
    saved = saved + (p.stages.length() - s.stages.length())
    match hal_exec(p, t) {
      None => ()
      Some(refv) =>
        match hal_exec(s, t) {
          None => simplify_ok = false
          Some(sv) => if !(@core.ct_eq(refv, sv)) { simplify_ok = false }
        }
    }
    pi = pi + 1
  }
  @core.chk(out, "正規化保存語意（\{plans.length()} 條計畫：exec(simplify p) = exec(p)）", simplify_ok)
  @core.chk(out, "正規化冪等、且不增加步數（共省下 \{saved} 步）", idem_ok && shorter)
  // 合併真的讓流量下降
  let shape : Array[Int32] = [2, 3, 2]
  let traffic_ok = {
    let unfused = plan_traffic(plans[0], shape)
    let fused = plan_fused_traffic(plans[0], shape)
    unfused == 3 * @core.ct_size(shape) && fused == @core.ct_size(shape)
  }
  @core.chk(
    out,
    "三連逐元素步：未合併流量 3N = \{plan_traffic(plans[0], shape)}，合併後 N = \{plan_fused_traffic(plans[0], shape)}",
    traffic_ok,
  )
  let mut monoton = true
  let mut strict = 0
  pi = 0
  while pi < plans.length() {
    let p = plans[pi]
    let unfused = plan_traffic(p, shape)
    let fused = plan_fused_traffic(p, shape)
    if fused > unfused {
      monoton = false
    }
    if fused < unfused {
      strict = strict + 1
    }
    pi = pi + 1
  }
  @core.chk(out, "合併流量 ≤ 未合併流量，且 \{strict} 條計畫嚴格下降", monoton && strict > 0)
  @core.chk(
    out,
    "只有逐元素步的計畫合併後只剩一趟（N = \{@core.ct_size(shape)}）",
    plan_fused_traffic(plan_new([StScale(q1()), StAdd(q2()), StScale(q3())]), shape) ==
      @core.ct_size(shape),
  )
  out
}

// ---------------------------------------------------------------------------
// 4. 分塊與道
// ---------------------------------------------------------------------------

///|
pub fn law_hal_tiling_partition() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let mut partitions = 0
  let mut perfect = true
  let mut n = 1
  while n < 40 {
    let mut span = 1
    while span < 9 {
      let blocks = hal_blocks(n, span)
      let cover : Array[Int32] = Array::make(n, 0)
      let mut total = 0
      let mut i = 0
      while i < blocks.length() {
        let start = blocks[i][0]
        let size = blocks[i][1]
        if size < 1 || size > span || start < 0 || start + size > n {
          perfect = false
        }
        let mut k = 0
        while k < size {
          cover[start + k] = cover[start + k] + 1
          k = k + 1
        }
        total = total + size
        i = i + 1
      }
      if total != n {
        perfect = false
      }
      let mut j = 0
      while j < n {
        if cover[j] != 1 {
          perfect = false
        }
        j = j + 1
      }
      partitions = partitions + 1
      span = span + 1
    }
    n = n + 1
  }
  @core.chk(
    out,
    "\{partitions} 組 (n, span)（n = 1..39、span = 1..8）分塊恰好覆蓋每個位置一次",
    perfect,
  )
  // 後端走訪順序也是排列
  let backends = hal_backends()
  let mut perm_ok = true
  let mut perm_count = 0
  let ns : Array[Int32] = [1, 7, 12, 36]
  let mut bi = 0
  while bi < backends.length() {
    let be = backends[bi]
    let mut ni = 0
    while ni < ns.length() {
      let n2 = ns[ni]
      let order = hal_order(be, n2)
      let seen : Array[Int32] = Array::make(n2, 0)
      let mut sum = 0
      let mut i2 = 0
      let mut size_ok = order.length() == n2
      while i2 < order.length() {
        let p = order[i2]
        if p < 0 || p >= n2 {
          size_ok = false
        } else {
          seen[p] = seen[p] + 1
        }
        sum = sum + p
        i2 = i2 + 1
      }
      let mut j2 = 0
      while j2 < n2 {
        if seen[j2] != 1 {
          size_ok = false
        }
        j2 = j2 + 1
      }
      if !(size_ok) || sum != n2 * (n2 - 1) / 2 {
        perm_ok = false
      }
      perm_count = perm_count + 1
      ni = ni + 1
    }
    bi = bi + 1
  }
  @core.chk(
    out,
    "\{perm_count} 組 (後端, n) 的走訪順序都是 0..<n 的排列（位置總和 = n(n−1)/2）",
    perm_ok,
  )
  // 向量道：覆蓋與浪費
  let mut lane_ok = true
  let mut worst = 0
  let mut checked = 0
  let mut n3 = 1
  while n3 < 40 {
    let mut lane = 1
    while lane < 9 {
      let passes = hal_lane_passes(n3, lane)
      let covered = passes * lane
      if covered < n3 || (passes - 1) * lane >= n3 {
        lane_ok = false
      }
      let waste = covered - n3
      if waste > worst {
        worst = waste
      }
      if waste >= lane {
        lane_ok = false
      }
      checked = checked + 1
      lane = lane + 1
    }
    n3 = n3 + 1
  }
  @core.chk(
    out,
    "\{checked} 組 (n, lane)：道覆蓋足夠且浪費 < lane（最大浪費 = \{worst}）",
    lane_ok,
  )
  out
}

// ---------------------------------------------------------------------------
// 5. 決定性、純度、無別名
// ---------------------------------------------------------------------------

///|
pub fn law_hal_determinism_and_purity() -> Array[(String, Bool)] {
  let out : Array[(String, Bool)] = []
  let t = @core.ct_probe([2, 3, 2], [3, 1, 2])
  let p = plan_new([StSwap(0), StScale(q1()), StContract(0)])
  let first = hal_exec(p, t)
  let second = hal_exec(p, t)
  let deterministic = match (first, second) {
    (Some(x), Some(y)) => @core.ct_eq(x, y)
    _ => false
  }
  @core.chk(out, "同一計畫跑兩次結果相同（決定性）", deterministic)
  // 無別名：改動輸出不會動到輸入
  let input_before = @core.ct_copy(t)
  let out_tensor = match hal_exec(plan_new([StScale(@core.qq_int(5))]), t) {
    Some(x) => x
    None => @core.ct_copy(t)
  }
  out_tensor.data[0] = @core.qq_int(12345)
  @core.chk(out, "輸出是新緩衝：改動輸出不影響輸入（無別名）", @core.ct_eq(t, input_before))
  // 輸入不被就地修改
  let t2 = @core.ct_probe([2, 2, 2], [1, 1, 1])
  let before = @core.ct_copy(t2)
  let _ = hal_exec(plan_new([StSwap(1), StScale(@core.qq_int(3)), StContract(2)]), t2)
  @core.chk(out, "計畫執行不會就地改寫輸入張量", @core.ct_eq(t2, before))
  // 後端不改語意 ⇒ 同一輸入不同後端結果相同（純度檢查的後端版本）
  let backends = hal_backends_typed()
  let mut same = true
  let mut bi = 0
  while bi < backends.length() {
    let be = backends[bi].0
    let got = hal_exec_backend(be, p, t)
    match got {
      None => same = false
      Some(g) =>
        match first {
          None => same = false
          Some(f) => if !(@core.ct_eq(g, f)) { same = false }
        }
    }
    bi = bi + 1
  }
  @core.chk(out, "純度：後端標籤不進結果（\{backends.length()} 個後端同值）", same)
  out
}

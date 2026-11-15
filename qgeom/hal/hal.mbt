// ---------------------------------------------------------------------------
// qgeom/hal — 高維「合體運算」的硬體抽象層（hardware abstraction layer）
// ---------------------------------------------------------------------------
// 抽象邊界是一條 trait：`FusedBackend`。它只承諾三件事——名字、向量道寬度、
// 分塊跨度——而**不**承諾走訪順序、暫存策略或道利用率。三個具體後端
// （純量參考、向量道、分塊）用完全不同的順序走同一張張量，卻必須給出
// 位元相同的結果；`law_hal_backend_equivalence` 就是把這件事當場算一遍。
//
// 「合體」在這裡有精確定義：`StContract` 把一軸收縮掉（秩 −1），而
// 交換＋收縮可以合併成一個動作（`law_hal_stage_semantics` 的
// `contract(τT, ax) = contract(T, ax+1)`）。`plan_fuse`／`plan_traffic`
// 兩個函式則回答硬體層真正的問題：合併之後要掃幾遍記憶體。
//
// 這個檔案只做「計畫」與「後端」的代數；張量本身、軸向交換算子在
// `qgeom/core`，兩者用同一個 `@core.CTensor` 型別對接，沒有第二套表示。

///|
/// 合體運算的一步。步是純函式，因此計畫的任何重新排序只要保持局部性，
/// 結果都不變——這正是抽象層必須先確立的不變量。
pub(all) enum Stage {
  /// 軸向交換 τ（交換相鄰兩軸）
  StSwap(Int32)
  /// 整張乘一個純量
  StScale(@core.QQ)
  /// 整張加一個常數
  StAdd(@core.QQ)
  /// 沿一軸收縮（高維合體：秩 −1）
  StContract(Int32)
}

///|
/// 一條運算計畫。形狀由輸入張量決定，計畫本身只記步驟。
pub(all) struct Plan {
  stages : Array[Stage]
}

///|
pub fn plan_new(stages : Array[Stage]) -> Plan {
  Plan::{ stages: stages }
}

///|
pub fn plan_concat(a : Plan, b : Plan) -> Plan {
  let out : Array[Stage] = []
  let mut i = 0
  while i < a.stages.length() {
    out.push(a.stages[i])
    i = i + 1
  }
  let mut j = 0
  while j < b.stages.length() {
    out.push(b.stages[j])
    j = j + 1
  }
  Plan::{ stages: out }
}

// ---------------------------------------------------------------------------
// 硬體後端：抽象邊界
// ---------------------------------------------------------------------------

///|
/// 後端只承諾三件事；走訪順序是實作細節，因此**不可**影響結果。
pub(open) trait FusedBackend {
  fn backend_label(Self) -> String
  fn lane_width(Self) -> Int32
  fn tile_span(Self) -> Int32
}

///|
/// 純量參考後端：單道、不分塊（走訪順序就是線性順序）。
pub(all) struct ScalarCore {
  tag : Int32
}

///|
/// 向量道後端：道內交錯（把一趟拆成 `lanes` 條等距子掃描）。
pub(all) struct LaneCore {
  lanes : Int32
}

///|
/// 分塊後端：分塊 + 道內交錯（典型共享記憶體 tile 策略）。
pub(all) struct BlockedCore {
  lanes : Int32
  block : Int32
}

///|
impl FusedBackend for ScalarCore with fn backend_label(self) {
  "scalar#" + self.tag.to_string()
}

///|
impl FusedBackend for ScalarCore with fn lane_width(self) {
  let _ = self.tag
  1
}

///|
impl FusedBackend for ScalarCore with fn tile_span(self) {
  let _ = self.tag
  1 << 20
}

///|
impl FusedBackend for LaneCore with fn backend_label(self) {
  "lane" + self.lanes.to_string()
}

///|
impl FusedBackend for LaneCore with fn lane_width(self) {
  self.lanes
}

///|
impl FusedBackend for LaneCore with fn tile_span(self) {
  let _ = self.lanes
  1 << 20
}

///|
impl FusedBackend for BlockedCore with fn backend_label(self) {
  "block" + self.block.to_string() + "x lane" + self.lanes.to_string()
}

///|
impl FusedBackend for BlockedCore with fn lane_width(self) {
  self.lanes
}

///|
impl FusedBackend for BlockedCore with fn tile_span(self) {
  self.block
}

///|
/// 後端的實際走訪順序：把 `0..<n` 重新排成一串位置。每個位置恰好出現一次，
/// 這一點由 `law_hal_tiling_partition` 當場數出來。
pub fn[T : FusedBackend] hal_order(be : T, n : Int32) -> Array[Int32] {
  let lane = if be.lane_width() < 1 { 1 } else { be.lane_width() }
  let span = if be.tile_span() < 1 { 1 } else { be.tile_span() }
  let out : Array[Int32] = []
  let mut base = 0
  while base < n {
    let len = if base + span <= n { span } else { n - base }
    // 道內交錯：先掃第 0 道，再掃第 1 道……
    let mut l = 0
    while l < lane {
      let mut k = 0
      while k < len {
        if k % lane == l {
          out.push(base + k)
        }
        k = k + 1
      }
      l = l + 1
    }
    base = base + span
  }
  out
}

// ---------------------------------------------------------------------------
// 單步語意（參考實作）
// ---------------------------------------------------------------------------

///|
/// 一步的參考語意：與 `qgeom/core` 的算子直接對接。
pub fn hal_stage_apply(t : @core.CTensor, s : Stage) -> @core.CTensor? {
  match s {
    StSwap(ax) => @core.ct_swap_axes(t, ax)
    StScale(c) => Some(@core.ct_scale(c, t))
    StAdd(c) => Some(@core.ct_add(t, @core.ct_of(t.shape, fn(_idx) { c })))
    StContract(ax) => @core.ct_contract_axis(t, ax)
  }
}

///|
/// 參考直譯器：依序套用每個步驟。
pub fn hal_exec(p : Plan, t : @core.CTensor) -> @core.CTensor? {
  let mut cur = t
  let mut i = 0
  while i < p.stages.length() {
    match hal_stage_apply(cur, p.stages[i]) {
      None => return None
      Some(next) => cur = next
    }
    i = i + 1
  }
  Some(cur)
}

// ---------------------------------------------------------------------------
// 後端直譯器：同樣的語意、不同的走訪順序
// ---------------------------------------------------------------------------

///|
/// 以某個後端的走訪順序套用一步。對每一步都是「輸出位置按後端順序填」，
/// 因此結果與 `hal_stage_apply` 必須逐位元相同。
pub fn[T : FusedBackend] hal_stage_apply_backend(
  be : T,
  t : @core.CTensor,
  s : Stage,
) -> @core.CTensor? {
  match s {
    StScale(c) => {
      let out = @core.ct_zeros(t.shape)
      let order = hal_order(be, t.data.length())
      let mut i = 0
      while i < order.length() {
        let lin = order[i]
        out.data[lin] = @core.qq_mul(c, t.data[lin])
        i = i + 1
      }
      Some(out)
    }
    StAdd(c) => {
      let out = @core.ct_zeros(t.shape)
      let order = hal_order(be, t.data.length())
      let mut i = 0
      while i < order.length() {
        let lin = order[i]
        out.data[lin] = @core.qq_add(t.data[lin], c)
        i = i + 1
      }
      Some(out)
    }
    StSwap(ax) => {
      let r = @core.ct_rank(t)
      if ax < 0 || ax + 1 >= r {
        return None
      }
      let new_shape = @core.ct_shape_copy(t.shape)
      new_shape[ax] = t.shape[ax + 1]
      new_shape[ax + 1] = t.shape[ax]
      let out = @core.ct_zeros(new_shape)
      let order = hal_order(be, out.data.length())
      let out_strides = @core.ct_strides(new_shape)
      let mut i = 0
      while i < order.length() {
        let lin = order[i]
        // 由線性位置反推多維索引
        let idx : Array[Int32] = Array::make(r, 0)
        let mut a = 0
        while a < r {
          idx[a] = (lin / out_strides[a]) % new_shape[a]
          a = a + 1
        }
        let old_idx = @core.ct_shape_copy(idx)
        old_idx[ax] = idx[ax + 1]
        old_idx[ax + 1] = idx[ax]
        out.data[lin] = t.data[@core.ct_lin(t, old_idx)]
        i = i + 1
      }
      Some(out)
    }
    StContract(ax) => {
      let r = @core.ct_rank(t)
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
      let out = @core.ct_zeros(new_shape)
      let order = hal_order(be, out.data.length())
      let out_strides = @core.ct_strides(new_shape)
      let in_strides = @core.ct_strides(t.shape)
      let mut i = 0
      while i < order.length() {
        let lin = order[i]
        let idx : Array[Int32] = Array::make(r - 1, 0)
        let mut a2 = 0
        while a2 < r - 1 {
          idx[a2] = (lin / out_strides[a2]) % new_shape[a2]
          a2 = a2 + 1
        }
        // 還原成原張量的索引，再沿 `ax` 求和
        let mut acc = @core.qq_zero()
        let mut step = 0
        while step < t.shape[ax] {
          let full : Array[Int32] = Array::make(r, 0)
          let mut a3 = 0
          let mut b3 = 0
          while a3 < r {
            if a3 == ax {
              full[a3] = step
            } else {
              full[a3] = idx[b3]
              b3 = b3 + 1
            }
            a3 = a3 + 1
          }
          let mut src = 0
          let mut q = 0
          while q < r {
            src = src + full[q] * in_strides[q]
            q = q + 1
          }
          acc = @core.qq_add(acc, t.data[src])
          step = step + 1
        }
        out.data[lin] = acc
        i = i + 1
      }
      Some(out)
    }
  }
}

///|
/// 後端直譯器：整條計畫。
pub fn[T : FusedBackend] hal_exec_backend(be : T, p : Plan, t : @core.CTensor) -> @core.CTensor? {
  let mut cur = t
  let mut i = 0
  while i < p.stages.length() {
    match hal_stage_apply_backend(be, cur, p.stages[i]) {
      None => return None
      Some(next) => cur = next
    }
    i = i + 1
  }
  Some(cur)
}

// ---------------------------------------------------------------------------
// 合併（fusion）與記憶體流量模型
// ---------------------------------------------------------------------------

///|
/// 一步是否為「逐元素」步（可以跟前後逐元素步合併成同一趟掃描）。
pub fn stage_is_elementwise(s : Stage) -> Bool {
  match s {
    StScale(_) => true
    StAdd(_) => true
    _ => false
  }
}

///|
/// 計畫在給定初始形狀下的「未合併」流量：每一步都完整掃一遍。
pub fn plan_traffic(p : Plan, shape : Array[Int32]) -> Int32 {
  let mut dims = @core.ct_shape_copy(shape)
  let mut total = 0
  let mut i = 0
  while i < p.stages.length() {
    total = total + @core.ct_size(dims)
    match p.stages[i] {
      StContract(ax) =>
        if ax >= 0 && ax < dims.length() {
          let next : Array[Int32] = Array::make(dims.length() - 1, 0)
          let mut a = 0
          let mut b = 0
          while a < dims.length() {
            if a != ax {
              next[b] = dims[a]
              b = b + 1
            }
            a = a + 1
          }
          dims = next
        }
      _ => ()
    }
    i = i + 1
  }
  total
}

///|
/// 合併後的流量：連續的逐元素步共用一趟掃描。
pub fn plan_fused_traffic(p : Plan, shape : Array[Int32]) -> Int32 {
  let mut dims = @core.ct_shape_copy(shape)
  let mut total = 0
  let mut i = 0
  let mut in_run = false
  while i < p.stages.length() {
    let el = stage_is_elementwise(p.stages[i])
    if el {
      if !in_run {
        total = total + @core.ct_size(dims)
        in_run = true
      }
    } else {
      total = total + @core.ct_size(dims)
      in_run = false
    }
    match p.stages[i] {
      StContract(ax) =>
        if ax >= 0 && ax < dims.length() {
          let next : Array[Int32] = Array::make(dims.length() - 1, 0)
          let mut a = 0
          let mut b = 0
          while a < dims.length() {
            if a != ax {
              next[b] = dims[a]
              b = b + 1
            }
            a = a + 1
          }
          dims = next
        }
      _ => ()
    }
    i = i + 1
  }
  total
}

///|
/// 計畫正規化：合併相鄰純量步、丟掉單位步、消去相鄰同軸交換（τ² = 1）。
/// 目標不是最短，而是「語意不變且冪等」。
pub fn plan_simplify(p : Plan) -> Plan {
  let out : Array[Stage] = []
  let mut i = 0
  while i < p.stages.length() {
    let s = p.stages[i]
    match s {
      StScale(c) =>
        if @core.qq_eq(c, @core.qq_one()) {
          ()
        } else {
          let n = out.length()
          let merged = if n > 0 {
            match out[n - 1] {
              StScale(c0) => Some(StScale(@core.qq_mul(c0, c)))
              _ => None
            }
          } else {
            None
          }
          match merged {
            Some(m) => out[n - 1] = m
            None => out.push(s)
          }
        }
      StAdd(c) =>
        if @core.qq_is_zero(c) {
          ()
        } else {
          let n = out.length()
          let merged = if n > 0 {
            match out[n - 1] {
              StAdd(c0) => Some(StAdd(@core.qq_add(c0, c)))
              _ => None
            }
          } else {
            None
          }
          match merged {
            Some(m) => out[n - 1] = m
            None => out.push(s)
          }
        }
      StSwap(ax) => {
        let n = out.length()
        let cancels = if n > 0 {
          match out[n - 1] {
            StSwap(ax0) => ax0 == ax
            _ => false
          }
        } else {
          false
        }
        if cancels {
          let _ = out.pop()
        } else {
          out.push(s)
        }
      }
      StContract(_) => out.push(s)
    }
    i = i + 1
  }
  Plan::{ stages: out }
}

// ---------------------------------------------------------------------------
// 分塊與道的計數定律
// ---------------------------------------------------------------------------

///|
/// 把 `0..<n` 切成跨度為 `span` 的連續塊，每塊 `[start, size]`。
pub fn hal_blocks(n : Int32, span : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let s = if span < 1 { 1 } else { span }
  let mut base = 0
  while base < n {
    let size = if base + s <= n { s } else { n - base }
    out.push([base, size])
    base = base + s
  }
  out
}

///|
/// 寬度 `lane` 的向量道要掃幾趟才能蓋完 `n` 個元素。
pub fn hal_lane_passes(n : Int32, lane : Int32) -> Int32 {
  let l = if lane < 1 { 1 } else { lane }
  (n + l - 1) / l
}

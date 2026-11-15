// ---------------------------------------------------------------------------
// cmd/qprob/main.mbt — 五階量子概率與非交換隨機空間定律總表執行器
// ---------------------------------------------------------------------------

///|
fn main {
  let mut pass = 0
  let mut fail = 0
  let mut idx = 0
  let stages = [
    (
      "Stage I · qprob/asymptotic — 代數子場塔與無窮漸近極限空間",
      @asymptotic.asym_all_laws(),
    ),
    (
      "Stage II · qprob/unbounded — 無界算子 *-代數概率空間與矩重構",
      @unbounded.unbounded_all_laws(),
    ),
    (
      "Stage III · qprob/fock — 全量子福克空間與 q-變形三統計分裂",
      @fock.fock_all_laws(),
    ),
    (
      "Stage IV · qprob/ccr_field — 連續創生與湮滅算子場、Wick 正規序與量子 Itô 代數",
      @ccr_field.ccr_all_laws(),
    ),
    (
      "Stage V · qprob/nc_measure — 非交換隨機分佈、POVM 算子測度與自由累積量統合",
      @nc_measure.nc_all_laws(),
    ),
  ]
  for stage in stages {
    let (title, chapters) = stage
    println("=== \{title} ===")
    for ch in chapters {
      let (ch_name, laws) = ch
      println("")
      println("  ── \{ch_name}")
      for item in laws {
        let (label, ok) = item
        idx = idx + 1
        if ok {
          pass = pass + 1
        } else {
          fail = fail + 1
        }
        let mark = if ok { "ok  " } else { "FAIL" }
        println("  \{mark} [\{@asymptotic.pad_left_int(idx, 3)}] \{label}")
      }
    }
    println("")
  }
  println(
    "通過 \{pass} / \{pass + fail} 個結構演化定理與演算法命題",
  )
  if fail > 0 {
    abort("qprob verification failed")
  }
}

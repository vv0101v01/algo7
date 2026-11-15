///|
fn pad(n : Int32, w : Int32) -> String {
  let mut out = "\{n}"
  while out.length() < w {
    out = " " + out
  }
  out
}

///|
fn main {
  let mut pass = 0
  let mut fail = 0
  let mut index = 0
  let packages = [
    (
      "qgeom/core — 精確四元數與軸向交換張量變體",
      @core.all_laws(),
    ),
    ("qgeom/hal — 高維合體運算的硬體抽象層", @hal.hal_all_laws()),
    (
      "qgeom/geom — 平移射影與雅可布全射張量積",
      @geom.geom_all_laws(),
    ),
    (
      "qgeom/susy — 超對稱四元數頂點對偶與複形四元數德朗姆幾何",
      @susy.susy_all_laws(),
    ),
    (
      "qgeom/qk — 四元數凱勒曲率張量群空間與雙射緊緻四元雅可比簇",
      @qk.qk_all_laws(),
    ),
  ]
  for pkg in packages {
    let (title, chapters) = pkg
    println("=== \{title} ===")
    for chapter in chapters {
      let (name, laws) = chapter
      println("")
      println("  ── \{name}")
      for law in laws {
        let (label, ok) = law
        index = index + 1
        if ok {
          pass = pass + 1
        } else {
          fail = fail + 1
        }
        let mark = if ok { "ok  " } else { "FAIL" }
        println("  \{mark} [\{pad(index, 3)}] \{label}")
      }
    }
  }
  println("")
  println("通過 \{pass} / \{pass + fail} 個命題")
  if fail > 0 {
    abort("qgeom laws failed")
  }
}

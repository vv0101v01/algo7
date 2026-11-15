# `cmd/qgeom/` — qgeom 子聯邦的定律總表

> **架構位置**：套件 `cmd-qgeom`，聯邦 `accel`（qgeom 子聯邦），**Layer 4**，
> `depends_on: [qgeom-core, qgeom-hal, qgeom-geom, qgeom-susy, qgeom-qk]`。
> 可執行套件（`pkgtype(kind: "executable")`）；只消費、不生產，任何套件都不得匯入它。

## 1. 一句話定位

把 `qgeom/core`、`qgeom/hal`、`qgeom/geom`、`qgeom/susy`、`qgeom/qk` 五個套件的
`*_all_laws()` 逐條執行並印出；任何一條為假就 `abort`。**179 條命題**。

## 2. 檔案

| 檔案 | 行數 | 職責 |
|---|---:|---|
| `main.mbt` | 59 | `main`：依套件、依章節印出每個命題，統計並決定結束碼 |
| `moon.pkg` | 8 | 五個 import ＋ `pkgtype(kind: "executable")` |

## 3. 得到的定理／實作的演算法

本資料夾不含數學內容——定理與演算法在五個被匯入的套件裡（見 [`qgeom/README.md`](../../qgeom/README.md)）。
這裡唯一的邏輯是「全部為真才正常結束」。

## 4. 依賴圖

```
qgeom/core ──┬──► qgeom/hal  ──┐
             ├──► qgeom/geom ──┤
             ├──► qgeom/susy ──┼──► cmd/qgeom（main）
             └──► qgeom/qk   ──┘
```

## 5. 流程與輸入／輸出

* **輸入**：無（不讀檔、不讀參數）。
* **輸出**（stdout）：逐套件、逐章節、逐命題編號 `1..179`

```
=== qgeom/core — 精確四元數與軸向交換張量變體 ===

  ── 精確有理數體 QQ
  ok   [  1] 樣本數 = 8（含 0、±1、負數與非整分數）
  …
=== qgeom/hal — 高維合體運算的硬體抽象層 ===
  …
=== qgeom/geom — 平移射影與雅可布全射張量積 ===
  …
=== qgeom/susy — 超對稱四元數頂點對偶與複形四元數德朗姆幾何 ===
  …
=== qgeom/qk — 四元數凱勒曲率張量群空間與雙射緊緻四元雅可比簇 ===
  …
通過 179 / 179 個命題
```

* **結束碼**：全部為真 ⇒ 0；否則 `abort("qgeom laws failed")`（wasm 會顯示 `RuntimeError: unreachable`，
  因此判斷成敗要看 stdout 的 `通過` 行，不要只看結束碼）。
* 標籤裡的數字是執行時算出後嵌入的；改了演算法而數字變了，輸出就會跟著變。

## 6. 規模

| 套件 | 章節 | 命題 |
|---|---:|---:|
| `qgeom/core` | 9 | 57 |
| `qgeom/hal` | 5 | 20 |
| `qgeom/geom` | 5 | 35 |
| `qgeom/susy` | 4 | 28 |
| `qgeom/qk` | 6 | 39 |
| **合計** | **29** | **179** |

# `qprob/ccr_field/` — 連續創生與湮滅算子場、Wick 正規序與量子 Itô 代數

> **架構位置**：套件 `qprob-ccr-field`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 3**，`depends_on: [qprob-asymptotic, qprob-unbounded, qprob-fock]`。

## 1. 定位

將離散福克模態連續化為 `L²([a,b], dt)` 塗抹算子場 `A(g)`、`A†(f)`，以第一階 Richardson 外推證明離散福克格點對易子在 `N → ∞` 零誤差收斂至連續積分內積；實作 Wick 正規序展開演算法、Weyl 相空間辛 2-上循環，以及 Hudson–Parthasarathy 量子隨機微積分乘法表與么正演化判準。

## 2. 檔案

| 檔案 | 行數 | 職責 |
|---|---:|---|
| `continuum_field.mbt` | 425 | 多項式測試函數 `ContinuumTestFn`、連續 `L²` 內積、離散福克格點對易子 `fock_lattice_bosonic_commutator`、`wick_normal_order`、`wick_vacuum_expectation`、`weyl_symplectic_form`、`quantum_ito_mul`、`qsde_ito_product` |
| `laws.mbt` | 302 | 4 章 / **11 條命題**（含 16 支展開對三配對高斯 4 點關聯定理與忽略 Itô 修正項之負控制） |

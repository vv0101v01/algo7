# `qprob/unbounded/` — 無界算子概率空間與矩問題重構

> **架構位置**：套件 `qprob-unbounded`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 1**，`depends_on: [qprob-asymptotic]`。

## 1. 定位

在共同不變稠密核 `𝒟` 上實現攜帶多項式成長階 `growth_deg` 的無界 `*-`代數 `Op*(𝒟)` 與量子概率態 `φ`，導出 Robertson–Schrödinger 不確定性不等式、Yosida 預解有界正則化，以及由無界矩序列反演 Jacobi 三對角無界算子的 Favard–Chebyshev–Lanczos 演算法。

## 2. 檔案

| 檔案 | 行數 | 職責 |
|---|---:|---|
| `probability_space.mbt` | 543 | `QComplex`、`UnboundedOp`（零算子、中心化、伴隨、複合、交換子、反交換子、粒子數與對偶 Jacobi 算子）、`QuantumProbState`（純態與對角 Gibbs 態）、`check_robertson_schrodinger`、`yosida_diagonal_approximant`、`reconstruct_jacobi_from_moments` |
| `laws.mbt` | 363 | 4 章 / **12 條命題**（含 Dirac 自伴對易子、真空飽和、Hermite 與 Poisson–Charlier 重構及負控制） |

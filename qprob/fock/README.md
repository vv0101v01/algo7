# `qprob/fock/` — 全量子福克空間與 q-變形子空間

> **架構位置**：套件 `qprob-fock`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 2**，`depends_on: [qprob-asymptotic, qprob-unbounded]`。

## 1. 定位

構造單粒子空間上的全量子（Boltzmann）福克空間 `ℱ_0(ℋ) = ⨁_{n≥0} ℋ^{⊗n}` 與 Bożejko–Speicher `q`-變形創生／湮滅算子及逆序數加權內積，證明 `q = 0`（自由 Cuntz–Toeplitz 與 Wigner 半圓 Catalan 矩）、`q = +1`（玻色對稱商空間）、`q = −1`（費米外代數與 Pauli 不相容核）在同一內積核下的統一分裂，以及 `Γ(T)` 與 `dΓ(H)` 二次量子化函子律。

## 2. 檔案

| 檔案 | 行數 | 職責 |
|---|---:|---|
| `full_fock.mbt` | 435 | `FockWord`、`FullFockVec`、`fock_create_left`、`fock_annihilate_q`、置換逆序數 `perm_inversions`、`fock_inner_q`、`fock_q_gram_matrix`、`fock_dgamma`、`fock_gamma` |
| `laws.mbt` | 341 | 4 章 / **13 條命題**（含 `|q| > 1` 破壞正定性與詞序非交換負控制） |

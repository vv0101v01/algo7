# `qprob/nc_measure/` — 非交換隨機分佈、POVM 算子測度與自由累積量

> **架構位置**：套件 `qprob-nc-measure`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 4**，`depends_on: [qprob-asymptotic, qprob-unbounded, qprob-fock, qprob-ccr-field]`。

## 1. 定位

作為五階結構演化的統合頂點，實作非交換過完備正算子值測度（POVM）、Born 機率律、CPTP 量子馬可夫通道與 Naimark 等距正交擴張演算法；並以非交叉配分卷積遞迴實作 Speicher 矩與自由累積量雙向轉換、自由加性卷積 `⊞`、Voiculescu 自由中心極限定理（Free CLT × Richardson 外推），最終將第四階連續場 Wick 高斯矩與第三階全福克半圓律自由矩閉合為對偶定理。

## 2. 檔案

| 檔案 | 行數 | 職責 |
|---|---:|---|
| `noncommutative_measure.mbt` | 384 | `PovmMeasure`、`povm_born_probabilities`、`verify_naimark_dilation`、`moments_to_free_cumulants`、`free_cumulants_to_moments`、`free_additive_convolution_moments`、`free_clt_scaled_moments`、`moments_to_classical_cumulants`、`apply_cptp_channel` |
| `laws.mbt` | 408 | 4 章 / **13 條命題**（含古典 vs 自由四階分岔、Free CLT 與五階大統一對偶定理） |

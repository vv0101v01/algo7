# `qprob/asymptotic/` — 代數子場塔與無窮漸近極限空間

> **架構位置**：套件 `qprob-asymptotic`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 0**，`depends_on: []`。零外部依賴，只使用 `moonbitlang/core`。

## 1. 定位

構造整個五階演化鏈的數域與極限基礎：有序子場塔 `ℚ ⊂ ℚ(√d)`、非阿基米德截斷 Laurent 漸近噴流場 `ℚ((ε))_≤M`（`ε → 0⁺`），以及射影極限空間 `lim_← V_k` 與四種精確收斂加速演算法。

## 2. 檔案

| 檔案 | 行數 | 職責 |
|---|---:|---|
| `subfield.mbt` | 546 | 正規形有理數 `QVal`（含負次冪）、二次擴張子場 `QuadElem`（共軛、範數、跡、反元素）、漸近噴流 `AsymJet`（賦值階、標準部商同態、長除法反元素、非阿基米德序） |
| `projective_limit.mbt` | 332 | 有理矩陣乘法與上三角高斯消去精確秩 `qmat_rank`、射影極限塔 `ProjectiveTower`、Mittag-Leffler 穩定秩、Richardson–Neville 外推、Shanks–Aitken `Δ²`、Wynn `ε`-算法、Cesàro 平均 |
| `laws.mbt` | 352 | 4 章 / **21 條命題**（含 4 條負控制） |

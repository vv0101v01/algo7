# `cmd/qprob/` — 量子概率與量子機率脈絡範疇合流執行入口（Layer 6）

> **架構位置**：執行器組件 `cmd-qprob`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 6**，`depends_on: [qprob-asymptotic, qprob-unbounded, qprob-fock, qprob-ccr-field, qprob-nc-measure, qprob-context-cat]`。
> **檔案規模**：`main.mbt`（63 行）。

---

## 1. 功能說明

`cmd/qprob` 是 `qprob` 六階子聯邦的獨立可執行測試與驗算驅動程式，依序執行全部 **6 階、24 章、88 條命題**（含 16 條負控制與分岔命題），逐條列印精確編號 `[001]–[088]`、章節命題名稱與實算數值見證；若有任何單一命題失敗立即以 `abort("qprob verification failed")` 終止執行並令 CI 失敗。

### 執行涵蓋範圍

| 區段 | 匯入函式 | 章節數 | 命題編號 | 通過數 |
|---|---|---:|---|---:|
| Stage I (`@asymptotic`) | `asym_all_laws()` | 4 章 | `[001]–[021]` | `21 / 21` |
| Stage II (`@unbounded`) | `unbounded_all_laws()` | 4 章 | `[022]–[033]` | `12 / 12` |
| Stage III (`@fock`) | `fock_all_laws()` | 4 章 | `[034]–[046]` | `13 / 13` |
| Stage IV (`@ccr_field`) | `ccr_all_laws()` | 4 章 | `[047]–[057]` | `11 / 11` |
| Stage V (`@nc_measure`) | `nc_all_laws()` | 4 章 | `[058]–[070]` | `13 / 13` |
| Stage VI (`@context_cat`) | `context_cat_all_laws()` | 4 章 | `[071]–[088]` | `18 / 18` |
| **總計** | — | **24 章** | **`[001]–[088]`** | **`88 / 88`** |

---

## 2. 執行方式與實際終端輸出

```bash
moon run cmd/qprob --target wasm-gc
```

終端結尾輸出：
```text
=== Stage I · qprob/asymptotic — 代數子場塔與無窮漸近極限空間 ===
...
=== Stage VI · qprob/context_cat — 空間子場雙範疇、主命題纖維化、機率單子與量子機率脈絡合流 ===
...
  ok   [ 88] 六階終極合流大定理：雙範疇 8 空間子場 × 主命題纖維化 8/8 × 機率單子 D_ℚ × 量子機率脈絡範疇 QProbCtx 全鏈合流

通過 88 / 88 個結構演化定理與演算法命題
```

完整逐條定理與演算法說明請見 [`../../qprob/README.md`](../../qprob/README.md) 與 [`../../docs/QPROB_THEOREMS_AND_ALGORITHMS.md`](../../docs/QPROB_THEOREMS_AND_ALGORITHMS.md)。

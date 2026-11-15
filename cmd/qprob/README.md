# `cmd/qprob/` — qprob 五階量子概率與非交換隨機空間定律總表

> **架構位置**：套件 `cmd-qprob`，第七聯邦 `discovery`（qprob 子聯邦），**Layer 5**，
> `depends_on: [qprob-asymptotic, qprob-unbounded, qprob-fock, qprob-ccr-field, qprob-nc-measure]`。
> 可執行套件（`pkgtype(kind: "executable")`）。

## 1. 定位

依數學結構演化順序（Stage I → Stage V）逐章重算並印出 `qprob` 全部 **70 條**定理與演算法命題；任何一條為假即 `abort`。

## 2. 執行

```bash
moon run cmd/qprob --target wasm-gc
```

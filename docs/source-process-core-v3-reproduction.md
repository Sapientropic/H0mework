# 过程核心第三版证明与复现

[第三版逐项映射](source-process-core-v3-map.json)连接 C46–C54 的论文位置、公开证明、直接消费者与认证。C1–C45 沿用[首发](first-release-reproduction.md)及[第二版](edition-reproduction.md)的固定材料。

| 主张 | 证明入口 |
| --- | --- |
| C46、C49、C50 | [整账法首版](whole-ledger-map.json) WA38–WA40 |
| C47–C48 | `H0mework.Papers.SourceProcessCoreV3.MV4` |
| C51–C52 | [整账法第二版](whole-ledger-v2-map.json) WA41–WA42 |
| C53–C54 | [整账法第二版](whole-ledger-v2-map.json) WA44–WA45 |

C47–C48 的[固定选集](../checks/source-process-core-v3-selection.json)以 Homework
`ba7e274beb1de38900a6fc2c8c8dfe6cfad9d9aa` 为证明来源。它包含实际输入上的源程序重生、
余项联合求值与写回、共同源查询、实际后继环境更新和线性接收器的直接消费。公开模块路径
及 66 项声明完整类型由映射和回执绑定。历史原认证逐份保留自己的 `fixed_head`。

在 H0mework 根目录使用固定的 Lean 4.33.0 与 Mathlib v4.33.0。Lake 可复用已有产物。

```sh
python3 tools/source_process_core_v3.py entry
python3 tools/source_process_core_v3.py source --output .local/core-v3-public
python3 tools/source_process_core_v3.py build --output .local/core-v3-build
python3 tools/source_process_core_v3.py trust --output .local/core-v3-trust
python3 tools/source_process_core_v3.py types --output .local/core-v3-types
cd Lean
lake env lean --trust=0 ../checks/source-process-core-v3-t0.lean
```

精确恢复时，按原 SHA-256 提供带公开路径变换的原回执，使用
`source --exact --private-originals "$ORIGINAL_RECEIPT_ARCHIVE" --output .local/core-v3-exact`。
公开恢复和 Lean 核验可直接使用 H0mework。

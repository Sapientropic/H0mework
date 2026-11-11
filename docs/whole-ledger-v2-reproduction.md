# 整账法第二版证明与复现

整账法第二版沿用 [WA1–WA40 的首版证明](whole-ledger-reproduction.md)。[第二版选集](../checks/whole-ledger-v2-selection.json)与[逐项映射](whole-ledger-v2-map.json)登记新增证明、原直接消费者和原认证。WA4 的容量核及 WA41–WA42 的同态续行和逐原语回放复用现有公开模块。CP483、CP485 的原认证沿用[一比特第二版](one-bit-v2-reproduction.md)。

| 主张 | 固定研究来源 | 实际验收包 |
| --- | --- | --- |
| WA4 的容量阻滞和源属维护扣款 | `b81a4438` | `capacity` |
| WA41 已付语法树的同态续行 | `df421ff6`，CP483 | `paid-method` |
| WA42 逐原语回放与关系余链微分 | `df421ff6`，CP485 | `relation-cochain` |
| WA43 自由常量表更新及证书反演 | `df421ff6` | `constant-tables` |
| WA44 原执行步、连续区间与防漏重 | `7e4da746`，CP514、CP521、CP528–532 | `batches` |
| WA45 已存历史的续行与时间线 | `7e4da746`，CP596–598 | `stored-history` |

WA44 的 Γ 联合边界和防漏重控制使用原右半零点条件输入。WA45 的原报告绑定 CP596–598 的生成 C，CP596 同时保留负控编译回执。CP528 的 `Shape.lean` 按原认证提交 `9a61a7df` 保存在[历史源包](../evidence/whole-ledger-v2/CP528-original-sources.zip)。十份历史认证的实际状态与本次 H0 构建、信任和类型回执分别登记。

CP532 的同一 canonical method 由原门检在 `--trust=0` 下重放。构建默认使用独立临时输出目录。
本次公开环境的[内核回执](../evidence/whole-ledger-v2/acceptance/cp532-canonical-application.json)
保存同一方法应用的三个结论和实际内核检查结果。

从仓库根目录执行。每次复验使用新的输出目录，Lake 沿用固定工具链、manifest 和现有产物。

```sh
make check-map
python3 tools/whole_ledger_v2.py entry
python3 tools/whole_ledger_v2.py source --output .local/whole-ledger-v2-public
python3 tools/whole_ledger_v2.py build --output .local/whole-ledger-v2-build
python3 tools/whole_ledger_v2.py trust --output .local/whole-ledger-v2-trust
python3 tools/whole_ledger_v2.py types --output .local/whole-ledger-v2-types
```

构建、信任和类型命令可用重复的 `--package` 选定表中的包。精确恢复时，把带公开路径变换的原件按各自的原 SHA-256 命名，放入所提供的原件目录。

```sh
python3 tools/whole_ledger_v2.py source --exact \
  --private-originals "$ORIGINAL_RECEIPT_ARCHIVE" --output .local/whole-ledger-v2-exact
```

[缓存保全报告](../evidence/whole-ledger-v2/acceptance/cache-preservation.json)登记固定分片、完整缓存键、旧成功存档观察和新增分片的构建量。

# 《战争与和平的源生终局定理》复现

按 [固定选集](../checks/enforceable-peace-selection.json) 恢复 PE1–PE33 的六个收稿截面。每个截面单独构建和审计。逐条主张的原声明、公开模块、直接消费者及回执列在[来源映射](enforceable-peace-map.json)。其中 `complete_type.declaration_index` 指向验收回执里的完整 Lean 表达式，`type_sha256` 绑定该表达式。[完整类型回执](../evidence/enforceable-peace/acceptance/declaration-types.json.gz)

| 主张 | Homework 收稿提交 | 公开 Lean 入口 |
| --- | --- | --- |
| PE1–PE10 | `7e4da746f3` | [EnforceablePeace.Terminal](../Lean/H0mework/Papers/EnforceablePeace/Terminal.lean) |
| PE11–PE14 | `b675168bda` | [EnforceablePeace.OpenLanguage](../Lean/H0mework/Papers/EnforceablePeace/OpenLanguage.lean) |
| PE15–PE22 | `71cb159f4f` | [EnforceablePeace.ActualClearance](../Lean/H0mework/Papers/EnforceablePeace/ActualClearance.lean) |
| PE23–PE27 | `3a90cba5ac` | [EnforceablePeace](../Lean/H0mework/Papers/EnforceablePeace.lean) |
| PE28–PE30 | `b5b9c5f86c` | [EnforceablePeace.QuorumRecovery](../Lean/H0mework/Papers/EnforceablePeace/QuorumRecovery.lean) |
| PE31–PE33 | `cf880bb282` | [EnforceablePeace.HandoffDisposition](../Lean/H0mework/Papers/EnforceablePeace/HandoffDisposition.lean) |

## 证明与源码

从仓库根目录执行，沿用固定 Lean 工具链、manifest 和已有 Lake 产物。每次复验选择新的 `--output` 目录。

```bash
make check-map
python3 tools/enforceable_peace.py entry
python3 tools/enforceable_peace.py source --output .local/peace-public
python3 tools/enforceable_peace.py build --output .local/peace-build
python3 tools/enforceable_peace.py trust --output .local/peace-trust
python3 tools/enforceable_peace.py types --output .local/peace-types
```

复用 owner 时比较原字节、语义来源和递归 imports。新增文件的适配是公开 import 和私有声明打开地址，记录在 [export-map](../tools/export-map.json)。两种源码视图都恢复原目录。精确视图反转 Lean 适配，并按 SHA-256 读取含私有运行地址的原回执。公开回执仅按登记规则变换运行地址，保持数字和原检查结果。[证据出版](evidence-publication.md#两种视图)

```bash
python3 tools/enforceable_peace.py source --exact \
  --private-originals /path/to/sha-indexed-originals --output .local/peace-exact
```

## 原账与离线复演

原四机记录按钟 12–16 准入、钟 16–20 冷恢复与换届、钟 20–28 有序处置分别保存。三份回执保持原字节及前序 SHA，原内核日志另行绑定。公开签名账本保留冻结副本的 `replica.bundle` 原字段，包含完整认证前缀和公开验证材料。[原准入](../evidence/enforceable-peace/original/Rc882831f/living-law/terminal-peace/original-six/acceptance.json) · [原恢复](../evidence/enforceable-peace/original/Rb5b9c5f8/living-law/terminal-peace/original-six/recovery-acceptance.json) · [原处置](../evidence/enforceable-peace/original/Rcf880bb2/living-law/terminal-peace/original-six/handoff-resolution-acceptance.json) · [签名账本](../evidence/enforceable-peace/original/certified-journal.json)

用装有 `cryptography` 的 Python 执行离线复验。复验用原激活版本逐笔核签、用公开 Lean 后端重放同一账本，再运行固定源码的冷恢复与有序处置夹具。后两者使用本机生成的签名和隔离账本。 [激活脚本清单](../evidence/enforceable-peace/original/activation/inventory.json)

```bash
python3 tools/enforceable_peace.py replay --output .local/peace-replay
```

PE27 的旧运行时临时覆盖和 PE28–PE29 的早期传输适配器由原回执保留 SHA-256。现存归档中只核到了这两项的摘要。复验使用固定源码、后续原激活程序及已认证的历史行。

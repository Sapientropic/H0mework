# 典范社会总定理：证明选集复现

[逐主张映射](generated-society-map.json)保存原声明、完整源签名、公开 owner、直接消费者、来源及资源；[选集](../checks/generated-society-selection.json)决定完整 imports 与资源闭包。实际执行结果见[验收](generated-society-readiness.md)。

## 固定范围与入口

所有入口均位于 `H0mework.Papers`。

| 入口 | 原来源 | 本篇范围 |
| --- | --- | --- |
| `GeneratedSocietyMInfinity` | e60 | G0–G7，及 G9 实际引用的 e60 消费者 |
| `GeneratedSocietyRegeneration` | AB | G8–G9 责任出生、六项续生及实际 next |
| `GeneratedSocietyInterfaces` | df | G10–G12 已有引用接口 |
| `GeneratedSocietyProgress` | 1d7 | G13 原周期、合规付款与严格已付历史进展 |
| `GeneratedSocietyEconomy` | df | G14–G27、G13 当前来源实例，以及语法、路由／服务、关系再选择和记忆链 |
| `GeneratedSocietyProductivitySupplement` | df | G12 实际资源生成复制、完整原根消费者及必要 imports |
| `GeneratedSocietyProtocolInterface` | e0b | 独立 C.13／PT15 接口及同一 emitter 的 whole-ledger／literal-next 消费者 |

本稿固定合同为 publish `d7253ee2c6db3ff52e709f78aa602ab0a6c921c5`；整理上限为 Homework `df421ff600085cbc290a7ae946193961bed7c83b`。各历史证明保留实际 epoch，G13 的历史 1d7 与 df 当前实例分别登记。十份完整清单的 345 项、原选集及其资源共同保留。

协议入口保留原认证请求提交 `e0b980ffb69e638c9f1e000932f6bb14f778dcdc`；其 11 个请求根的原字节与 df 请求一致。当前 H0 依赖环境分别登记20个缺树 Git provider和实际6c的完整 `Trace.Challenge`，以完整递归身份共享 owner。原请求、实际辅助来源与原认证按各自身份保存。

`Distributed.Execution` 保持原资本认证绑定的实际 provider `7e2cc053821fedbb638122b3b2f8c82134c61ac0` 及完整记忆语义。原 df 单树字节另存于 `docs/source/generated-society/historical/`；精确视图恢复实际选定来源，身份归映射的 `source_providers`。

生产辅助 `Quota.Plan` 采用 `59df7e39d81e8698f3cf8507e64b93829bb1cac3` 的原门控等式；Trace carrier采用 `6c24593364cd7763e3cdccf8f3654996a6dc8b5f` 的完整六分支。原DF无条件Quota等式在paid-memory环境有kernel反例，不能以证明体适配签收；两个原坏体保为G12资源并关联[首轮失败回执](../evidence/generated-society/acceptance/final-manuscript/attempt-original-provider/)。Regression的四个默认记忆字段重绑定属于另一项可逆编译适配，原类型／证明保留。所选主根源码签名保持，实际carrier、完整类型及公理闭包由本轮重新验收。

`Feedback.Regression` 的 signals=3 更新另取固定7e原修复体（同59df），只新增四个原默认字段重绑定，其他定义、原定理类型、证明及4M预算均不变；原DF体与[第二次失败](../evidence/generated-society/acceptance/final-manuscript/attempt-feedback-defaults/)分别保留。

G2 的非空正例、完整 raw 分类、first-refusal 长链和 G9 实际 next 消费均保留。正式 §5.12 的三项实际值依赖也已显式登记。G27 的耗尽量是责任的严格进展预算。完整签名和类型验收保留原 universe、量词与前提。

## 检查与构建

需要 Git、Python 3、make 和 elan。工具链、固定依赖与缓存按 `Lean/lean-toolchain`、`Lean/lake-manifest.json` 使用；已有工作区直接复用现有缓存。新克隆可先执行 `make bootstrap`。

以下命令在仓库根执行，每次使用新的 `.local` 输出目录：

```sh
make check-map
python3 tools/generated_society.py entry --output .local/society-entry
python3 tools/generated_society.py source --output .local/society-public-source

python3 tools/edition_release.py --edition generated-society build --output .local/society-build
python3 tools/edition_release.py --edition generated-society trust --output .local/society-trust
python3 tools/generated_society.py types --output .local/society-types
python3 tools/generated_society.py entry --require-ready --output .local/society-readiness
```

`build` 构建完整七包及其所有实际 producer／消费者 imports。`trust` 先核对 Lake 新鲜性，再检查所选声明的完整 type/value、互递归、归纳类型及 recursor 元数据、公理、`unsafe` 和 `partial`。`types` 独立重建完整 Lean Expr DAG 并由 Lean 检查类型等价。

本轮完整七包构建通过，耗时 189.546 秒；1012 个声明的 trust 与完整类型全部通过，标准三公理为 `Classical.choice`、`Quot.sound`、`propext`，`unsafe=0`、`partial=0`。三层执行的输入前后保持，各类型的 owner、完整名称及 Lean 内核等价逐项核对。map 的 `complete_type` 已绑定[本轮固定回执](../evidence/generated-society/acceptance/final-manuscript/summary.json)。`entry --require-ready` 已核实 4091 个证明 owner、156 项公开资源身份与全部 1012 项完整类型。

执行输入 map 的原字节保于本轮 `execution-map.json.gz`；最终 map 追加真实回执及类型引用，所选证明与声明保持。自行重跑写入新目录，不自动替换固定回执。两次构建失败原件与此前五包的 967 项签收分别保留，后者位于[原目录](../evidence/generated-society/acceptance/expanded-g0-g27/)。

## 原路径恢复

公开恢复不依赖 Homework 工作区或私人运行路径。所有原源码和经过公开化的资源按各 epoch 恢复到原路径；全部资源的原字节逆恢复需要按 `source_sha256` 命名的原件目录：

```sh
python3 tools/generated_society.py source --exact \
  --private-originals "$ORIGINAL_RECEIPT_ARCHIVE" \
  --output .local/society-exact-source
```

两种视图、允许变换及缺件失败行为遵循 [source_view 原件规则](evidence-publication.md#两种视图)。原协议 68 项文件在 G12 的 resources 中逐项保存原 SHA、公开 SHA、custody 来源和原状态。原 strict／T1、原 review、原负例拒绝与本轮 H0 执行分别记账。原 `RejectUnconditionalWindow` 是原 verifier 生成的审计测试，引用的 `ReceiptWindowControls` 属于原九项检查；这组历史原件保持原状态，本稿正向十一根与当前独立检查按自己的闭包验收。

## 默认覆盖与缓存

```sh
python3 tools/ci_plan.py plan
python3 tools/ci_plan.py coverage
python3 -m unittest discover -s tools -p 'test_*.py' -q
```

七个社会入口及新增证明已进入默认构建，完整默认覆盖检查为 53198 个模块，唯一库 owner 检查通过。原五包 source-scope 摘要、旧 52523 个模块及入口的递归身份和 63 个完整分片记录均保持。本轮两稿共新增 2106 个证明 owner、7 个论文入口及 306 项资源，追加两个新分片；逐片完整键、资源逆恢复、旧材料身份及科学输入核对见[当前共用缓存报告](../evidence/economic-constitution/acceptance/initial-intake/cache/current-report.json)。固定布局仅追加新模块位置，未运行 `--rebalance`。

本机 Darwin 缓存与 Linux runner 存档具有不同平台身份。新选集需由正式 CI 取得自己的完整验收，旧 seal 不迁签。本轮没有推送、触发远端工作流或发布；Bell 与量子载体保持 `full_replay=false`。

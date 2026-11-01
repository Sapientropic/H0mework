# 典范社会总定理：证明选集复现

[逐主张映射](generated-society-map.json)保存原声明、原签名、完整类型索引、来源提交、公开 owner、直接消费者及原材料。[选集](../checks/generated-society-selection.json)决定完整 import 闭包；实际执行结果归[验收](generated-society-readiness.md)。

## 固定范围

| 原来源 | 本篇范围 | 独立公开入口 |
| --- | --- | --- |
| `e60a86058abcb74b7f2225f2383c182be8343785` | G0–G7：主体／谱系商、完整 M∞ 基础及 M13 理论采用、非空根法完成、raw/external 桥、退出、first-refusal、制度文化 | `H0mework.Papers.GeneratedSocietyMInfinity` |
| `fde5c14df36b6064c87064acd20830d3df0500bb` | G8–G9：责任出生、同支付六项续生与实际 next | `H0mework.Papers.GeneratedSocietyRegeneration` |
| `df421ff600085cbc290a7ae946193961bed7c83b` | G10–G12 的实际引用接口及所需闭包 | `H0mework.Papers.GeneratedSocietyInterfaces` |
| `1d7db207f618738c642d0f14635949b8b21a9e19` | G13：任意原周期与原合规付款的严格已付历史进展 | `H0mework.Papers.GeneratedSocietyProgress` |
| `df421ff600085cbc290a7ae946193961bed7c83b` | G14–G27、G13 当前来源实例，以及语法、路由／服务、关系再选择与记忆的实际引用链 | `H0mework.Papers.GeneratedSocietyEconomy` |

`df421ff6` 是整理上限，各历史证明保留自己的 epoch。MV5 的 `Distributed.Execution` 恢复原资本认证实际绑定的固定 Git provider `7e2cc053821fedbb638122b3b2f8c82134c61ac0`：原 1297 源环境的其余 1296 份源码均与 df 相同。provider 的完整记忆语义及 `afterDelivery` 保持，未改写其消费者的陈述或证明；原 df 单树依赖字节另保于 `docs/source/generated-society/historical/`。精确视图恢复的是这组实际选定来源，详细身份见映射的 `source_providers`。

五个入口分别接受审查，具有不同历史定义的 Lean 环境保留独立身份。G13 的历史来源和 df 当前实例分别映射，不把两者的 Cycle／Payment 等同。G10–G12 的资本刻画、全原责／next、劳动红利／角色外生产及双路 25 帧接口保存其真实强度；独立后续论文的其余根不在本选集。

G2 同时包含 rooted-external 非空正例和任意 raw submission 的分类。first-refusal 的 repair renewal、承担者及 constitution 消费链全部在闭包内；G9 同时编译原 regeneration 和保存它的 M14 whole。完整声明类型保留全部 universe、量词和前提。

以下承重声明均位于 `SaturationMonoid.ProcessGame.Society` 命名空间；精确 owner 路径及完整类型由映射中的相应主张绑定：

| 主张 | 可引用声明 |
| --- | --- |
| G2 | `M14WholeProgramRegression.canonicalSociety_rootLawComplete_and_u8Available` |
| G2a | `M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.canonicalActualRootedExternal_nonempty` |
| G5 | `M14ProofCarryingCanonicalSocietyFirstRefusalSourceOwnedRecourse.canonicalSocietyFirstRefusalSourceOwnedRecourse` |
| G9 六项共生 | `M14ProofCarryingSameOccurrenceRegenerationRegression.periodicSameOccurrenceRegeneration_certificate` |
| G9 实际接续 | `M14ProofCarryingSameOccurrenceRegenerationRegression.periodicSameOccurrenceRegeneration_nextIsNextStep` |
| G9 whole 保存 | `M14WholeProgramRegression.canonicalSociety_periodicSameOccurrenceRegeneration` |
| G13 严格已付历史进展 | `CanonicalSocietyProgress.strictCanonicalProgress_iff_lt`（历史 1d7 入口；df 实例归 Economy） |
| G14 每笔原付款的完整承接 | `M14ProofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation.proofCarryingFiniteCycleMaximalCanonicalPaidStepPreservation` |
| G18 共终同点事件 | `M14SourceGeneratedCanonicalSocietyCofinalReadout.sourceGeneratedCanonicalSocietyCofinalReadout` |
| G24 任意有限续行与前缀 | `M14ActualEconomicViabilityPath.viableContinuationPathAt`、`M14ActualEconomicViabilityPath.viableContinuationPath_prefix_factorizes` |
| G26 原概率与同源精化 | `M14ActualRepairFailureObserverKernelFold.actualRepairFailure_normalized_probability_exact`、`M14ActualRepairFailureRefinedObserverFold.refined_probability_separates_actual_pair` |

G27 的耗尽量是责任的严格进展预算。其通用承重声明为 `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.NoFreeCapacityRestoration.SourceNativeSequentialActualActionTargetAt.firstSuccessorPositiveProgress_isEmpty`；实际社会消费者与同源 residual answer 一起保于 Economy 入口及逐主张映射。

## 检查与构建

需要 Git、Python 3、make 和 elan。工具链和固定依赖使用本仓 `Lean/lean-toolchain`、`Lean/lake-manifest.json`。有既有缓存时直接复用；新克隆仅首次取回固定依赖缓存：

```sh
make bootstrap
```

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

`build` 实际构建全部五个入口及其完整生产／消费者闭包。`trust` 先让 Lake 核对当前源码的新鲜性，再沿所选声明的完整 type/value、互递归声明、归纳类型及 recursor 元数据检查标准三公理、`unsafe` 和 `partial`。`types` 使用既有完整 Lean Expr DAG 编码，独立重建并由 Lean 检查类型等价；映射中的 `complete_type` 指向固定验收类型。

`entry --require-ready` 核对本仓已保存的实际执行回执。自行重跑的结果写入指定目录，不自动覆盖固定回执。原始社会总口的公理身份为 `propext`、`Classical.choice`、`Quot.sound`。

`source` 按 epoch 输出公开原路径闭包，只需本仓材料。历史文档及 Lean 原源码可直接核对原 SHA；选集还包含经过路径清理的原认证回执，全部资源的原字节逆恢复需要按 `source_sha256` 命名的原件目录：

```sh
python3 tools/generated_society.py source --exact \
  --private-originals "$ORIGINAL_RECEIPT_ARCHIVE" \
  --output .local/society-exact-source
```

原件身份、允许的变换及原件缺失时的失败行为遵循 [source_view 原件规则](evidence-publication.md#两种视图)。公开证明构建使用上面的公开视图，不依赖私人运行路径。

## 默认覆盖与缓存

```sh
python3 tools/ci_plan.py plan
python3 tools/ci_plan.py coverage
python3 -m unittest discover -s tools -p 'test_*.py' -q
```

新增证明与五个论文入口均由 `GeneratedSocietyRelease` 唯一拥有，并进入真实默认构建。固定布局只追加新位置，不运行 `--rebalance`。逐片身份、旧材料保全、平台区别和科学输入比较见[缓存保全报告](../evidence/generated-society/acceptance/expanded-g0-g27/cache-preservation.json)。

本机使用 Darwin 缓存；远端完整分片存档具有 Linux 平台身份，不能相互冒充。本稿加入后完整选集指纹改变，必须由正式 CI 为新指纹取得新的完整验收；原 seal 不迁签。

`tools/export-map.json` 已接近公开单文件上限。本次仅去除 JSON 排版缩进以保持小于 100 MiB；全部值与数组顺序保留，科学回执未重新序列化。审阅实际接入差额可用 `git diff --ignore-all-space -- tools/export-map.json`。

## 原认证与新执行

e60 与 AB 的 active、原定理表、拒绝旗舰卡、复现卡和 regression 矩阵按原 epoch 保存。它们记录原 strict／T1 与 9722／9833 jobs 的历史验收。独立原始 JSON／日志未由这组固定来源恢复，因此以“原来源记录”列入映射；本稿 H0 构建、类型和 trust 由自己的新执行回执承担。

G13 的 strict 记载来自固定来源机制卡，保持原认证身份；本次 H0 的五包执行单独记账。补稿独立附录的 C13／PT15 receipt-window 接口沿用自身的未闭合记录，未计入 G13–G27 的验收结果。

Bell 与量子载体沿用原程序、配置、输入及成功回执身份，`full_replay=false`。本篇没有新增科学重算；原失败与过期 artifact 的状态分别保留在缓存报告中。

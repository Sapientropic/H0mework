# 过程核心第三版本地验收

C47–C48 的 721 个源码身份与 10 份历史 verdict 已通过公开恢复及原字节核对。8 个新 owner
接入默认构建，沿用已有 owner 的 14 个必要依赖进入默认目标。实际 Lake 构建、`--trust=0`
依赖核验和 66 项完整声明类型均通过。公理闭包为 `propext`、`Classical.choice`、
`Quot.sound`，核验发现的 `unsafe`、`partial` 和 `sorryAx` 依赖为零。
回执及固定来源见[逐项映射](source-process-core-v3-map.json)。

[展开与根读检查](../evidence/source-process-core-v3/acceptance/foundation-axioms.json)的
15 项声明中，14 项公理列表为空。`RootedAccountedUnfolding.cardinalShadow_parallelAt`
依赖 `propext`。

原 verdict 对应 CP122–126、CP128–131 和 CP136。CP132–135 的历史身份由固定纪元的
[检查点账本](../evidence/whole-ledger/original/Rba7e274b/Lean/docs/ledgers/living-law-framework-checkpoints-v32.md)记录，原 verdict 字节未取回。C49 复用 WA39 的公开
构建和类型回执，C48 的相关声明以本版 H0 核验回执为准。

[联合缓存保全报告](../evidence/whole-ledger-v2/acceptance/cache-preservation.json)登记默认构建
及历史成功分片。以上新证明验收在本地执行。

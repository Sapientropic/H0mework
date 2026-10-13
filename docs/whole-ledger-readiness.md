# 整账法证明包准备状态

固定材料提交：`f607eb646d4e9cddba3512755365842895af44ca`。源码、逐项映射、公开证据与以下实际验收由该提交绑定。

全局目标已完成：WA1–WA40 的完整生产证明、原直接消费者、imports／资源与公开复现闭包已在 H0 接收。来源上界固定为 `ba7e274beb1de38900a6fc2c8c8dfe6cfad9d9aa`；13 个历史环境保留各自 epoch，实例 8.7 使用 Y1，其余原 Y 材料保持原身份。

机器签收：公开来源核查和读者恢复通过；40 条 WA 的 772 项材料映射、5,752 个完整证明源码 owner、340 项资源均可从本仓恢复。13 个历史包的完整依赖构建、完整 metadata trust 与 5,025 个显式声明的无损完整类型核验全部通过，执行前后输入一致。39 份原控制保留 453 个具名声明和 424 个匿名 kernel 例子；审查公理限于 `propext`、`Classical.choice`、`Quot.sound`，unsafe／partial 依赖为 0。

这条证明链贯通同一源的完整账、真实请求 AST、实际有费执行与同债付款、完成回答、whole write／canonical next 和后继继续消费。WA38–WA40 的 47 个生产／消费者／控制入口与 66 个关键实际声明另有[本次范围认证](../evidence/whole-ledger/acceptance/scoped-certification/verdict.json)；原 Factory、initial、cfg、实际共尾 ordinal、环境、作用词和观察位置沿用原类型。

完整类型采用共享 Lean Expr DAG，并在 Lean 中从 JSON 重建、核对原 kernel 类型；具体表示与命令由[复现入口](whole-ledger-reproduction.md)说明。原／有效源码、失败字节、源补充和公开回执变换分别绑定 SHA，不将真实定义适配写成 namespace 改名。

本 checkpoint 的机器验收：`make check-whole-ledger-full` 全部步骤成功；`verify-map --require-ready` 与 `entry --require-ready` 通过，来源、资源、kernel 和 runtime 待付项均为 0。198 项工具回归通过；回执如实记录现有工作区缓存。

原认证身份由[逐项映射](whole-ledger-map.json)的 `original_receipts` 保存；未恢复的原 verdict 保留固定 ledger 的状态与原 SHA，本次 H0 验收独立登记。四篇既有版本与原 Y／Y1 的源码、资源字节保持；旧 map 和入口沿用既有含义。

权威入口：[逐项映射](whole-ledger-map.json)、[固定选集](../checks/whole-ledger-selection.json)、[导出身份](../tools/export-map.json)及[复现命令](whole-ledger-reproduction.md)。当前有限合同无待付项；正文与 PDF 由写作窗口另行接入。

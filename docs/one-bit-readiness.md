# 一比特证明材料

固定材料提交：`c40ef754ccbbea96f8c1417f12348e840da5eb82`；源码、OB 映射、control 映射与实际验收由该提交绑定。

目标：交付 OB1–OB11 所用已签证明包、精确历史来源与新增 ghost 反例 control。权威对应由[逐项映射](one-bit-map.json)维护，新增 control 的声明和实际验收集中在[控制映射](../checks/one-bit-control-map.json)。

已闭合：整账法 Y／MV4 两个历史包及首发核心 H、物理 H／F 三个历史包的完整源码范围与原验收一致；本篇复用 1,315 个具名审查根及 194 项资源。26 份选定源码可从公开目标精确恢复，原 epoch 与来源摘要保持。

新增原反例完整迁入：32 个源码身份中复用 31 个，只增加[ghost Regression](../Lean/H0mework/Checks/OneBit/ZeroLawRootAdmissionRegression.lean)。原 raw Bool 两值不等、相同合法状态／登记发生／完整演化，以及真正不同发生的正例均保留；17 个原 control 声明和直接消费的 6 个准入声明通过实际构建、完整 metadata trust 与完整类型核验。公理限于 Std3，unsafe／partial 为 0，输入未变。

两条 `True` 声明保留原 `fail_if_success`，检查非法 API 应用无法 elaboration；它们与独立的不等式／等式证明分别登记，不充当通用无魔法定理。OB1 的语义约定、OB11 的方法论综合保原贡献身份。

本 checkpoint 的机器验收：`make check-map`、`make check-one-bit-full`、`entry --require-ready` 与 32 文件完整原路径恢复均通过，28 项工具回归通过。原包按精确源码／审查根复用，新执行只核新增 control；[范围认证](../evidence/one-bit/certification.json)和[新回执](../evidence/one-bit/acceptance/)与旧回执分列。读者命令、原路径恢复及完整类型表示见[复现入口](one-bit-reproduction.md)。本有限材料合同无待付项。

额外阅读的 RootInquiry 文件和两份 F 上下文文件保留为未选语境，不用相同正文的 H 模块替换 F 环境。四篇已发表选集、原 Y／Y1 和整账法 map／回执保持原身份。

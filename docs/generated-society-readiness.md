# 典范社会总定理：选集与验收

[逐主张映射](generated-society-map.json)与[选集](../checks/generated-society-selection.json)覆盖 G0–G27、G2a 及实际引用接口。G10–G12 保持 `interface_only`；C.13／PT15 按原协议上下文独立验收。

## 本轮状态

完整七包本地构建、1012 个声明的 trust 与完整类型验收均已通过。构建耗时 189.546 秒，输入前后身份一致；完整 type/value 闭包仅依赖标准三公理 `Classical.choice`、`Quot.sound`、`propext`，`unsafe=0`、`partial=0`。全部类型均由 Lean 重建并检查等价。独立审查核对了实际回执、审计程序、日志及完整 owner／声明清单。

[本轮真实回执](../evidence/generated-society/acceptance/final-manuscript/summary.json)保存执行输入快照与最终类型绑定；`entry --require-ready` 已通过，核实 4091 个完整证明 owner、156 项公开资源身份和 1012 项完整类型。两次失败原件与[此前五包验收](../evidence/generated-society/acceptance/expanded-g0-g27/)分别保留，此前 967 项类型保持原身份。

| 检查 | 当前状态 |
| --- | --- |
| 七包完整 Lean 构建 | 通过；189.546 秒，输入身份保持 |
| 完整 type/value trust 闭包 | 1012 根通过；标准三公理，unsafe=0、partial=0 |
| 完整 Lean Expr DAG 类型 | 1012 项通过；owner／声明及内核类型等价一致 |
| 固定来源与包归属 | 29 主张、12 个来源 epoch；351 个 Lean 文件根、165 个资源来源键 |
| 原五包 source scope | 五个摘要均与此前实际验收一致 |
| 新生产接口 source scope | 562 模块，含独立入口 |
| 新协议接口 source scope | 635 模块，含独立入口 |
| 公开恢复与资源核对 | 4091 个证明 owner、156 项公开资源身份通过 |
| 默认覆盖与旧材料身份 | 通过；详见共用缓存报告 |

原五个入口、owner 与源码保留。新增 `H0mework.Papers.GeneratedSocietyProductivitySupplement` 和 `H0mework.Papers.GeneratedSocietyProtocolInterface` 分别承接本稿实际引用的生产消费者与协议接口；完整 producer、消费者和 imports 都进入各包范围。

## 固定来源

命题合同固定于 publish `d7253ee2c6db3ff52e709f78aa602ab0a6c921c5`。十份完整来源清单的全部 345 项与原有选集并集保留，包含 G13 的 df 当前来源实例和原认证资源。整理上限仍为 Homework `df421ff600085cbc290a7ae946193961bed7c83b`，各证明保留自己的实际 epoch。

publish 后续提交 `99860025b4c810011ef37d7e04c197fb6e7bf41c` 更新图件及双语图2图注；claims、逐结果对应、完整来源清单和附录字节保持，未增加证明根。本轮保持固定合同身份。

C.13／PT15 的真实原认证上下文为 `e0b980ffb69e638c9f1e000932f6bb14f778dcdc`。原 window 的 9 份检查源码、9 份 setup 和 8 份 olean 身份已恢复核对；原 61 个 parent 回执与 window 回执及支持文件共 68 项材料逐项映射。后置 custody 提交 `de213ed9d6ac05cf7acfd6ec2c974ce8c1df78d6` 只固定恢复原件的 SHA，不改写原执行身份。原 review 状态和 exit=1 的负例拒绝均保留；本轮 H0 执行单独记账。

本轮实际辅助来源另行明确：`Trace.Challenge` 使用固定6c版本补全 `scopeBoundary` carrier与第六事件分支；`Quota.Plan` 使用固定59df版本的真实 `memoryReady` 门控等式。它们是实际源修订。`Distributed.Regression` 则按实际 Code 的四个默认记忆字段作可逆依赖类型重绑定，保留原定理类型及证明。三个原坏体按4个来源键保于G12资源；[首轮失败](../evidence/generated-society/acceptance/final-manuscript/attempt-original-provider/)保留原错误、超时和执行输入。所选主根源码签名保持，本轮完整类型与公理依赖重新机器验收。

第二次完整构建只在 `Feedback.Regression` 的 signals=3 依赖域更新失败，[该次回执](../evidence/generated-society/acceptance/final-manuscript/attempt-feedback-defaults/)独立保留。现采用固定 `7e2cc053821fedbb638122b3b2f8c82134c61ac0` 中确有的四个默认字段重绑定版本（与59df同字节）；整份源文件的原定理类型、证明和其余字节保持，完整源与四项字段 `rfl` 检查已经通过。有限调用点扫描未发现其他同族漏项；修复后的完整七包构建、trust 与类型均由本轮实际执行签收。

## 缓存与远端

[当前缓存报告](../evidence/economic-constitution/acceptance/initial-intake/cache/current-report.json)固定选集指纹 `c3e4f6280b9b8b450e2aa582acde2547549d97162174c7da7d992434314e8bc8`，逐片记录本轮两稿接入：旧 52523 个模块及入口的源码／递归身份、63 个完整分片记录均保持；新增 2106 个证明 owner、7 个论文入口及 306 项资源，只追加两个分片。默认构建覆盖 53198 个模块，唯一 owner 与原六篇材料身份检查通过。

工具链、manifest、工作流、固定布局和缓存版本沿用项目机制；本机 Darwin 产物与 Linux 分片存档分别处理。Bell 与量子载体输入及原回执身份保持，`full_replay=false`，未重跑科学任务。

本轮尚无新提交的远端 CI 或新 seal。没有推送、远端合并、工作流触发、手工 seal／save／prune 或远端缓存删除。

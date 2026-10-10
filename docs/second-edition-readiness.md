# 第二版材料与验收

## 全局目标

交齐过程核心、同源物理旗舰与低能首发采用的生产证明、直接消费者、资源及成品，推送 H0 并完成远端 CI。第二版固定 `9c73a630ce05bea062ec889b188f5105c0afb796`；低能 L1–L28／Q1–Q6 固定 `71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9`。各历史证明与认证保持原 epoch；第一版 60 条主张继承 `234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a` 与[冻结映射](first-release-map.json)。Homework／写作仓只读。

## 已闭合的权威证明链

71e 的五个核心包已实际构建及完整审查，PR／C62／completion／full-stock／runtime 分别覆盖 361／202／38／128／58 根。Bell 新增证明 39 根、低能 Q3 材料 94 根、低能 AD／AE 1／286 根及第一版 GSR 适配后的 AD／AE／CAP 640／841／224 根均通过。全部签收范围保留完整声明元数据、Std3／unsafe0／partial0及各自来源摘要。

9c73 的 same-event-feedback、type-completion、full-stock-next 已独立构建及完整审查，分别覆盖 176／232／508 根，执行输入与 HEAD 前后一致。Type 覆盖 73,337 常量、2,047,952 依赖边；三包当前完整来源范围与实际回执一致，正式登记到第二版地图。

71e 的 charged-transfer 已独立构建及完整审查，覆盖 78 根、129,502 常量、3,449,931 依赖边，完整元数据与 Std3／unsafe0／partial0。稳定 `c762e7806b91e721d86e0938666e413765e6029a` 的执行输入前后一致，源码范围与当前包相同；原长构建的实际全局身份变化及其已支付对象分别保留。

9c73 的 registered-forcing 已独立构建及完整审查，覆盖 21 根、8,974 常量、144,130 依赖边，完整元数据与 Std3／unsafe0／partial0。稳定 `db4d0f1bb2caa84ad9a57767ae5c62c78f82cb52` 的执行输入前后一致，当前四个选定源及完整闭包与实际验收相同。

低能 13 个科学消费范围已签收：五项原消费者实际重放，八项继承固定原认证。Bell 三项消费者重放与完整比较通过，30 件冻结输入共 1,143,760,250 字节按原 SHA 恢复。两稿的[成品快照](../papers/low-energy-first-release/2026-10-09/README.md)保留四份双语 PDF、两个可编辑 ZIP 与原解包字节。

固定 9c73 八个 intake 的完整材料已提交为 `53779d64cf2215f87db80bbe59d8a98d4928e127`：新增 15,554 个源、728 件工件和 12 个聚合入口。真实 `make check-map` 通过 47,737 个逻辑源码视图，生产、消费者与资源身份缺项为零。CPS1 原 LAlanine／临床依赖与固定 Physlib 63 模块随完整闭包接入。

公开完整原路径恢复已实际核对 21,168 个源码布局、84 件工件、38 个嵌入资源与 178 条资源地址。低能九个新增视图的清单各补齐 23 个已有资源，全部实际恢复与 288 条地址检查通过；生成器的全部 20 个视图与应用清单相同。

## 这些闭合改变了什么

原计算读口、receiver 费用、factory 生成环境与有限 Incoming 已对齐；稳定合同见[源与环境接口](source-action-environment.md)。完整递归签名相同的视图共享声明 owner，同时精确恢复各原路径与原 SHA。

GSR 稀疏证明保留原定理及 kernel 检查，降低实际编译内存，九份旧副本的来源、内存调度与受影响包重验已同步。动态私有 owner 按真实环境定位；Jets／DiracRay 及同 namespace 的 charged 局部实例精确命名；prepared Ward 直接消费同一算子恒等式与实际左右 leg。原陈述、类型、数值、证明责任和预算保持，完整逆验与独立消费者通过。机制只在[证明构建适配](proof-build-adaptations.md)详述。

## 当前最高杠杆的结构责任

核心剩 9c73 runtime 的 740 根及四篇论文的完整构建／审查。原 `AdmissionStops` 已完成；runtime 的 13 个原生生产前沿覆盖 18,238 个模块，计算产出随后由稳定提交上的正式整包验收消费。

九个低能新增包需正式收尾。已通过的 24 目标补建保留；六份 DiracRay 修复消除已确认的联合导入冲突。九包所选 55 个生产模块由 15 个最高原生消费者一次支付共享依赖，随后逐包实际构建与完整审查。旧 prepared／signal 主包及独立认证消费者四包消费同批共享产出。

新 9c73 charged、prepared、signal 及两独立认证消费者继续验收。charged 的九个源／十一局部实例已修复联合导入重名；两原 owner、九个完整 canonical 源、原 Candidate／JointFacts 及完整联合 theorem 消费者共十四步实际通过。已命名的 Yukawa 源与六个其他 namespace 的局部实例保持。该修复与全部已签包、runtime、低能十五目标及新 GSR 完整源码范围不相交。新 GSR 原生构建已按原预算实际退出 0、完整 4,114 源前后一致；原全局身份变化记录保留，正式包验收消费该对象。原 charged／forcing 联合导入失败保持，forcing 已由独立 21 根验收签收；后续稳定验收消费现有对象。

远端 [CI 38015786104](https://github.com/Sapientropic/H0mework/actions/runs/38015786104) 已实际复用全部 42 个旧完整分片，附件 ID／大小／摘要保持；Bell、量子、规划及冻结证据通过。真实规划 47 片与本地一致。九源修复后的实际规划继续保持阶段 1–8 的 44 片全部八字段与缓存键，只改变 s9-01 及总选集指纹。当前阶段 8 两片继续构建并保存进度；等待其缓存落稳后推送下一批，整轮通过后签收 CI。

核心／物理第二版成品待写作侧 final；低能成品已完成，公开绑定待完整材料验收。成品按独立版本接入。

## 本 checkpoint 的机器验收

- 9c73 [same-event 构建](../evidence/second-edition/acceptance/core-9c73-same-event-build-20261010/result.json)／[审查](../evidence/second-edition/acceptance/core-9c73-same-event-trust-20261010/result.json)、[Type 构建](../evidence/second-edition/acceptance/core-9c73-type-completion-build-20261010/result.json)／[审查](../evidence/second-edition/acceptance/core-9c73-type-completion-trust-20261010/result.json)、[full-stock 构建](../evidence/second-edition/acceptance/core-9c73-full-stock-build-20261010/result.json)／[审查](../evidence/second-edition/acceptance/core-9c73-full-stock-trust-20261010/result.json)。
- [低能 24 目标补建](../evidence/second-edition/acceptance/low-24-focused-build-20261010/result.json)、[独立 coframe／adjoint 消费者](../evidence/second-edition/acceptance/physics-direct-coframe-adjoint-build-20261010/result.json)及[Dirac／GSR 联合消费者](../evidence/second-edition/acceptance/dirac-ray-owner-consumer-compatibility-20261010/result.json)按各自实际范围签收；[原导入失败](../evidence/second-edition/acceptance/low-e055-selected-proof-failed-20261010/result.json)及[原三包身份变化批次](../evidence/second-edition/acceptance/core-9c73-three-package-drift-failed-20261010/result.json)保持原结果。
- 71e charged [构建](../evidence/second-edition/acceptance/physics-charged-transfer-build-20261010/result.json)／[完整审查](../evidence/second-edition/acceptance/physics-charged-transfer-trust-20261010/result.json)、[原长构建身份变化](../evidence/second-edition/acceptance/physics-charged-transfer-drift-failed-20261010/result.json)及[新 9c73 十四步完整联合消费者](../evidence/second-edition/acceptance/physics-new9-instance-consumer-compatibility-20261010/result.json)均保留原执行与源码。
- 9c73 forcing [构建](../evidence/second-edition/acceptance/physics-9c73-registered-forcing-build-20261010/result.json)／[完整审查](../evidence/second-edition/acceptance/physics-9c73-registered-forcing-trust-20261010/result.json)、[原联合导入失败](../evidence/second-edition/acceptance/physics-9c73-charged-forcing-failed-20261010/result.json)及[GSR 原构建身份变化](../evidence/second-edition/acceptance/physics-9c73-gsr-native-drift-20261010/result.json)按实际范围分列。
- [固定 9c73 完整公开恢复](../evidence/second-edition/acceptance/fixed-cap-9c73-public-source-view-20261010/result.json)与[低能九视图资源修复](../evidence/second-edition/acceptance/low-reader-resources-candidate-20261010/result.json)保留原缺项、全部恢复及生成器的实际记录。
- [当前 CI 真实规划](../evidence/second-edition/acceptance/ci-actual-plan-38015786104-20261010.json)、[科学回执复用](../evidence/second-edition/acceptance/ci-scientific-reuse-38015786104-20261010.json)、[42 片实际完整复用](../evidence/second-edition/acceptance/ci-old42-reuse-38015786104-20261010.json)及[九源修复后阶段 1–8 保持](../evidence/second-edition/acceptance/cache-preservation-new9-actual-ci-20261010.json)。
- [完整材料落地](../evidence/second-edition/acceptance/fixed-cap-9c73-material-apply-20261010.json)、[11 源修复缓存核验](../evidence/second-edition/acceptance/cache-preservation-coframe-ward-20261010.json)、[远端真实规划](../evidence/second-edition/acceptance/ci-actual-plan-38012233973-20261010.json)、[41 片实际复用](../evidence/second-edition/acceptance/ci-old41-reuse-38012233973-20261010.json)及[s7 完整存档](../evidence/second-edition/acceptance/ci-s7-complete-38012233973-20261010.json)。超限日志、引用及未推送历史已修复并推送，[原执行标签](../evidence/second-edition/acceptance/local-history-rewrite-20261010.json)保留。

最终验收是两份 `verify-map --require-ready`、[四篇论文实际构建／审查](edition-reproduction.md)、有限成品交接及实际提交的远端 CI 成功。

## 权威源码入口

[第二版逐项映射](second-edition-map.json)、[低能逐项映射](low-energy-release-map.json)登记生产声明、直接消费者、程序、资源及原／派生验收。[版本复现](edition-reproduction.md)提供构建、完整审查、原路径恢复与科学消费命令。

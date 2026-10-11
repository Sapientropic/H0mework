# 第二版材料与验收

## 全局目标

交齐过程核心、同源物理旗舰与低能首发采用的生产证明、直接消费者、资源及成品。先交付论文可引用的固定源码绑定，整包 kernel 验收与远端 CI 分别继续签收。第二版固定 `9c73a630ce05bea062ec889b188f5105c0afb796`；低能 L1–L28／Q1–Q6 固定 `71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9`。各历史证明与认证保持原 epoch；第一版 60 条主张继承 `234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a` 与[冻结映射](first-release-map.json)。Homework／写作仓只读。

## 已闭合的权威证明链

71e 五个核心包与 charged-transfer、Bell、低能继承 AD／AE、第一版 GSR 适配范围已有真实构建及完整声明审查。9c73 的 same-event-feedback、type-completion、full-stock-next、charged-transfer、registered-forcing 已独立签收，根数分别为 176／232／508／560／21；原回执及 Std3／unsafe0／partial0 身份保留在各包映射。

固定 9c73 八个 intake 的完整生产、消费者与资源已迁入，公开原路径恢复覆盖 21,168 个源码布局、84 件工件、38 个嵌入资源与 178 条资源地址。最终 L23 改绑固定 c62 原单位修复，完整四源、13 根消费者、原认证及 23 件资源已接入；公开 CLI 实际恢复 5,098 文件和 32 条资源地址。低能 13 个科学消费范围已签收，两稿四份双语 PDF 和两个可编辑 ZIP 保存在独立[成品快照](../papers/low-energy-first-release/2026-10-09/README.md)。

ActualEffective 九份适配已逐环境完成真实 Lake 全模块／CoefficientPrice 构建、freshness 和六条原陈述消费者，共 27 步全部退出 0，执行输入及消费者对象稳定。单线程可比 R71e 峰值 RSS 从 21.3 GiB 降至 9.1 GiB；九环境公开构建峰值为 8.95–9.21 GiB。原定理、定义、预算及完整源码逆验保持。

四篇论文的 49 条选定主张已绑定公开源码 `643721f170e563ee607329ac55c951aabad3e1b1`，写作选择固定 `6850c9501e55786ce1701a7310a253ae49c2b868`。第二版 15 项与低能 34 项的源码身份、资源、运行材料缺项均为 0；[固定绑定导航与双语可得性表述](source-materials.md#四篇论文的源码绑定)沿用固定写作选择，源码修复提交 `643721f1` 的四个 EM audit 均实际编译通过。原 `b9d66048` 绑定保留为历史固定导航。

第一版 AE／CAP 在 `b9d66048` 上的实际整包 build 与完整元数据审查均通过：分别为 841／224 根、Std3、unsafe0、partial0，执行输入不变。新回执已本地归档，冻结第一版 map 保留原身份。

## 这些闭合改变了什么

原计算 reader、receiver 费用、factory 环境与有限 Incoming 已对齐；[源与环境接口](source-action-environment.md)维护稳定合同。GSR 与 ActualEffective 的证明适配减少实际内存；匿名实例、动态私有 owner、prepared Ward 与共享 carrier 按真实类型接线。详述集中在[构建适配](proof-build-adaptations.md)。

GT 六份原程序的双 provider owner 已可逆修复，原完整 kernel 消费者与当前应用分别保留，83 项工具测试通过。它影响 17 个待验包，已签 33 包、runtime 与 charged 不相交。公开目标由下一正式包构建消费。

## 当前最高杠杆的结构责任

低能稿 2 的 `b9d66048` 整包 build 正在执行；先保存它的真实终态，再进入下一源码 cohort。低能稿 1 的实际整包 build 失败于四个 audit 的导出模块名和三次 Mathlib 文件读取错误（ENFILE）。四 audit 的可逆修复已在独立提交树完成原参数编译，精确影响 E055／C62 两个低能包；本轮 build 终态后应用该树，利用现有热缓存重验低能稿 1，并完成两稿与两篇第二版的整包 build／trust。实际通过后登记回执，执行两份 `verify-map --require-ready`。

写作提交 `6850c950` 的最终成品已按原 SHA 核验：第二版 10 份 PDF／751 页、两份可编辑 ZIP 与两个 arXiv 源包；低能两稿四份 PDF／241 页与两份可编辑 ZIP。当前 build 终态后，将成品与已通过回执独立接入 `2026-10-11` 版本，不等待剩余整包队列；原低能 `2026-10-09` 快照保留。

远端已自动进入 [CI 38154135554](https://github.com/Sapientropic/H0mework/actions/runs/38154135554)，HEAD 为导航提交 `e9734c69`，源码仍为 `b9d66048`。前轮 [38129862129](https://github.com/Sapientropic/H0mework/actions/runs/38129862129) 到达既定构建时限后退出 75，最终 s8-01 续跑缓存已保存。该轮实际复用了 41 个旧完整分片，s7-01／s8-02 的新完整分片已完成并上传；s9 尚待执行。自动续跑已实际复用 43 个完整分片（41 旧分片加两个新完整分片），原 43 份完整缓存全部保留。[缓存合同](../evidence/second-edition/acceptance/actual-effective-ci-cache-preservation-20261011/cache-preservation-effective-gt.json)中的 compatibility、分片位置和顺序保持；四 audit 修复只改变 s8-01 及完整选集指纹。ActualEffective 内存表向上取整为 9.3 GiB，单编策略与原 import 顺序保持，28 项 focused 测试通过。

## 本 checkpoint 的机器验收

- [原可比测量、失败尝试及最终正常 kernel](../evidence/second-edition/acceptance/actual-effective-proof-measurement-20261011/result.json)、[完整 Price／六原陈述消费者](../evidence/second-edition/acceptance/actual-effective-proof-consumers-20261011/result.json)。
- [九环境实际公开 Lake 验收](../evidence/second-edition/acceptance/actual-effective-nine-public-build-20261011/result.json)、[九源应用／完整逆验／原 52 包范围](../evidence/second-edition/acceptance/actual-effective-nine-application-20261011/result.json)。
- [GT 六源应用与当前交集](../evidence/second-edition/acceptance/gt-six-owner-application-20261011/result.json)、[原完整 kernel 消费者](../evidence/second-edition/acceptance/gt-owner-original-kernel-consumers-20261010/result.json)。
- 已签包的构建／完整审查与精确来源摘要由下列映射链接；原失败和已付对象保持原身份。超限日志及未推送历史已修复，[历史替换回执](../evidence/second-edition/acceptance/local-history-rewrite-20261010.json)保留。

## 权威源码入口

[第二版逐项映射](second-edition-map.json)、[低能逐项映射](low-energy-release-map.json)登记生产声明、直接消费者、程序、资源与原／派生验收；[版本复现](edition-reproduction.md)提供完整执行命令。

# 第二版材料与验收

本轮接收过程核心、同源物理旗舰第二版，以及低能首发 L1–L28／Q1–Q6。新增收稿上限固定 Homework `71e94e8261d67cf4849a05eb14ac95aa2f7dcbb9`，各历史证明与回执保持自己的实际 epoch。原 60 条首发主张继承 `234817b3c3f7a1023226e7a4fdb8660ddcbc9d0a` 与[原映射](first-release-map.json)。逐项生产、消费者、资源和结果由[第二版映射](second-edition-map.json)与[低能映射](low-energy-release-map.json)登记，命令见[版本复现](edition-reproduction.md)。

## 机器签收

- 两份 map 的公开身份已实际通过：第二版 11 条新增主张、低能 34 条主张，生产／消费者／资源身份缺项为零。旧 25,362 个模块与 2,225 件工件的字节、主来源及公开变换保持；来源兼容只追加已核实的同字节 epoch。
- 核心 C39–C41 三个公开包已编译并完成独立声明审查：38／128／58 个根，完整声明闭包分别 13,701／57,545／75,718；类型、值、归纳与 recursor 元数据均已检查，trust0／werror、Std3、unsafe0／partial0。见[新公开回执](../evidence/second-edition/acceptance/core-cap-trust-20261009/receipt.json)。
- 四组物理原路径已从 H0 公开材料恢复。Bell 原冻结资源 30 件、1,143,760,250 字节全部按原 SHA 恢复；实际运行追出的动态 import／源登记依赖逐件补入，未执行新的求解。
- 原远端 CI 的 25,404 个模块、29 个资源及 42 个旧分片完整身份保持；新增 6,885 个默认模块只追加到两个阶段 8 分片。见[缓存保留回执](../evidence/second-edition/acceptance/cache-preservation-20261009.json)。缓存与 private-owner 工具的修正已在 `04067b1bcce9828f93e0d670fa473e6bfc39b076` 本地提交，39 项公开变换测试和 21 项缓存测试通过。

## 当前验收责任

完成尚未验收的实际生产／直接消费者构建和独立声明审查；核心 PR／C62 深依赖正在编译，物理与低能的无重叠入口在另一组 focused 构建中。C62 的 L24–L25 复用前者已付依赖后验收。保留实际耗时、缓存和原失败身份，再按固定原程序完成必要的有限消费者检查。

核心历史 `InventoryTransport.born_kernel_member` 的 rewrite 失败已有收稿上限前的纯证明修正；两次声明的类型、前提和原主张来源保持。`source_origin`登记实际补充提交，原源码与[首次失败记录](../evidence/second-edition/acceptance/core-build-failure-20261009/result.json)分别保留。核心原 61 份认证材料已迁入；CP36／CP37 的原不可变 verdict SHA 与 counts 来自固定 ledger，新的公开声明审查独立签收。

本地源码阶段提交完成后，按独立版本位置接入低能两稿已交双语成品。过程核心／物理旗舰第二版成品由写作窗口 final 后接入；本仓不改写作仓、不推送或发布。成品中的代码绑定以写作窗口实际回填为准。

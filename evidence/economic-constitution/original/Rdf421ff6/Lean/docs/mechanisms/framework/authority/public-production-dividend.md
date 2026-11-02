# 源生物量红利与持续开放复制

当前责任见[社会线 active](../../../handoffs/process-generated-society-active-route.md)；能力索引经[协调机制](source-generated-coordination-protocol.md)到达本卡。

## 原始输入与两个实际发生

`Productivity/Dividend.input n shared` 从同一个 `OpenReplication.law n`、初始库存和零 claims 生成两条独立 root 历史。
`shared` 选择首个原始程序，不向输入提供成功计划、红利或后继。观察报告与物量发射共用 `dispatch`。

原 law 明示：私有批次管理消耗燃料 `n+2`，开放消耗1，生产者生产消耗1，原维护消耗1；
接收者在开放技术下复制的边际燃料消耗为0。燃料和服务品是不同 Good；不把两种数量相加。
这些是具体成本族的原语，比较对象是其排他程序，不是所有市场机制的最优值。

## 首窗完整任务与严格燃料红利

共同 `task n` 在时窗 `[1,2]` 要求接收者完整使用服务品 `n+1`，生产者完成维护1。
两路全部 actual items 通过原 `Valid`，逐 Party／Good 的完整借记和贷记由实际 receipts 生成。

| 首窗实际量 | 排他路线 | 公共路线 |
| --- | ---: | ---: |
| 接收者服务品使用 | n+1 | n+1 |
| 生产者服务品转出 | n+1 | n+1 |
| 生产者燃料总借记 | n+4 | 3 |
| 燃料贷记 | 0 | 0 |
| 末燃料库存 | 1 | n+2 |

`dividend n` 定义为两条首窗实际燃料借记之差，输出 `n+1>0`。
开放和维护已入账；源中没有发债、结算或额外材料动作。单位 `u` 就是燃料，不输入估值权重或兑换表。
服务品的全部借记／贷记在两路相等，直接消去。

## 用同一库存付款，再持续生成服务

visit2 从自己的实际燃料生成 `maintenanceBudget = floor(stockFuel-1)`，发出相应数量的单位维护请求。
排他路线预算0，公共路线预算 `n+1`；每笔原请求合法，每个中间截点前后均保燃料≥1。
共同窗口 `[2,3]` 后两路全部库存相同、claims为0、时钟为3。

`extraDebit` 差恰等于首窗红利。首窗节省、visit2前库存差和visit2付款是同一份燃料；
`saved_fuel_equals_spent_dividend` 证明两窗累计燃料借记相等，禁止把它们相加为两份收益。
追加维护付款不冒充另一份生产红利。

从visit3起，源每轮都在当前状态检查候选 `[personalCopy, consume n]`：

- 开放路线实际发射两项原请求，每期生产并使用服务品 `n+1`，新增燃料借记0。
- 排他路线的原候选index0因许可拒绝，`Access.respond`生成refused，实际词为空；被拒候选没有作为物量操作执行。
- 对所有 `later : Nat`，自己的 `currentAt (3+later)` 保燃料1、零claims、同一技术与正确时钟；每期公共服务在 `[3+later,4+later]` 实付。
- `Openness` 从原必要使用item识别真正recipient，再逐access item排除private phase；每一期公共实际词均无完整 `CapitalRelationKernel`。

这是本零边际复制原语下的持续服务发生，不依赖额外补给。它不把整个社会的逐期维护约束从首窗推演出来。

## 原根与消费

`Runtime.Certificate` 保存首窗任务／全成本／正红利、visit2当下预算／实际词／逐cut底线、实际付款和不重复核算恒等。
`AccessCertificate` 保存源选择的Response、实际后继词、每期原服务与全部费用读数、无完整资本关系、原行报告和literal next。
两者经同一原根的 `dividend/access` coface 安装。

`taskWrite` 的destination与该实际visit原 `.instruction 0` 的destination具有机器证明的同一身份。
两条source各有自己的整账；具名 `LivingLawPublicDividendInstance` 在实际visit2及所有visit `3+later`
消费证书、原行收据、whole-ledger及自己的next。`LivingLawPublicProductivityInstance` 导入此入口，使其进入active graph。

该证明属于 `OpenReplication` 成本族；Cell自己的严格劳动红利见[实付方法复用](public-production-shared-audit.md)，完整 `ArtifactZero` 由社会线active继续承担。

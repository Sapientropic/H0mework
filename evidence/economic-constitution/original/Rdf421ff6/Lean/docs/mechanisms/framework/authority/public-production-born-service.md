# 实际出生生成新生服务责任

当前责任见[社会线 active](../../../handoffs/process-generated-society-active-route.md)；原细胞与劳动红利见[共享库存细胞](public-productivity-cell.md)、[实付方法复用](public-production-shared-audit.md)。

## 同一实际发生中的生产细胞出生

`Cell.SharedAudit.Born.itemsAt` 从 SharedAudit 自己的 `frameAt／wordAt` 取原 items，并逐访问证明等于同一 root 的实际 raw execution。
`recognizeBirth` 只接受原 items 中已经合法执行的本人签署种子转移：父方与接收者不同、接收者原种子为0、实际 seed credit 与转移后种子均为正。
角色3执行的是废料回收技术，不属于该种子生产 recipe，故明确排除。

每枚 `Birth` 保存原 ordinal／item、双方、转移包、Valid、签署与实际库存变化。
`instructionOrigin` 经原 `RootFace` 解码回同一 item；原 `.instruction 0` 的任务写回与该访问的 literal next 同时保留。
`birthKey = (ordinal, item.index)` 标记这次生产细胞的出生事件，不把 Party 数字本身当作出生来源。

截至 frame11，源生成四枚出生：

| 原 visit／item | 实际转移 | 首产与首轮服务 visit |
| --- | --- | --- |
| 4／1 | 0 → 1 | 6 |
| 7／0 | 0 → 2 | 8 |
| 9／1 | 1 → 4 | 9 |
| 10／1 | 2 → 5 | 10 |

四枚原坐标互异；首产 item 均合法、发生在自己的获种子之后，并使用该细胞实际持有的正种子。
这些是同一共享库存中的生产细胞出生，未重置世界或复制初态。

## 准入在出生时，归档由后续实际付款决定

原六服务槽已经覆盖0／1／2的启动生活与维护；它们继续保原 archive。新义务是各生产细胞获种子后的首轮服务，不能用启动旧款冲销。

每枚出生独立生成两个固定槽：生活品1／necessity、维护品1／maintenance。
规则在出生时确定，时窗从出生 item 的 clock 起，到该 clock+3；准入只消费出生、实际 seed credit、原指令及原任务行，不读取未来付款。
协议原指令 seat 承担该义务，受保护者是接收细胞；它不指定强制劳动者。

`payments` 从各自原 word 搜索合法的精确 `.use child goods purpose`：

- `Later` 比较 visit 及同词 item index，排除出生前或出生项之前的付款。
- `Window` 同时核对实际 word 的 before／after 时钟；deadline 不随重试刷新。
- 必须整包、正确承担者、正确用途并通过原 `Valid`；库存余额、完成标签或半额款都不能生成归档。

`Native` 直接使用通用 `NativeResponsibilityProcess` 内核。出生生成 `.admit` 和 live 槽；每个实际后续访问生成 `.cross`：
原词无匹配款则 maintained，有原款才 fulfilled。完整依赖 Run 满足：

```text
live     ↔ 从出生起的已检查访问均无实际付款
terminal ↔ 已检查访问中存在实际付款
archive  = 第一张原付款，所有有限后继保同一 terminal 整态
```

服务 lineage／incidence 是 `(birthKey, kind)`，不能跨出生事件借用责任身份。
原物量词不重放，新增的是这些原发生自身生成的责任准入、处置与完整 Run。

## 本拍出生清单决定具名责任面

`births count` 由原 prefix 中的实际 items 生成；`every_generated_birth_is_in_the_prefix` 给出原 ordinal < count。
`Runtime.Face ordinal` 的 newborn 索引是 `Fin (births (ordinal+1)).length`，由本拍实际 word 及过去 word 共同决定；没有未发生出生的索引。
每个源选出的出生有两项 face，`discovered_has_arrived` 证明其已经到达本拍。

具名 `publicBornCellFacade` 从唯一 seed.advance 激活。每个 newborn 面在同次原访问消费：
出生原 item、当初 live admission、到本次实际 after 的新服务完整 Run、旧六服务 Run、全金融矩阵、原任务行及 own next。
它继承 SharedAudit 的 method／dividend 与旧服务面，`original_root_is_preserved` 为 rfl；不建立第二个生产 root。

visit10 的 family 面进一步消费四枚出生、八个已经实付的 terminal 槽、实际首产、任意有限后继首 archive 保持，以及原严格劳动红利1和完整 carrier 差。
这把新增细胞的首轮责任带进原根；实际退出／挑战续行见[参与机制](public-production-participation.md)，两个独立全合同 verifier 继续按 active 的总合同生成。

## 关键反控

伪造种子签署者被原 law 拒绝；启动旧款不能结清新生服务。
实际等待前缀中的新槽保持 live。删除 replay 数据中的 necessity 项或改为半额，生活槽拒绝而维护槽仍接受；
把原付款数据放到窗外访问不能刷新 deadline。低层 replay 数据只有认回原 source items 后才可进入 native 付款证据。

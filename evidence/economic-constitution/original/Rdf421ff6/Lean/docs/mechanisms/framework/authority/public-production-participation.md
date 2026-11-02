# 公共细胞的实际退出、拒绝与重返

当前责任见[社会线 active](../../../handoffs/process-generated-society-active-route.md)；实际出生与严格劳动红利分别见[新生服务](public-production-born-service.md)、[实付方法复用](public-production-shared-audit.md)。

## 原动作语言中的本人请求

`SharedAudit.Participation` 保持 `Cell.law`、初始库存、捕获词和原任务。协议请求由本人签署、空 consent、revision purpose、精确 gates 与劳动 bundle 编码；`decode` 检查全部字段。
重复 revision gate 的次数是安装在 source-root 面上的协议编码，原 RawLaw 继续独立检查签名、权限、资源与实际借记。

| 命令 | revision gates 数 | 实际劳动成本 | 协议效果 |
| --- | --- | --- | --- |
| accept | 1 | 1 | 本人加入或自愿重返 |
| challenge | 2 | 2 | 复核，保原准入 |
| exit | 3 | 1 | 释放本人的工作角色 |
| refuse | 4 | 1 | 未加入者拒绝角色 |

注册表由本源每拍实际 raw items 顺序 fold 生成。只有精确解码、本人 standing 允许且原 law 接纳的 item 才更新本人位置；其他签署者不能更新你的 standing。
`CanRun` 允许 released／declined 本人重新 accept。该注册表控制自愿角色派工，不是公共机器的生产许可。“自愿”在本模型中指本人自签并保拒绝／退出后的重返选择；这些实际动作由source程序排定发射。

两条 source 分别保自己的 input、report、原行及 root。visit11 之前实际物量前缀与各自 Cell／SharedAudit 基线相同；共同 raw cut 不生成不同报告或 root 相等。

## 真拒绝、真退出以及退出后的生产

本源从实际 raw current／注册表生成以下请求与供料，不由调用者提供成功状态：

| visit | 原执行与后继 |
| --- | --- |
| 11–13 | 母源实付供料；1本人付劳动1加入，再付劳动2复核 |
| 14 | 再次本人复核；当前劳动0，原 item 真实拒绝、借记为空、raw step 不变 |
| 15–16 | 3实际补劳动2，随后复核实付 |
| 17–18 | 3实际补劳动1，随后本人退出实付，standing 变 released |
| 19 | 2本人实付拒绝，standing 变 declined |
| 20–21 | 母源实际补料；此时审计1合法且付得起，但两个本人均未任职，实际派工词为空 |
| 22 | 已退出的1实际完成自己的生产、生活和维护，种子净增2 |
| 23–24 | 3实际补劳动1，1本人付费重返，standing 重新 active |

缺料复核的原 item 保在实际 trace，不能记成付款。退出时可工作却不派工，区分了本人拒绝与物理无能力；退出后的实际首循环证明生产不依附该角色。

## 原生完整边界 Run

`Native` 的准入来自 visit12 本人实际 accept 和劳动1借记；scope／bearer 是本人，lineage／incidence 保该准入的原坐标。
内容是共同复核角色，residual 为空包；原六项服务和新生服务由自己的责任账保留，不把未来强制劳动塞进准入。

每个边界保存自己的实际 `Message`，其原 item 经本源 `RootFace.original` 精确解码。实际依赖 Run 的完整历史读出为：

```text
admitted → maintained → deferred → maintained → bearerRelease → maintained
```

接受的复核维护原责任；拒绝只 defer；实付 exit 由实际注册表释放生成 `jurisdictionEndedWithResidue`。
release 保原 admission／live 角色槽及完整 Run，并携同源旧服务 histories、全金融 Run、该次原任务行与自己的 next。
重返沿原责任继续，不借新 admission 擦除旧记录。

原六服务的首 archive 在所有有限后继保持。四枚历史出生的八项服务保原 native Run／首付款 archive；共同实际前缀把出生和付款 item 认回新 source 的原指令，保两边自己的来源，不把不同 root 强写相等。

## 25帧完整成本与后继能力

全部本人命令、缺料拒绝、供料转移、自主生产和重返均计入两条路线的同一25帧核算。
对每个 Nat 地址、每种 Good：贷记相同；借记只母细胞劳动少1；完整末 carrier 恰好多同一劳动1。
拒绝成本为0，已付款不复用，供料也没有重置库存。因此严格劳动红利仍为 `1 > 0`。

所有实际 item 前后，原三人和已获正种子的细胞均保生活／维护库存底线；所有清单外 Nat 地址逐 Good 库存为0。
原 raw 债的 native 金融账户／完整 Run 保持，全地址 claims 精确相等；frame25 原本金已归档。
任意旧末态合法有限词在新末态仍逐项合法，执行后完整 carrier 仍多劳动1；所有后续实际 current 保开放态，任意词无完整资本 kernel。

## 同一原根消费

新 runtime 从 `NativeService.Runtime.root (Participation.source true)` 安装自身 coface；继承的是自己 source 的原根。
每个 `ordinal ≥ 12` 的 dialogue 面消费到本拍的完整边界 Run、旧六 archive、金融矩阵／完整 Run、原任务行与 literal next。
visit24 的 complete 面联合消费实际释放／拒绝／重返、自主生产、八项历史服务运输、全Nat逐cut底线、完整25帧红利及全部旧合法后继能力。

具名入口是 `LivingLawPublicCellParticipationInstance.publicCellParticipationFacade`，经旧 Productivity／Outstanding 入口进入 active graph；readout、whole-ledger 与 generated next 同次因子化。

同一25帧的两路独立验收与本源新生责任重放见[双路验收](public-production-artifact-zero-audit.md)。

## 关键反控

改签名、加 consent、删 gate、改 purpose 或成本 bundle 不解码；另一签署者不能修改本人 standing。
真实缺料复核不扣库、不释放责任；退出与拒绝保重返路径。派工空词时原 law 确认审计仍可支付；退出后实际生产和维护通过。
完整成本差从25帧原 receipts 重算，未沿用11帧终点作为新成本结论。

# 共享库存的公共生产细胞

当前责任见[社会线 active](../../../handoffs/process-generated-society-active-route.md)；能力跃迁见[公共任务 ledger](../../../ledgers/society/public-function.md)。

## 原始载体与生成

`PublicFunction/Productivity/Cell` 的一个 `OutstandingSource.input` 保存自然数参与者地址、七种 Good、实际库存、claims、技术和时钟。
母细胞0、子细胞1／2、共享库存与回收角色3、后代4／5／6／7共用这一条历史；出生不重置库存，也不复制另一个初态。
种子、原料、生活品、维护品、废料按声明的材料数量核算；能源和劳动分别记账，不与材料相加。

前十个 visit 的 `candidate` 从当前阶段生成 primitive 请求，`Cell.respond` 在每个请求自己的中间状态检查原 `RawLaw.Valid`；不输入成功计划或目标库存。
该局部 admission 接受时发射候选词，拒绝时保留候选非法性的证明并发射空词；十次之后由下面的同源反馈接手实际发射。

| 实际 visit | 原操作与后果 |
| --- | --- |
| 1 | 从零债发行／放款1，支付三人各自的生活与维护，生产因机器准入被拒 |
| 2 | 母细胞支付能源1、劳动1，实际开放机器 |
| 3 | 母细胞生产种子1→3，实付原债1及本轮生活／维护 |
| 4、7 | 母细胞各付审计劳动1、转出新种子1；共享库本人请求交付真实投入品给子细胞1／2 |
| 5 | 子细胞1支付原料1、能源1、劳动1并实际更新技术 |
| 6、8 | 两个子细胞各自首产、支付生活与维护，种子各为3 |
| 9、10 | 子细胞各付审计劳动1、交付完整种子／投入／生活／维护包；下一代4／5各自首产并实付生活／维护 |

复制词中只有复制者与新细胞的本人请求，没有母细胞或库存提供者的签字入口。
`valid_debits_only_the_signer` 对任意 current、任意合法请求证明每个物量借记只落在请求本人；开放机器不赋予扣取他人库存的权限。

## 生成的不变量与独立消费

- `actual_copy_word`、`actual_seed_and_first_cycle`、`actual_second_generation`：实际发射、母源种子与两代首产／实付认回同一个 source。
- `every_migration_cut_keeps_the_original_bearers`：全部实际操作前后，原三名承担者各保生活品≥1、维护品≥1；新一代从实际得种子起也保同一底线。
  六个原服务槽有实际首付款，`original_service_archives_survive` 在任意有限后继保其 native archive。
- `opening_and_research_are_paid` 与 `finite_material_and_work_account`：开放和技术更新均实际扣库；整个有限过程能源借记7、劳动借记11，材料83→66，末态种子11、废料1、原债0。
  材料减少17由生活／维护消耗16及技术更新原料1组成，不把这些消耗叫材料毁损。
- `receipt_fold_matches_actual_inventory`：第二消费者把原实际 receipts 的 debit／credit 汇总，与全部六人、七种 Good 的末库存逐项对账。
  `Feedback.Accounting` 将其提升为任意有限长度、任意自然数地址、任意 Good 的累计收据对账及完整有限库存支持；不向检查器输入目标余额。
- `missing_physical_seed_is_not_compiled_away`：只删初始种子仍实际付开放成本，但生产被拒、实际空词、原债1与原料24保持。

## 从原始库存条件生成复制

`Copy.lean` 将方法提升到本原 law 的任意 current、不同复制者／接收者（接收者不是共享库角色3）。`CopyResources` 只输入公开改进技术、复制者库存下界和接收者逐 Good 非负；不输入合法计划、目标库存或未来补给。

| 原始资源条件 | 同一 `law.next` 生成的复制者净变化 |
| --- | --- |
| 种子≥2、原料≥8 | 种子−1、原料−8 |
| 能源≥1、劳动≥2 | 能源−1、劳动−2（审计1＋交付的生产劳动1） |
| 生活品≥2、维护品≥2 | 各−1，实交接收者启动包 |

`resources_generate_legal_copy` 输出五项全部合法和上述六项成本，接收者种子／生活品／维护品净增3／5／1。
`resource_generated_copy_pays_child_services` 从同词原 execution items 生成真实生活／维护付款；所有金融位置按任意 instrument／debtor／creditor 外延保持。
`physical_resources_generate_the_copy_request` 生成原 `IncomingWord.check` 的 admission。具名 Track 从实际 visit9／10 的库存证明资源条件，将这枚 admission、原实际词、效果、服务、原账与自己的 next 同次消费。

`attemptCopy` 对任意输入扫描原候选词：成功输出复制词；失败保存具体候选 item、原成员身份和 `¬Valid`，发射空词，所有金融位置保持。
拒绝 item 的 before 是检查候选前缀所得状态；blocked 没有实际执行该前缀，也没有支付模拟审计成本。该拒绝不是其他方法都不可行的 no-go。
`CopyRegression` 在实际 visit9 库存上显式改劳动：2成功、1在候选 index1拒绝、0在index0拒绝；失败发射后的库存／claims保持。

## 实际后果驱动供料、再生与下一次复制

`Feedback.respond` 直接成为原 `source.completionReport` 的 emitter。visit>10 时从当前库存扫描 `[0, round+5]` 内持有正种子的最大地址，接收地址为 `max 6 (parent+1)`。
它检查当下 `CopyResources`：足料发射原复制词；缺料则按实际执行后的库存生成修复词。调用者不提供成功词、目标 current 或未来补给。

修复先提交 `attemptCopy` 所找到的第一个拒绝项及其原候选前缀；`rejected_candidate_is_in_repair_execution` 把它认回本次实际 execution。
随后按已经执行的前缀，补到完整六项资源预算；供料仅来自0／3的现存库存，非共享库的种子／生活／维护各保留1。
不能只补第一个拒绝项，否则审计劳动每轮耗1、只补1会阻断真正复制。
缺维护品且母源确有废料时，发射母源本人交付废料、角色3付能源1／劳动1回收为维护品、角色3本人交付三项请求。
每项仍由原 `RawLaw.Valid` 判定；转运或回收失败不生成对应库存。

| 实际 visit | 本次响应与实际后果 |
| --- | --- |
| 11 | 5的审计因缺劳动实际被拒；原母源从剩余库存供原料8、能源1、劳动2、维护品1 |
| 12 | 5实付复制出全新6；6首产后种子3／生活品5／维护品1 |
| 13 | 6实际请求失败后获供料；原母源废料1实际回收为维护品1并交给6 |
| 14 | 6实付复制出全新7；7首产并付生活／维护，库存同为3／5／1 |
| 15–18 | 7继续请求复制8，有限剩余供料和审计逐步耗用 |
| 19 | 8未出生；实际缺口为原料1、劳动2、维护品1，保持可读责任 |

`next_word_uses_actual_after` 对所有 depth≥10 证明下一实际词由本次实际 after 生成。
`response_keeps_all_financial_positions` 对任意进入反馈相位的 current 证明所有 instrument／debtor／creditor 余额函数保持；`every_actual_response_keeps_old_claims` 把它接到所有实际反馈访问。
`all_actual_cuts_preserve_living_floors` 检查原19个 frame 的每个原请求前后：原三人，以及已实际播种的4／5／6／7，生活品和维护品均≥1。

`receipts` 从原实际执行收集收支。`cumulative_material_balance` 和 `receipt_consumer_matches_every_actor` 对任意有限长度／Nat参与者／Good复核实际库存。
`participants` 只由初始非零地址与这些实际流转地址生成；`outside_generated_support_has_zero_stock` 证明其余全部地址库存为零。因此有限清单覆盖整个无界地址域的现存库存。

`Runtime.ActualTail` 同时输出本次词／原报告、实际 after 的 typed deficits、全旧债保持、完整库存清单和独立收据核算。
具名 Track 的 `actual_feedback_is_consumed_with_the_whole_inventory` 将它们与下一实际词、同次 productivity face、whole-ledger和自己的next一起消费；`feedback_births_pay_their_first_services_in_the_original_root` 直接消费新生6／7的真实资源、实际词、全部效果和服务付款。

关键反控：删除母源废料不能再生维护品；原law允许耗尽最后维护品的复制仍被 `CopyResources` 拦下；显式非零旧债在修复中保持。
无界地址、两个全新参与者和实际反馈均已生成；有限库存耗尽后的反复 repair 不声明无限增长或 `FutureOpen`。

## 原issue、偿付与原生金融责任同源

`Finance.account` 直接复用 `Financial.accountAt source.input`，从原注册inventory和实际instruction trace逐项产生native admission／crossing；不把raw余额矩阵当准入输入。
零债genesis实际发行并放款1。frame2原native本金为 `[1]`、槽为live；母源生产及实际偿付后，frame4本金为 `[0]`、同一槽为terminal archive。
归档前后原issue的 `(index, debtor, holder, quantity)` 均为 `(0,0,2,1)`；原claim和history在任意有限续行保持。

`all_native_positions_are_the_actual_claims` 对所有有限访问证明完整native余额矩阵等于本source的raw claims，包括任意Nat债地址。
`Runtime.ActualTail` 在实际after同时生成这个完整账户、精确矩阵、从before到after的依赖式native Run，以及原claim／history前缀保持。
增强的同一Track消费者将其与原任务报告、全库存、实际缺口、下一发射和整账／next共同消费。金融折叠不再次执行物量词。
本口安装的是原source全部指令生成的native金融账户与Run；宏询问引擎的独立准入访问不属于此次验收。

## 完整资本关系与原根

`step_preserves_open`、`execution_preserves_open` 从实际 policy／step 证明开放态对任意词保持开放。
`no_capital_kernel` 消费完整 `CapitalRelationKernel` 必需的 reproduced private phase，推出任意开放 current／任意 word 不存在该完整 kernel。
这不是工资、组织名称、净剩余或单次检测器返回值的判定。

`actual_root_capital_family_is_empty` 对实际 visit≥3 的每个原 `RootFace.Item`，经原 provenance theorem 穷举产权、实际剩余和跨词历史三类 witness，分别排除其私有阶段。
历史来源不被删除；开放后的新控制 family 为空。

`Runtime` 在原 `NativeService` root 上增加 productivity coface，保同一 `ProgrammeLiving.livingRoot input` 身份。
`LivingLawPublicProductivityInstance` 同次消费实际复制／完整资本关系排除、原任务 report、whole-ledger 与自己的 generated next，旧服务面继续安装。
sealed activation 从具名 facade 的 `seed.advance` 生成；原 outstanding active Track 导入它。

## 原服务与责任联合验收

[公共生产联合验收](public-production-audit.md)生成原服务的trace／native两条回放、全Nat逐截点库存及底线、原19 frame种子历史保持，并与原生金融Run、原任务行和自己的next同根消费。

## Cell自身的严格红利

[实付方法复用](public-production-shared-audit.md)从同一起点的两条实际程序生成劳动红利1、全部Nat／Good结算、原责任和全部旧合法后继能力保持，并在自己的具名原根消费。

## 实际出生后的新责任

[新生服务责任](public-production-born-service.md)从SharedAudit原种子转移生成出生身份和新的生活／维护义务；每拍实际出生清单自动决定具名责任面，四枚细胞的八项首轮责任已实付归档，并保所有有限后继。

## 总口的剩余责任

本构造生成有限共享库存的实际多代复制、技术更新、原生金融责任、实际反馈及既有责任的联合验收。实际退出／拒绝／重返、退出后自主生产与25帧完整成本红利见[参与机制](public-production-participation.md)。完整 `ArtifactZero`／`LiberateProduction` 继续生成两个独立全合同 verifier、typed合法来源、任意状态开口、逐时服务及试验到采用的创新协议。
库存底线不替代每个未来时窗的实付；末态种子不替代下一轮投入；该有限过程不声明无限免费增长。

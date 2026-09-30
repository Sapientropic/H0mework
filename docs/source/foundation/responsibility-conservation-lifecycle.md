# 责任守恒生命周期

> 状态：稳定机制卡，非 live route、非 checkpoint ledger。
>
> 职责：规定一项 source-backed responsibility 怎样被生成、承载、输运、结算与退出；
> 不记录阶段战报、回归清单或下一步。

## 核心判断

责任不是 mutable status、ticket 数量或总残差标量。它是一枚由 actual source event 生成、
带 exact anchor、incidence、scope 与 lineage 的 dependent lifecycle。
```text
ObstructionAt source
  -> ProducerDemand
  -/-> AdmittedObligation

actual AdmissionEvent
  -> NativeAdmissionPayload
  -> AdmissionReceipt + AdmittedObligation
  -> source-native boundary events
  -> local terminal archive | live successor
  -> next world occurrence
```

obstruction 可以生成结构 demand，但不能自动指定 bearer。只有 actual admission event 连同
authority、assumption / standing mandate、scope 与 discharge jurisdiction，才能把 demand 或其他
合法承诺送入 live responsibility carrier。

## 核心 carrier

[`ResponsibilityLifecycleKernel.lean`](../../../../SaturationMonoid/ResponsibilityLifecycleKernel.lean)
固定以下分层：

- `Vocabulary`：领域语法；其中 `ProgressAt` 只是 raw receipt family；
- `ProducerDemand`：由 obstruction 生成的结构责任，不含 bearer 或 admission authority；
- `NativeAdmissionPayload` / `AdmissionReceipt`：actual admission 的 canonical payload 与原始法域；
- `AdmittedObligation`：当前 live obligation；其变化由 lifecycle event 生成；
- `NativeResponsibilityProcess`：actual event 的 classifier；调用方不提交 target state 或 branch；
- `Edge` / dependent `Run`：前一 edge 的 exact target 是下一 edge 的 source；history 只在尾部追加。

源码故意没有 primitive `isAdmitted`、`isAccepted`、`isFulfilled` 或 `isDischarged` Boolean。
这些状态必须由 typed event 与 receipt 生成。

## 三条守恒 law

- `Edge.freshlyAllocated_implies_admitted`：全新 stable slot 只能由 actual admission 生成；
- `Edge.newlyLive_implies_admitted_or_reopened`：已有 slot 重新 live 时，额外来源只能是带
  terminal archive 与同 lineage 证据的 reopen；
- `Edge.disappears_implies_obligationTerminal`：live slot 只有 obligation-level terminal receipt
  才能消失。

由此得到三条框架纪律：

```text
No-Free Generation
No-Free Continuation
No-Free Disappearance
```

每次 live boundary crossing 必须由 source-owned event 生成 progress、maintenance、typed defer、
scope narrowing、accepted transfer、supersession 或 typed exit。bearer release 不等于 obligation
terminal；reopen 与 supersession 也不能洗掉旧 debt lineage。

当责任已经作为root ledger中的live entry存在时，不再为它重建领域私有vocabulary、单-obligation
`ResponsibilityState`或`NativeResponsibilityProcess`。exact operational delivery由
[`LivingLawOperationalSeparationSourceNativeRootAdapter.lean`](../../../../SaturationMonoid/LivingLawOperationalSeparationSourceNativeRootAdapter.lean)
直接读出consumer entry，随后由
[`LivingLawRootCausalEntryTotalDispositionKernel.lean`](../../../../SaturationMonoid/LivingLawRootCausalEntryTotalDispositionKernel.lean)
读取同一whole-ledger successor或terminal。initial/cofinal generated row完成一次admission；后续sparse patch
只选择local processing，不能让已入账责任消失、重开或生成平行obstruction。generic lifecycle grammar仍描述
责任守恒，但领域不得靠重新实例化它取得第二本活账。

[`LivingLawTypedSemanticWorldNetworkU8LifecycleKernel.lean`](../../../../SaturationMonoid/LivingLawTypedSemanticWorldNetworkU8LifecycleKernel.lean)
给出U8共享实例：typed revision原生生成revised root first write，old/new causal entries沿同一actual write进入target
occurrence，anchor、incidence、lineage与whole ledger逐项保留。target consumer再由
`LivingLawTypedSemanticWorldNetworkU8RecoveryKernel.lean`在该occurrence结算或继续责任。

旧root-native three-edge court把audit、selection与consumer law作为既有world之后的参数，且只有facade/self-regression
consumer，现已删除。multiplicity residual仍只是未结readout；真实后继必须从下一枚registered root occurrence的exact
ledger match生成。

## 原子更新与顺序历史

actual update 同时改变 residual 与 bearer 时，底层 grammar 使用单枚
`.progressedAndTransferred`：同一 event 同时生成 progress receipt 与 accepted route，不暴露
“先 progress、后免费 transfer”的中间状态。

`Run.history_eq` 把 target history 固定为 source history 加上本次 run 的有序事件；`Run.concatRuns`
只在中间 exact state 对齐时组合。cursor、suffix 或 progress 若只留在 readout 而未进入
`Edge.target`，不构成 lifecycle continuation。

## Transfer、split、merge、rename 与 reopen

这些结构都是 receipt / consumer mouth，不是领域 event producer：

- accepted transfer 才改变 bearer；transfer offer 只是 observation；
- split / merge 必须保存 parent、child 或 target 的 exact incidence、local discharge、debt lineage
  与 whole-anchor transport；
- rename 必须保存 source ownership、incidence 与 anchor transport；
- supersession 保存 old/new exact incidence、coverage 与 old→successor transport；
- reopen 还要证明 reopen source 与新 admission source 对齐，并保存 old→new transport。

守恒的是 provenance-preserving incidence，不是 ticket 数量。合法的 split、merge 或 recurrence
可以改变对象数；它们不能无回执地复制、合并或删除责任。

## Consumer-relative observer

[`ResponsibilityObserverKernel.lean`](../../../../SaturationMonoid/ResponsibilityObserverKernel.lean)
把 consumer status 分为：
```text
certifiedSafe | hidden HiddenNullWitness | unclassified
```

`certifiedSafe` 必须在 observer image 上生成 consumer factorization；`hidden` 证明同一 observation
fibre 内存在不同 required disposition；`unclassified` 没有 default-safe readout。

`currentResponsibilityObserver` 保留 exact live obligation。薄 projection 若擦掉 actual admission，
框架生成 actual-edge `HiddenNullWitness` 与 full-trace redirect，不宣称 projection 已经安全。

## Capacity 与 liveness

[`ResponsibilityCapacityKernel.lean`](../../../../SaturationMonoid/ResponsibilityCapacityKernel.lean)
中的数值 budget 是 lifecycle 的有限投影，不是责任本体。

`ActualMaintenanceDebit` 把 debit 锁回 exact edge、slot、obligation、lineage、`.maintained`
receipt 与 source/target live readout；`NativeDebitedRun` 再逐 edge 覆盖同一 dependent run。
budget 耗尽只排除继续把后继称为 certified unchanged-maintenance segment；后续事件仍可由另一枚
typed disposition 合法生成。

[`LivingLawRootNoetherianDebtClosureKernel.lean`](../../../../SaturationMonoid/LivingLawRootNoetherianDebtClosureKernel.lean)
把这项有限算术提升到 fixed living-root process。`SourceNativeRootDebtCurrentAt` 以一枚 origin row 固定
`RootDebtLineageAt`；每个微步只能落在 `process.successor` 的完整 target ledger，并携带一枚实际
`LedgerEntryEvolutionAt`。同债与 no-refill 只从该 row 读出，不能由领域平行提交。非结算分支必须给出
可空的前后 no-refill history，以及夹在其中的一枚 exact payment step；kernel 自动组合
`≤ ; < ; ≤` 得到 macro 的 `targetBudget < sourceBudget`，不再接受 caller-supplied endpoint strictness。
由此得到构造性的 well-founded continuation relation，任意 total
`SourceNativeNoetherianDebtClosureLaw` 都生成同一 debt 的 exact compiler discharge。

这里的 totality 是 debt-indexed：它不从 `actual write` 推出终止，也不限制无限 fresh-write 系统。
领域实例仍须从其真实 root history 生成 macro coverage 与 exact payment；不能把 budget、target、terminal
或完成历史塞进 caller premise。transfer、U7/U8 carrier revision 与 local clock change若继续同一 debt，
都只能保留旧预算，不能生成 fresh credit。

root live entry 的 `progressBudget` 同时进入 whole-ledger row identity。债务本身不是在 ledger compartment
间移动的 token：ordinary carry 是同一 row 在定义性相同 root face 上的读取，故 budget 精确相等；
accepted transfer 是同一 debt 的 bearer/anchor/incidence relation 发生 actual reassignment，而非刷新 debt identity。
`LedgerEntryEvolutionAt` 的权威分支现在是：ordinary carry 定义性保持完整entry；maintenance允许support
随actual current前进，但保持anchor、incidence、lineage、responsibility与claim，并严格支付
`targetBudget < sourceBudget`；accepted transfer
携带world receipt；新anchor/incidence由外层exact root transition登记，但lineage与claim必须保持，且只能满足
`targetBudget <= sourceBudget`。maintenance没有独立inhabited receipt，只有
fixed root occurrence的exact row event/compiler能生成该分支并进入whole-ledger fold。真实新额度必须来自
另一枚source-generated root occurrence，不能藏在transfer、U7 redirect或U8 carrier revision里。
若一枚旧 row 实际 split 为多枚 descendants，每条 child branch 还必须严格支付 parent budget；逐项
`<=` 不足以阻止把同一有限续期能力复制给多个后继。

## Dormant effect 不是空账

[`LivingLawRootEffectReactivationKernel.lean`](../../../../SaturationMonoid/LivingLawRootEffectReactivationKernel.lean)
把 installed effect 的 inactive fibre 保留为同一 live row，而不是把“当前不可见”解释成责任消失。
source 必须穷尽生成：

```text
faithful settlement
| same-row dormant successor
| whole-ledger transport + source-native receipt-backed reactivation
| same-row obstruction → U7 cut
```

不存在裸 `inactive → active` constructor。reactivation receipt 同时索引 source occurrence、compiler
successor 与 target active witness；whole-ledger transport又证明 dormant entry 确实成为该 target 的
effect entry。分类、payload与 exact temporal authority随后作为原 authority source 的 installed lifecycle
face读取，不建立第二本 effect ledger。转入 inactive 不补预算；重新 active 也不生成 fresh debt identity。

## Pending claim birth、gated current 与 U7

终局claim若尚无首笔payment，先由package-valued installed face生成fresh pending ledger row；package的
`PayloadAt`定义性固定activation law、claim、initial state与正预算，禁止外部payload mapper代写claim。
[`SourceGeneratedPendingClaimBirthLedgerKernel.lean`](../../../../SaturationMonoid/LivingLaw/Inventory/Birth/Pending/SourceGeneratedPendingClaimBirthLedgerKernel.lean)
的birth不生成root或next。随后
[`SourceNativeGatedClaimPreProcessKernel.lean`](../../../../SaturationMonoid/LivingLaw/Runtime/GatedClaim/SourceNativeGatedClaimPreProcessKernel.lean)
只允许actual `StepAt`生成whole-ledger strict advance；local settlement单独只清零本债且无next，whole terminal还需
base support-settlement receipt或独立`SupportTerminalAt`；obstruction保持同claim进入既有debt-U7且无next。
只有source已对每个gated current生成合法step、whole terminal或U7处置后，才可安装total living process。

strict payment 与其target上的whole-terminal都已实际生成时，
[`SourceNativeGatedClaimPaidRootKernel.lean`](../../../../SaturationMonoid/LivingLaw/Runtime/GatedClaim/Authority/SourceNativeGatedClaimPaidRootKernel.lean)
把这一个已付款分支编译为两相authoritative root。payment patch以source-selected transported remainder覆盖完整
active ledger，initial generated row逐字选择born debt row；causal authority只能沿该strict write进入paid row，
随后同一row才被faithful terminal discharge。该bounded producer不赋予pending或obstruction分支next；future
terminal只作为已经生成settlement的target receipt进入，不是预填答案。

obstruction分支则停在
[`SourceNativeGatedClaimObstructionInquiryBoundaryKernel.lean`](../../../../SaturationMonoid/LivingLaw/Runtime/GatedClaim/Authority/Obstruction/SourceNativeGatedClaimObstructionInquiryBoundaryKernel.lean)：
同一debt row原生生成U7 theory audit，但仍无next。若当前law surface是完整`rootSemantic`，该obstruction已有
literal expression与active debt realization，所以audit是`oldLanguageAnswered`，并由既有no-go排除U8；这只说明
residual已被忠实表示，不支付原claim。只有actual operational theory同时给出不可表达与无合法realization时，
existing U8才自动触发。不得为取得causal token另造identity self-loop audit root。

`DebtActivationLaw`的step、settlement与obstruction共享同一DebtState和identity。generic debt-U7保持旧
obstruction calculus，并对active debt obstruction原生生成unit demand、exact live debt row与
`debtObstructionReceipt` theory-audit；inactive face没有debt event。领域不得再建私有U7 vocabulary。

当base obstruction fibre为空时，canonical vacuous U7只由fibrewise`IsEmpty`生成，不接受caller demand/event；
它仍可被debt-U7扩张。U7 row生成后仍必须进入target living root的source-generated initial patch，单独的row或
audit receipt不等于causal authority，也不自动触发U8。

target audit root可以用complete two-row initial patch取得causal authority，但identity carry只表示audit期间同一
row被保留。只有bearer/anchor/incidence发生actual reassignment时，下一物理拍才可用same-debt transfer保存这段
历史；若这些身份仍是同一row，obstruction不能改名为transfer。transfer可保持预算，但不能补充预算、退出U7或
代替strict payment。

## Local settlement 不是 world terminal

obligation-level terminal只关闭一枚exact incidence。它可以改变live ledger，却没有权威声称现实整体不再发生。
[`LivingLawRootAnswerNextKernel.lean`](../../../../SaturationMonoid/LivingLawRootAnswerNextKernel.lean)
直接强制正确形状。entry-indexed terminal只有在同一whole-root compiler生成`faithfulTerminal`时才出现；完整source
identity在emitter之前固定terminal handoff compiler，因而exact whole-ledger terminal occurrence只能
成为当前typed answer，并由这枚pre-emitter law直接生成下一authoritative root的initial occurrence；旧的
`GeneratedSourceNativeTerminalHandoffAt`与temporal answer-and-next重复包装均已删除。public readout只有
同一root occurrence的whole ledger与`generatedNextCurrentAt`，不暴露world-terminal branch。

operational target不再发行自己的lifecycle classifier或execution。transfer/carry由root
`CausalEntrySuccessorAt.entryDestination`保留为exact dependent ledger row，terminal保留为
`LedgerEntryTerminalAt`，registration miss仍是root typed obstruction。把这些row再次编译成领域私有edge/run
会重建一套平行账本，因此该adapter已经删除。
[`LivingLawRootAnswerNextHistoryKernel.lean`](../../../../SaturationMonoid/LivingLawRootAnswerNextHistoryKernel.lean)
再把每枚next current的living source law锁进同一process identity；finite history只有actual step与观察fuel exhaustion。

typed-U8 不再另建 post-recovery schedule 法域。
[`LivingLawTypedSemanticWorldNetworkU8RecoveryKernel.lean`](../../../../SaturationMonoid/LivingLawTypedSemanticWorldNetworkU8RecoveryKernel.lean)
直接在 revised first-write 的 exact target occurrence 上生成 old-failure 与 new-only 两行 disposition；后续时间若取得
authority，必须重新进入通用 living-root answer-and-next，而不能由 U8 adapter 自行发行一条 history。

## 与其他稳定机制的分工

| 机制卡 | 独立职责 |
| --- | --- |
| [source / root authority](../authority/source-root-authority.md) | O0 anchor、canonical receipt、single-root visit 与 whole-ledger authority |
| [causal realization / no-free difference](../ontology/causal-realization-no-free-difference.md) | 固定 causal surface 与 operational equivalence 下的唯一合法现实类 |
| [atom-field / living evolution](../ontology/atom-field-living-evolution.md) | finite atom、field readout 与 living-law total evolution 的层级 |
| [U7 / U8 no-free idealization](u7-u8-no-free-idealization.md) | obstruction demand、theory revision、pair comparison 与 independent settlement |
| [operational separation](../authority/operational-separation.md) | actual search 如何生成 finite delivery 或 exact cut→U7 |
| [world progress / standing renewal](world-progress-standing-renewal.md) | exact root answer-and-next、maintenance debit 与 standing-as-successor |

本卡不复制这些机制的 theorem 清单。框架 checkpoint 状态只见
[living-law framework ledger](../../../ledgers/living-law-framework-checkpoints.md)。

## 权威源码入口

- [`Tracks/ResponsibilityConservation.lean`](../../../../SaturationMonoid/Tracks/ResponsibilityConservation.lean)
- [`ResponsibilityLifecycleKernel.lean`](../../../../SaturationMonoid/ResponsibilityLifecycleKernel.lean)
- [`ResponsibilityObserverKernel.lean`](../../../../SaturationMonoid/ResponsibilityObserverKernel.lean)
- [`ResponsibilityLineageKernel.lean`](../../../../SaturationMonoid/ResponsibilityLineageKernel.lean)
- [`ResponsibilityCapacityKernel.lean`](../../../../SaturationMonoid/ResponsibilityCapacityKernel.lean)
- [`NativeResidualUpdateResponsibilityProcess.lean`](../../../../SaturationMonoid/NativeResidualUpdateResponsibilityProcess.lean)
- [`LivingLawTypedSemanticWorldNetworkU8LifecycleKernel.lean`](../../../../SaturationMonoid/LivingLawTypedSemanticWorldNetworkU8LifecycleKernel.lean)
- [`LivingLawTypedSemanticWorldNetworkU8RecoveryKernel.lean`](../../../../SaturationMonoid/LivingLawTypedSemanticWorldNetworkU8RecoveryKernel.lean)
- [`LivingLawOperationalSeparationSourceNativeRootAdapter.lean`](../../../../SaturationMonoid/LivingLawOperationalSeparationSourceNativeRootAdapter.lean)
- [`LivingLawRootCausalEntryTotalDispositionKernel.lean`](../../../../SaturationMonoid/LivingLawRootCausalEntryTotalDispositionKernel.lean)
- [`LivingLawRootNoetherianDebtClosureKernel.lean`](../../../../SaturationMonoid/LivingLawRootNoetherianDebtClosureKernel.lean)
- [`LivingLawRootEffectReactivationKernel.lean`](../../../../SaturationMonoid/LivingLawRootEffectReactivationKernel.lean)
- [`LivingLawRootAnswerNextKernel.lean`](../../../../SaturationMonoid/LivingLawRootAnswerNextKernel.lean)
- [`LivingLawRootAnswerNextHistoryKernel.lean`](../../../../SaturationMonoid/LivingLawRootAnswerNextHistoryKernel.lean)

## 边界

- source / receipt authority 不由本卡重复定义，见 source/root card；
- raw `.progressed` 不等于 shared-world strict progress；
- raw lifecycle `.maintained` 若没有对应root exact row与严格debit，只是custody/readout；
- obstruction 不自动变成 admitted obligation；
- consumer mouth、coverage、safe certificate、next state 或 terminal branch 不能作为 primitive
  source premise；
- 领域 adapter 尚未进入共享 constructor 时，只是 transporter，不是领域自治 lifecycle。

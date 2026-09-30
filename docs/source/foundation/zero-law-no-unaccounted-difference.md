# 零号律：无账外差异

> 状态：稳定机制卡，非 active route、非 checkpoint 战报。
>
> 职责：规定什么对象有资格成为 lawful world state，并把 U1–U8 解释为同一闭域原则的不同投影。

## 不是把结论写进定义

“无账外差异”是派生合同，不是 `NoMagic := 没有无根据事实` 的循环定义。它的非循环地基见
[总体实在与结构归属](total-reality-structural-identity.md)：先独立给出 actuality、stable reference、
real difference、redundancy 与 positive structural identity；再证明 magic claim 必然形成
external-supplement obligation，而 source-native total reality 排除该 obligation。

Lean 中的抽象链是：

```text
MagicBitAt
-> ExternalSupplementAt

TotalRealityAt
-> not ExternalSupplementAt
-> not MagicBitAt
```

`TotalRealityAt` 只含正向 `Redundant ∨ StructuralIdentity` classification，不含 `NoMagic` 字段。
具体 world 的 totality 由 `SourceNativeLedgerRootClosure` 的 exact registered-occurrence theorem生成，
不能由consumer提交。

## 派生的本体合同

```text
任何 actual difference
-> 已进入 source / exact root occurrence / trace-write-back / live ledger
 | 生成 typed residual / U8 revision responsibility
```

不存在第三种“确实不同，但可以永远不记账”。这条判据不等待差异改判：只要一枚 bit 能作为独立
lawful world state 存在，却没有上述任何支撑，law inventory 已经不是全账。这里的“不记账”是当前
world/evolution 的操作性断言，不是把尚未发现的数学真理判成不存在。

反向边界同样重要：若两个 raw values 在全部 source-fixed operational contexts 中永远不可区分、不可输运
且无 effect，它们只能是同一 operational reality 的不同 presentation。框架不必用 Lean quotient 把二者
字面压平；构造性的 `EquivalentAt` 已经是 world identity 的语义 quotient。

U8 不属于账外自由度。旧 epoch 无法表达 actual obstruction 时，obstruction 生成 meta-residual、
failure-indexed revision、faithful compiler、theorem survival、semantic-change ledger 与后继 root closure，
正是在恢复闭域。真正击穿 lawhood 的只会是一枚差异既逃离旧账，又拒绝成为任何 faithful U8 history。

## 机器入口

[`LivingLawZeroLawRootAdmissionKernel.lean`](../../../../SaturationMonoid/LivingLawZeroLawRootAdmissionKernel.lean)
不新增监督 record。`LawfulWorldStateAt root` 就是既有 source-native root 的 exact temporal visit：

```text
fixed source-native ledger root
-> finite | source-owned cofinal | post-cofinal history
-> exact registered causal occurrence
-> whole generated evolution + exact current patch
-> native | relation | continued | redirect | terminal | extension
```

`registeredOccurrence_ne_of_ne` 给出零号律的同根正向式：两枚 lawful world states 若不同，其 exact
registered occurrences 必不同。外部可以定义 `LawfulWorldStateAt root × Bool`，但该 wrapper 不是 lawful
state carrier；投影回root visit后两枚值具有同一 state、occurrence 与 whole evolution。若要让 bit
成为真实差异，它必须先改变 source/root occurrence，或由新的 residual/U8 event 登记。

这个接口直接依赖
[`LivingLawRootTemporalAnswerNextKernel.lean`](../../../../SaturationMonoid/LivingLawRootTemporalAnswerNextKernel.lean)
已有的 source-native temporal occurrence。它不是从任意 `RawWorld` 与一组 optional premise 推出合法世界；
满足 root closure、registry 与 whole-ledger compiler 是讨论域的准入条件，也不再经过一座identity causal court。

## U1–U8 是零号律的投影

- U1：状态差异由 actual update 生成；
- U2：换 carrier 保持同一差异与责任；
- U3：observer kernel 不能让真实差异无处安放；
- U4：差异进入 independent consumer 或留下 exact obstruction；
- U5/U6：组合网络保存 occurrence、lineage 与 whole-carrier effect；
- U7：未结差异生成下一 producer demand；
- U8：表达差异的语言不足本身也成为 registered meta-residual。

因此“全律同根”不等于把所有 law 字段塞进一个大 structure。承重事实是 world identity 只由 complete
registered incidence 取得 authority；后续 kernel 是这条 identity conservation 在不同接口上的展开。

## 重分图不得洗掉差异

局部chart可以为一枚actual relation生成新的共同root key，但该key必须把造成重分图的旧端点数据一并带走。
例如event-indexed lineage transport不能通过把两端都改写成一个空token来获得字面相等；合法common key至少
保留exact event、两端旧anchor/incidence/lineage与whole-ledger seam。这样新chart中的equality表达“同一笔
关系账”，而不是宣称旧presentation中的两个值从未不同。

早期 registered-contact local rechart 曾把这一合同编码成独立 local world，但它没有 exact root consumer，已删除。
合同本身保留：若不能从同一 root transition生成保留旧端点数据的 key，重分图就只是 presentation 或待登记的
U8责任，不能取得 world authority。

U8同样遵守这条边界，但不再拥有registered-atlas process专用court。root-native theory audit、heterogeneous
first write与typed semantic change都索引同一root occurrence；theory selection不再索引typed world，只能在
revised-root installed equation presentation中生效。未resolved的multiplicity只能成为同一root law生成的下一笔
responsibility，不能由领域prefix另开new-root compiler。旧process-local
audit→selection→history链已退出production graph。

时间边界上的漏登记同样属于账上差异。
[`LivingLawRootCausalEntryTotalDispositionKernel.lean`](../../../../SaturationMonoid/LivingLawRootCausalEntryTotalDispositionKernel.lean)
把每枚已有causal authority穷尽为whole-ledger successor或actual terminal discharge。initial/cofinal generated row
完成首次登记后，complete ledger在每枚continuing occurrence中都给出dependent destination；finite patch仅是本拍
local processing readout，其`none`不构成world差异，也不能生成新的jurisdiction residual。这样“本拍patch没有
处理我”既不等于“我不存在”，也不会被误报成另一笔U7债。

[`LivingLawObstructionGeneratedMinimalCofaceKernel.lean`](../../../../SaturationMonoid/LivingLawObstructionGeneratedMinimalCofaceKernel.lean)
只允许fixed-root failure face启动world-network U8：actual obstruction的token必须已是同root visit的projection
payload，并与canonical U7 event、theory-audit demand row及whole-ledger successor对齐。领域sibling
compiler、selection projection或裸typed semantic change不能激活U8。真正改变support/responsibility inventory的
authority只存在于下游typed semantic-change producer；revised initial support、occurrence与old-entry row均从
原root successor生成。

[`LivingLawTypedSemanticWorldNetworkU8Kernel.lean`](../../../../SaturationMonoid/LivingLawTypedSemanticWorldNetworkU8Kernel.lean)
实现了这枚非保守分支。old carrier进入`NewN`时只要求constructive retract：old value精确round-trip，但revised carrier
可以有无old preimage的新值。同一selected event的compiler output必须同时携带typed semantic change、revised first
write、old causal entry在initial finite patch中的generated row，以及一枚同patch new-only row与其no-preimage证明。
因此世界差异不是“类型里可任选更多值”，而是actual root write生成了新的registered incidence。该机制仍不生成
independent closure；old obstruction的settlement与new-only responsibility的后继处置必须由下游actual consumer分别支付。

[`LivingLawTypedSemanticWorldNetworkU8LifecycleKernel.lean`](../../../../SaturationMonoid/LivingLawTypedSemanticWorldNetworkU8LifecycleKernel.lean)
把这项登记推进到首写之后。old row与new-only row只能从各自的revised initial-patch membership取得initial causal
authority，并共同消费同一枚compiler-generated first write；target authority仍按两枚entry分别生成。于是“新语言已经
写出第一拍”不能洗掉旧债，也不能让新增差异成为一次性装饰。该kernel只证明账的时间连续性，不把迁账、表示或
semantic change重命名成independent settlement。

[`LivingLawTypedSemanticWorldNetworkU8RecoveryKernel.lean`](../../../../SaturationMonoid/LivingLawTypedSemanticWorldNetworkU8RecoveryKernel.lean)
进一步规定什么才算旧obstruction的恢复，而不是same-support误认。pre-emitter U8 source law把旧root的literal
occurrence映到source-owned U7 calculus的canonical obstruction event；old root entry再由该event的demand entry经exact
support transport直接生成。revised first-write target随后作为新的actual consumer occurrence，对old entry生成terminal
discharge或causal successor；new-only entry的target disposition也直接读取同一root
classifier，不在每个verdict中重复保存。因此
旧债是否结清与新语义差异是否继续是两笔同时发生、不可相互抵销的账。

这给零号律增加了一个dependent边界：账面位置相同不等于责任相同。obstruction support、root occurrence、U7 event与
demand entry必须同源对齐；否则只能说revision保存了一枚live entry，不能说它恢复了当前failure。反过来，一旦exact
demand entry已经抵达target root，它就由complete ledger继续；consumer sparse patch是否选中不再参与其存在性。

`RootedActualExpressibilityFailureAt.ofRootFailureFace`完成唯一同源入口；typed revision同时索引该rooted
failure与后续source-selected candidate。selection只支付actual realization分叉，不再复制failure-entry、old-root
projection或compiler。旧`RootedSelectedWorldNetworkRevisionAt`与selection-root grammar已删除；它们不能因为
“处理同一failure”而另开一套账。

这也说明零号律不是额外监督字段：只有已形成proof graph的actual occurrence与ledger realization取得authority；未接入
root graph的识别工具最多是readout，不因拥有自己的canonical receipt而成为现实分支。

## 数学也在现实总账内

“现实”在本机制中不是物质对象的窄集合，而是全部actual state、relation、proof event、observer与representation
共同形成的结构。因此数学实践显然是actual occurrence；固定定义后的逻辑后果则是该结构的刚性关系。Lean证明项
验证的是这类内部关系，不是从现实外部向世界颁布命令。

这不把语言中每个可定义对象都升级为已经完成的世界库存。`Nat -> A`可以作为source-generated time field或统一
规则的readout，但不能仅凭函数类型获得current-atom authority；完成无穷与逐步生成仍由
[atom-field living evolution](atom-field-living-evolution.md)区分。数学条件模型也可以自由研究任意`Fin (N+1)`；
只有当“实际过程恰好停在N”成为world difference时，terminal identity才必须进入同一结构账。

[`LivingLawArithmeticNakedTerminalKernel.lean`](../../../../SaturationMonoid/LivingLawArithmeticNakedTerminalKernel.lean)
把这条边界做成派生consumer。`ArithmeticTerminalCandidateAt`保存local admissibility、reachability、terminal claim，
以及该exact index上actual decision occurrence投影出的ambient nonredundant difference；它仍不授予terminal authority。
`DecisionOccurrenceAt`代替了旧的`Nat → Difference`：未发生决策的index保持空fibre，不为统一定理mouth预装
一张完成的未来决策表。
`TotalRealityAt`只能生成positive `StructurallyGroundedTerminalDecisionAt` readout，不能由此铸造terminal。
若候选同时否认这项structural grounding，它便生成
`ExternalSupplementAt`，并被`TotalRealityAt`统一消去：

```text
actual nonredundant stop/continue difference
-> positive structural grounding
 | external supplement

source-native total reality
-> structurally grounded decision difference
 | rejection of the naked terminal
```

[`LivingLawRootArithmeticNakedTerminalAdapter.lean`](../../../../SaturationMonoid/LivingLawRootArithmeticNakedTerminalAdapter.lean)
从既有source-native ledger root直接派生该结论；theorem mouth没有`NoMagic`、completed future或“过程理应继续”的premise。
领域仍须忠实识别自己的local arithmetic predicates与exact root difference，并另取同一actual terminal occurrence的
complete ledger grounding。若一个过程进一步证明每个reachable finite index都没有source-native grounded terminal，并且
source-native evolution总能生成下一处置，才可派生逐有限截面的无终点运行；框架不会
把这个更强领域事实偷塞进通用kernel。

`LivingLawRootTotalRealityAdapter`直接从同一root生成positive total reality，随后导出
external-supplement、magic-bit与arithmetic naked-terminal消去；零号律不是另一个可由consumer选择的world record，
也不再经representation-owned wrapper转发。

因此“一证永证”的准确含义也是结构性的：同一命题、定义、domain与推演关系固定后，已经成立的proof relation不能
无账改口。若后续结论不同，必须显影为对象、语义、law epoch或interpretation map的actual change，而不是让同一证明
关系被现实凭空背叛。

## 幻想与未实现对象

幻想不是账外差异。想象、语言或图像已经是心智世界中的 actual occurrence；它所指向的外部截面尚未
实现，二者间的差距可以登记为 residual、producer demand 或 expressibility failure。合法名字未必立即
获得对象，但必须落到 realization、exact obstruction 或 theory evolution，不能作为空字符串悬浮。

## 验收

```text
#print axioms = []
+ no caller-supplied world state / occurrence / outcome / ghost field
+ raw wrapper cannot mint a second lawful identity
+ real state difference implies registered occurrence difference
```

零公理排除逻辑悬空；private/source-generated authority mouth 排除 producer smuggling。两者缺一不可。

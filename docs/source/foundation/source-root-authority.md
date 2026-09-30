# Source / Root Authority

> 状态：稳定机制卡。当前路线见
> [living-law active route](../../../handoffs/living-law-framework-active-route.md)。

本卡只规定一件事：一枚 subsystem 结果何时有资格影响已登记 world。

已发生事实的根级确定性、历史溯源、局部观察与未来生成，先按
[根读恒等](same-occurrence-inquiry-answer.md)恢复；本卡的解释映射与准入区分不重开那些已证的同发生关系。

## 真值、表示、证明、occurrence 与 live authority 的四层分界

本卡中的 `authority` 是 typed proof/runtime 链上的**操作性与谱系资格**，不是数学真值的制造权。
数学命题或结构因其语义、结构或公理而真；发现、证明与登记只是把它显影并接入可复核链。
必须分开四层：

```text
T = 数学命题或结构的真值 / 存在
S = 在某种语言、模型或坐标中的 statement / representation
P = 在给定语义/公理/结构下对 S 的证明或推导
O = 对 S/P 的发现、显影、登记或消费 occurrence
```

“定理”可指成立的命题，也可指形式系统中已取得证明的状态；本卡只把后者作为链上证据，不把它当作真值的出生事件。

形式系统内的真值是其公理/语义下的结构后果；要把它读作目标现实中的真值，还需 faithful
interpretation。`P` 给出相对于条件的证据，`O` 把 `S/P` 以 source-faithful 方式接入这条链。
`O` 缺失不改写 `T`。无魔法 bit 沿用绝对刚性定义：一枚真实且非表示/命名冗余的差异，既不是
此前现实生成的，也不由当前整体结构或已有关系决定，却被选成 0/1；这不是“尚未找到证明”的同义词。
`source-generated` 统一读作对既有 source 的忠实显影、推导、证明或登记，不读作创造知识；root
authority 只表示它能影响本链的 current、next 或 consumer。

```text
source-owned actual event
→ complete event-inventory admission
→ exact temporal root occurrence
→ canonical path / trace / write-back / whole ledger
→ installed dependent face
→ answer-and-next
```

少任一层都不能取得本条 live-chain authority；这不等于背后的数学命题为假。

## Source 是责任起点

[`SourceAnchorConservationKernel.lean`](../../../../SaturationMonoid/SourceAnchorConservationKernel.lean)
用 complement、scope 与 lineage 登记 source anchor。O0 是最低户籍格式，不是上级 source；
primitive source 可以很小，也不需要另一位 authority 授权。

source-local compiler 同样合法。它的 receipt 默认只在自己的 anchor、incidence、lineage 与 law epoch
内有效。换 source 必须走 explicit transport、transfer 或 law-surface revision；不能只因两个 carrier
外观相同就复用旧 authority。

[`CanonicalReceiptAuthorityKernel.lean`](../../../../SaturationMonoid/CanonicalReceiptAuthorityKernel.lean)
把 canonical receipt 定义成 exact actual event 经 fixed compiler 的像。`Type` 可居住、等式、
observer readout 或 total function 都不能代替该 event。

## Complete event inventory

[`LivingLawRootSourceNativeAuthorityKernel.lean`](../../../../SaturationMonoid/LivingLawRootSourceNativeAuthorityKernel.lean)
中的 `SourceNativeCompleteEventInventoryAdmission` 是准入门。它双向保留：

- current 与 ordinary occurrence/evolution 的完整 fibre；
- structural branch、exact target 与 support；
- whole-ledger write-back 与 finite generated patch；
- cofinal event、`emit?`、predecessor path 与 landing target。

因此 faithful rechart 不能删 continuation、重标 branch、伪造 terminal，或插入/擦除 cofinal
boundary。authority terminal 还必须证明 admitted concrete source 的 ordinary outgoing-event fibre
确实为空。

这里必须区分两种 inventory：

- actual-event inventory 必须完整，由上述 admission 支付；
- projection family 只是 source-fixed readout 坐标，不宣称 global completeness。

所以 `Projection := PUnit` 只表示“一枚投影坐标”，不是“完整 root”证书。类似地，function-valued
payload 可以是合法 field readout；它不能仅凭可读性升级成 atom、effect、inquiry、U7 或 U8 authority。
同一 source classifier 若重复认证同一 fibre，`active_eq_of_classify_eq`、
`inactive_eq_of_classify_eq` 与 `project_heq_of_classify_eq` 会构造性地锁死两侧 witness 及完整
dependent payload；proof-relevant token 不能成为第二枚 outcome selector。即使调用者为同一 semantic
component 提交两条不同 installation/embedding，`outcome_heq_of_same_component` 仍迫使两条路径在
fixed whole inventory 上读出同一完整 outcome；embedding 不能藏 outcome bit。

## Root occurrence 与 temporal authority

[`LivingLawRootConstructiveKernel.lean`](../../../../SaturationMonoid/LivingLawRootConstructiveKernel.lean)
让同一 occurrence 同时决定 structural evolution 与 whole live ledger。`CompleteLiveLedgerAt.Entry`
是该 support 上完整的 open-responsibility fibre，不是调用者选择的一笔债。

[`LivingLawRootAnswerNextKernel.lean`](../../../../SaturationMonoid/LivingLawRootAnswerNextKernel.lean)
以 `SourceNativeTemporalVisitAt` 统一 finite、cofinal 与 post-cofinal history。即使 recurrence 回到相同
current，新的 visit 仍保留完整 predecessor history，不能重放旧 authority。

[`LivingLawRootTemporalAnswerNextKernel.lean`](../../../../SaturationMonoid/LivingLawRootTemporalAnswerNextKernel.lean)
将 complete-source temporal authority 索引到完整 admitted root；其 canonical ledger/history coordinate
通过 `toLedgerReadout` 单向读取。`temporalVisitAuthorityCompiler` 的 codomain 就是该 root-sealed token；
裸 temporal ledger token 不能构造 authority，也不能在共享同一 lower ledger compiler 的 sibling source 间重用。
通用 raw theorem 只叫 `installedSubsystemReadout_factorizes`；atom-field 与 operational/U8 joint coface
等 public authority theorem 必须消费 `SourceNativeAuthoritativeTemporalEvolutionAt`，不能把该 readout
重新包装成领域 authority。

Authoritative temporal token 仍是 terminal-handoff 之前的单向 coordinate。凡返回 living next root 的
组合接口必须消费 `SourceNativeLivingRootCausalEvolutionAt`；否则两枚共享同一 lower
occurrence 但 handoff law 不同的 living source 可以重放同一 ledger token 选择不同 successor。

local faithful terminal 是相对结束，不是 world-global terminal：

```text
exact local terminal occurrence
→ complete old-ledger settlement
→ source-fixed terminal handoff
→ same root law surface
→ next registered root current
```

跨拍 process 只暴露整枚 generated-successor relation：exact handoff target 与 continuing-branch
living-law conservation 不可拆开提交。Terminal handoff 可以更换局部 vocabulary/current，但 target
root 必须保留 source-fixed law surface；语义修订只能经 rooted U7/U8。这一保守律是
next-current私有compiler的dependent产物，并由固定process的successor逐拍继承；不存在可脱离
实际handoff消费的平行“保法”token。

同 standing 跨 root 必须保持 anchor、incidence、lineage、responsibility 与 claim；其 budget 不得
refill，也不得复制成多个 target row。更弱但承重的 debt identity 只锁 lineage+claim：即使 handoff
改变 anchor、incidence、carrier、degree、responsibility presentation 或 clock，该债仍不得 refill/clone。
非平凡 split 的每枚 child 都必须相对共同 parent 严格扣减 `progressBudget`；因此领域不能在下一 carrier
重新 canonicalize 一份相同额度，再把跨拍续杯伪装成新的局部坐标。
target ledger 每一行必须由唯一root law在该occurrence上的dependent-face realization
穷尽判为旧债 continuation，或证明对 complete old ledger
构造性 fresh；不能仅因它已出现在新 root 就自称新 admission。局部 terminal 与另一枚 cofinal landing
可以同时存在，只要二者都属于同一 admitted source inventory。handoff 的 event/next root 还索引完整
source-level causal history；finite、cofinal 与 post-cofinal 的同名 current 不是同一续期 occurrence。

## Ledger authority 不可拆卸

[`LivingLawRootCausalEntryAuthorityKernel.lean`](../../../../SaturationMonoid/LivingLawRootCausalEntryAuthorityKernel.lean)
的 causal-entry authority 以完整 authoritative/living root、exact visit 与 exact row 为类型索引，
constructor 私有。公开生成只来自 initial/cofinal canonical row，后继只来自同一 whole-ledger fold。

[`LivingLawRootCoreRepresentationKernel.lean`](../../../../SaturationMonoid/LivingLawRootCoreRepresentationKernel.lean)
进一步让 causal world 的 occurrence、evolution、`Process` 与 `FaithfulRealization` 保留完整 source root；
共享 lower ledger 的 sibling projection law 不再拥有同一 causal-world 类型。

ordinary row evolution只有三种：

- carry：同 support、同 dependent entry；
- maintenance：同 standing，严格扣 debit；
- transfer：有 source-owned transfer receipt，保持 lineage/claim，且不得 refill。

只有 exact settlement 可以关闭旧 row。换 bearer、换 carrier、换 degree 或换语言若改变 standing，必须
在同一 root transition 中显式成为 transfer、new admission 或 semantic change；不能把旧债重命名成 fresh。

## Domain face 只是 root restriction

[`LivingLawRootAuthorityFactorizationKernel.lean`](../../../../SaturationMonoid/LivingLawRootAuthorityFactorizationKernel.lean)
把已安装 subsystem outcome 因子化为：

```text
exact temporal root token
+ dependent projection outcome
+ source-generated next current
```

同一因子化已提升到完整 `SourceNativeLivingRootProcess`：当前 process state 先决定 living root 与
temporal visit，face 与 next living current 再由该拍的 root compiler共同读出。下一拍即使使用异质
carrier、weight 或 vocabulary，也不能借新 presentation 改写上一拍的 occurrence、ledger 或 face。
任意 faithful executor 也必须经过这枚 process-state factorization，而非只有 canonical executor 受限。
joint readout 同样一次恢复两枚 installed component outcome、共同 occurrence 与同一 successor；
因此一个 grounded component 不能在换拍或换 event presentation 时替 sibling component 借权。

固定 source process 内，隐藏 premise 也不能绕开这条链：
`canonicalAnswerAndNext_heq_of_current_eq` 证明完整 registered current 相同即 exact
answer-and-next 同一；`successor_difference_reflects_current` 反向证明 next world 的任何差异已经在
当前 registered current 中显影。若一枚外部参数真改变 evolution，它只能改变 source identity 或
current；否则仍是条件推理，不能影响这枚 fixed world。

领域不能另建 registry、court 或 domain root。两个领域的共同性来自同一 root occurrence/coface 的
不同 restriction；若当前没有共同 coface，必须生成 contact occurrence 或 exact obstruction，而不是现场
提交 comparator。

Authority 也不在 record 字段之间传染。一个 grounded 字段不能替 sibling answer、ledger row、theory、
semantic change 或 consumer 取得权威；`Grounded A` 不推出 `Grounded (A × B)`。

会影响 next 的 effect face 还受
[`LivingLawRootEffectDynamicalClosureKernel.lean`](../../../../SaturationMonoid/LivingLawRootEffectDynamicalClosureKernel.lean)
约束：effect、operational scale/time 与 exact live row都由同一 lower occurrence 生成；next 必须携 target
effect、whole-effect commuting、whole-ledger transport，以及 actual change 或 strict debit。无法生成 next
时，同一 row 进入 U7 cut，不能把 `CutAt` 写成空 fibre；同一 fixed visit 的重复注册也只能读出同一
完整 effect disposition。

## Inquiry 与 U7/U8

[`LivingLawRootInquiryCompletionKernel.lean`](../../../../SaturationMonoid/LivingLawRootInquiryCompletionKernel.lean)
只公开 `Engine.ask`。返回值是一枚 `ExactRootInquiryOccurrenceAt`；answer、receipt 与 next 都是该
occurrence 的 restrictions。下一 node 若仍开放 inquiry，普通分支必须保留完整 living root，U8 分支必须
落到同一 failure 生成的 revised living root；只相等于 authoritative erasure 不足以续接。调用方不能提交
result、answer face、failure、revision candidate、branch 或 sibling terminal-handoff law。

U7/U8 的完整合同见
[U7/U8 mechanism](../runtime/u7-u8-no-free-idealization.md)。本层只要求：failure 必须是 fixed root occurrence
的 installed face；U7 demand 的 entry 与 settlement/redirect/theory-audit disposition 必须同时等于
whole-root compiler 的同一 live row；redirect只有严格消耗该row的budget才取得inquiry-answer
authority；minimal coface/revised first write 不能换 root 或换账。

## Atom / field 边界

[`LivingLawRootAtomFieldAuthorityKernel.lean`](../../../../SaturationMonoid/LivingLawRootAtomFieldAuthorityKernel.lean)
只给 source-generated finite section 以 atom authority。完成 future field 可以作为 derived field/readout，
不能穿成 current atom；atom projection 也不能替未提及的 sibling future 接地。详见
[atom-field mechanism](../ontology/atom-field-living-evolution.md)。

## 硬边界

合法：

- primitive source 多样性；
- 小 source、`PUnit` projection、函数空间与无限 ambient mathematics；
- local terminal、transfer、U7/U8 与不同 law epoch；
- 条件模型和 hypothesis sandbox。

无 authority：

- 裁剪 actual inventory 后自称 terminal；
- sibling source/row/face receipt 重放；
- projection payload、inhabited type 或 theorem-shaped premise 直接改变 world；
- 完成未来、comparison oracle 或 anonymous semantic bit 冒充 current occurrence；
- 未经 root registration 的 domain executor。

一句话：不同 source 可以真实不同；固定 source 与 exact occurrence 后，不再有 outcome 自由度。

## 验收

- `LivingLawRootSourceNativeAuthorityRegression.lean`：terminal 裁剪、branch 重标、cofinal 插入/擦除；
- `LivingLawRootAtomFieldAuthorityRegression.lean`：完成未来与 sibling-field authority；
- `LivingLawRootCoreRepresentationRegression.lean`：复合字段 authority 不传染；
- `Tracks/LivingLawSingleRootAuthorityFacadeRegression.lean`：唯一 active firewall；
- `lake build LivingLawActive`。

构造性 root authority 与 inventory theorem 必须保持 `#print axioms = []`；Mathlib field/quotient
结果只作为 adapter/readout。Axiom audit在checkpoint按需生成并记录结论，不把`#print axioms`
诊断常驻 active facade。

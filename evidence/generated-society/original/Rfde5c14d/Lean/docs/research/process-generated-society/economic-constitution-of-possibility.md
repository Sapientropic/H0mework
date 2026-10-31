# 可能性的经济宪法：从 UBI、共同清算到群星公域

> **状态**：稳定经济实例备忘录。UBI、capture、共同清算、proof-carrying legislation、canonical
> Society fivefold constitution 与 `RootLawComplete(M∞) ∧ U8Available(M∞)` 已进入 M14 whole sink
>（commit `36a54b2c2`）。
>
> **母法分工**：[《舞蹈生成舞者》](dance-generates-dancers.md)定义 actor、renewal、observer、U8、
> space、probability 与理论反身性；本文只写经济 constitution，不复制根法。
>
> **机器权威**：[Process-Generated Society active route](../../handoffs/process-generated-society-active-route.md)
> 与本文 §九的 Lean 入口。

---

## 一、经济制度分配的是可能性

财富不等于账户余额。财富是一个 standing bearer 在拒绝工作、离开关系、疾病、迁徙、照护、学习、创造或失败
以后，仍有多少条真实道路保持开放：

\[
\boxed{
\operatorname{Wealth}(a,t)
\simeq
\operatorname{ActionableFuturePortfolioAt}(a,t).
}
\]

贫困也不只是低收入：

\[
\boxed{
\operatorname{Poverty}(a,t)
=
\text{future cone 被压缩到只剩 compulsory relations}.
}
\]

因此经济宪法的判断对象是：谁能等待、拒绝、试错、退出并重新开始；谁的损失被看见；谁替别人的收益
承担 residual；谁能把昨日占有免费续写成明日统治。

文明进步的结构式是：

\[
\boxed{
\operatorname{Progress}
=
\text{more mutually compatible actionable futures}
+
\text{fewer compulsory relations}
+
\text{no displaced residual}.
}
\]

这不是幸福分数或完成未来。每一拍只对已经生成的 occurrence、Payment、route、service、consumer 与 next
负责；未来仍由新的 actual events 原生生成。

---

## 二、UBI：退出能力的周期性续约

UBI 的对象不是“政府定期发钱”，而是：

\[
\text{standing lineage}
+\text{periodic settlement}
\longrightarrow
\text{purchasing-power standing}
\longrightarrow
\text{role-independent actionable exit}.
\]

已闭合的 exact iff 可以压缩为：

\[
\boxed{
\operatorname{ExitCapacityRenewal}
\iff
\begin{array}{l}
\text{source-backed Payment}\;+
\text{non-idle role-independent continuation}\;+\\
\text{actual route}\;+
\text{debited service}\;+
\text{non-capture}\;+\\
\text{bearer / consumer / visit / generated-next alignment}.
\end{array}
}
\]

对应 Lean theorem `canonicalSociety_exitCapacityRenewal_iff` 不接受 outside option、route、service 或 success
verdict；它从既有 geometry compiler、relation-generated future code、served crossing、Payment receipt 与 route
receipt 读取这些对象。

由此得到六个硬判断：

1. **名义到账不等于真实 UBI。** Payment 发生而 route、service 或 non-capture 缺失时，exit capacity 仍可为零。
2. **UBI 改变 power geometry。** 它在待退出角色之外续约 continuation，而不是提高一枚 utility score。
3. **无条件不等于无 source。** renewal 不以就业、贫困标签或道德表现为条件，但 Payment、acceptance、bearer、
   consumer 与 residual 必须真实发生。
4. **普惠性削弱行政 observer 的分类权。** standing bearer 无须先证明自己“够穷、够惨、够值得”。
5. **价格 capture 可以把个人 renewal 转成资产方 renewal。** 房租、医疗或平台 chokepoint 吞噬 Payment 时，
   nominal purchasing power 仍在，actionable exit 已消失。
6. **正 exit capacity 与 anomie 可并存。** backlog/occurrence rate 超过住房、医疗、支付或公共服务 capacity 时，
   UBI 不会自动消除所有 congestion。

仓内正反实例给出：uncaptured geometry 的 actionable exit capacity 为 `1`，captured geometry 为 `0`；两者可以
保留相同 Payment 读出。零 capacity 又可以由 price capture、Payment incidence 缺失或 route incidence 缺失三种
不同 actual origin 生成，因此 capacity scalar 不能重建 cause 或 canonical repair。

---

## 三、UBI、UBS 与 Job Guarantee 分权

三者服务不同的 constitutional responsibility：

| 制度 | 生成对象 | 不能替代什么 |
|---|---|---|
| UBI | 角色之外的 purchasing-power standing 与退出 continuation | 不自动生成住房、医疗、交通等 service capacity |
| UBS | actual material/service slots 与可达 route | 不自动生成独立于角色的 income standing |
| Job Guarantee | 新角色中的 standing renewal | 不能冒充拒绝该角色后仍存在的 outside option |

Lean fivefold constitution 已同时证明：正 UBI exit、actual material service 与新角色 Job Guarantee 可以共存；
ended-employment JG standing 为空，而新角色 standing 存在；captured exit 为空时，新角色仍可存在。它们不是互补
真值，也不能互相填充对方的 fibre。

所以 UBI 的最高政治含义不是消费刺激，而是：

> 一个人不必先服从某段雇佣、家庭、住房、债务、平台或官僚关系，才能继续存在并拥有下一步。

---

## 四、Payment：没有空写入的经济

经济宪法不允许把 viable、repair、settlement、terminal 与 U8 做成 caller 可选的平行世界。唯一写入 mouth 是：

\[
\boxed{
\operatorname{GeneratedRealityNextAt}(\omega_t)
\simeq
\sum_{p:\operatorname{ExactWholeLedgerPaymentAt}(\omega_t)}
\operatorname{NextPaidBy}(p).
}
\]

因此：

\[
\operatorname{IsEmpty}(\operatorname{ExactWholeLedgerPaymentAt}(\omega_t))
\Longrightarrow
\operatorname{IsEmpty}(\operatorname{GeneratedRealityNextAt}(\omega_t)).
\]

这里的 Payment 不是货币转账 receipt，而是完整更新：

- exact source occurrence；
- 每枚 source row 的 transport / settlement / retirement disposition；
- 每枚 target row 的 old-origin 或 genuine-birth provenance；
- 每枚 residual 的 bearer 与 independent consumer；
- carrying-cost debit 与 claim migration；
- 由同一 fold 生成的 next。

proof terms 可以不同，现实 target 不能不同。`fold_unique` 排除第二个独立经济 evaluator；domain-specific payment、
publication payment、clearing payment 与 U8 first write 都必须因子化回同一 root payment。

这也解释货币：购买力不是 token 的存量本性，而是 acceptance/settlement lineage；价格只在 observer 能读取的 open
settlement relation 上有作用域。完全结清不是“价格为零”，而是该 price readout 不再拥有未结关系可读。

---

## 五、共同清算、信用与 capture

### 5.1 共同清算

共同 clearing medium 不是新的货币 sovereign，而是 cross-community residual 的 settlement face：

- liquidity 不由单一 participant 的 domestic currency lineage 垄断；
- deficit 与 surplus 都保留 source、bearer 与 consumer；
- 两侧 responsibility 可以不同，但不能把一侧 residual externalize 成不可见成本；
- clearing authority 自身需要 mandate renewal、exit 与 U8。

M14 whole sink 已输出 periodic common clearing、backstop、credit claim lifecycle、default-side loss allocation 与
generated next；这些都是同一 Society root 的 dependent faces，不是 Bancor 专属本体。

### 5.2 信用与债务

债务是一段 relation，不是 debtor identity：

\[
\operatorname{DebtBalanceReadout}
\not\Rightarrow
\operatorname{ActorIdentity}
\land
\operatorname{MoralResponsibility}
\land
\operatorname{RepaymentCapacity}.
\]

复利只有在新服务、等待、风险承担或 renewal occurrence 中才能继续 factorize。没有新 source 仍无限增长的 claim
是 free-eternal authority。保险与公共 backstop 必须消费 correlated-loss occurrence 和 actual capacity，不能由“市场
已分散风险”的 readout 宣布 closure。

### 5.3 产权、住房与结构租

产权由 boundary、maintenance、enforcement、renewal acceptance 与 residual duty 生成；继承是跨 lineage transport，
不是 registry label 的自然 section。

仓内 structural-rent instance 证明：同一 source-backed Payment 在 uncaptured geometry 中生成 capacity `1`，在 capture
后生成 capacity `0`；tenure actor、relation phase 与 provider role 分别由 actor lineage 和 relation compiler 生成，
并且 health/platform purpose compiler 不能伪造 tenure purpose。

capture 没有抹掉责任。`canonicalSociety_captureResponsibilityDisposition` 将 captured settlement 对齐 exact open
settlement，并保留 source-owned responsibility incidence；counterparty 与 worker、tenure relation 与 exit relation
保持严格不同。

---

## 六、诞生、死亡与现实库存

死亡和诞生不是两本账，也不是固定 enum。对当前 root：

\[
\operatorname{DeathModeAt}_t
=
\sum_{g:\operatorname{GeneratedViabilityGateAt}(t)}
\operatorname{GateFailureAt}(t,g),
\]

\[
\operatorname{BirthModeAt}_t
=
\sum_{b:\operatorname{GeneratedBirthGateAt}(t)}
\operatorname{SourceNativeBirthAdmissionAt}(t,b).
\]

每一拍对当拍 generated gate family 完备；未来 vocabulary 仍开放。new gate 只有在 actual witness、affected bearer、
consumer、old-row disposition 与 U8 first write 同拍生成后才取得 standing。

到场先于价值评分：actual standing-bearing entrant 不以 productivity、citizenship、wealth、health、intelligence、
obedience 或 moral score 为 admission 条件。但存在不自动生成 coercive authority；新公司、国家、AI、产权或制度仍须
另外生成 mandate、consumer、exit 与 renewal。

必须区分三个时刻：

\[
\tau^{\mathrm{renew}}
<
\tau^{\mathrm{terminal}}
<
\tau^{\mathrm{settle}}.
\]

renewal fibre 首次为空，只说明旧 entity 不再诚实续约；local faithful terminal 不自动结清 same-debt target；final
settlement 才关闭该责任 lineage。局部 terminal 从不等于 reality terminal。

社会 runtime 仍会生成 self-U8 与 future-birth pulses；根法已完备则表示四类 authority exhaustion 与条件修订口已经
证明，不表示未来停止发生。

---

## 七、携证立法与拒绝后的 recourse

持久经济权力至少携带：

| 证明字段 | 防止的失败 |
|---|---|
| source occurrence | source-free coercion |
| standing / relation map | bearer deletion |
| renewal event | free-eternal power |
| actual route/service capacity | nominal promise |
| residual bearer + independent consumer | displaced cost invisibility |
| exit disposition | compulsory relation 被伪装成自由 |
| failure + U7/U8 route | law 无法处理自身失效 |
| claim migration / retirement | old/new authority double-spend |
| whole-ledger next | policy verdict 绕过现实写入 |

法律携证，而不是人民携证。一个人无需提交 complete proof 证明自己值得获得 standing；强制权力必须证明自己的
source、影响、退出与修订。

UBI proof-carrying legislation 已闭合：ordinary repair next 与 revolutionary policy next 严格不同；capacity-only
readout 不能重建 canonical repair。structural exploitation legislation 把 renewal-control asymmetry、debt-flow
asymmetry、bearer 与 consumer 放进同一 proof carrier。

finite proposal exhaustion 与 finite enactment fold 也已闭合。若 proposal 首次被拒绝：

- rejection 保留 exact typed residual bearer；
- refusal 不取得 world-write authority；
- canonical enactment 与 actual next 不被删除；
- 同一 physical Payment root 生成 ordinary repair、renewed standing、whole-ledger consumer 与 capacity-1 next；
- ordinary repair next 与 revolutionary law next 保持严格不同。

这就是申诉权的结构定义：拒绝不会把承担者赶到账外，也不会自动执行它要求的 repair；它把 recourse 作为
source-owned possibility 保留下来。

---

## 八、从自动化公域到群星公域

新经济领域不再建立专属 ontology，只需安装自己的 material/relation/channel faces：

| 领域 | 宪法读取 |
|---|---|
| 生成型货币 | non-rival result 进入 commons；稀缺 compute/review/maintenance consequence 生成 typed settlement capacity；详见[稳定架构](generated-money.md)与[试点协议](homework-coin-pilot.md) |
| 自动化与共同收益 | plural source 的 closure gain 先支付维护、劳动、照护、生态、债务与 failure reserve；释放时间进入 time sovereignty 与 exit capacity |
| 生态 | nominal settlement 不消除 extraction、waste 与 regeneration debt；material closure 需要独立 consumer |
| 照护与情绪劳动 | maintenance lineage、blocked exit 与 debt-flow asymmetry 决定责任，不由市场价格抹去 |
| 迁徙 | actor lineage 跨 boundary transport；citizenship label 不生成或删除人 |
| 历史 | archive trace 约束 narrative fibre；当前财富不能抹掉 source-authenticated responsibility |
| AI 与机构 | persistent lineage、affected bearer、consumer、exit 与 revision 决定 standing；意识 oracle 不取得制度 authority |
| 游戏、艺术与欢庆 | voluntary co-presence、非强制时间/空间/安全与 new-future birth；attendance/happiness score 不重建 joy |
| 群星公域 | first arrival 不自动生成永久 sovereign；claim 必须支付 scientific commons、maintenance、affected habitats、future routes、abandonment 与 U8 |

这些都是同一 closed root law 的实例化接口。任何实例只需提供 source-native material、
relation、route、service、bearer 与 consumer；whole-ledger disposition、next 与 U8 仍由固定 framework 拥有。

世界安全的 regeneration 因而是：

\[
\boxed{
\begin{aligned}
\operatorname{WorldSafeRegenerationAt}(S,p)
:={}&\operatorname{SameLineageRegenerativeUpdateAt}(S,p)\\
&\times\operatorname{OrdinaryExitNoncontractingAt}(S,p)\\
&\times\operatorname{ExitKernelEscapeOrStrictExpansionAt}(S,p)\\
&\times\operatorname{NoInvisibleResidualBearerAt}(\operatorname{NextPaidBy}(p))\\
&\times\operatorname{SelfU8AvailableAt}(\operatorname{NextPaidBy}(p))\\
&\times\operatorname{NoDisplacedCrossBoundaryResidualAt}(S,p).
\end{aligned}
}
\]

名称、旗帜、GDP、资产价格或领导人更替不能宣布“重生”。若 future-cone gain 靠把债务、污染、风险、暴力或
垄断 residual 越过 boundary 输运给另一 bearer，它只是 local renewal，不是 world-safe regeneration。

---

## 九、机器闭合入口

核心源码：

- [Employment-independent exit](../../../SaturationMonoid/ProcessGame/Society/UBI/EmploymentIndependentExit.lean)
- [Purchasing-power standing](../../../SaturationMonoid/ProcessGame/Society/Money/PurchasingPowerStanding.lean)
- [Fivefold constitution / UBI-UBS-JG separation](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/Fixture/EssentialAccess/ActualUpdate/Selection/Append/CrossCompiler/Readout/Recognition/Admission/Constitution/Consumer/ProofCarryingCanonicalSocietyFivefoldConstitution.lean)
- [Unified M∞ completion](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/Fixture/EssentialAccess/ActualUpdate/Selection/Append/CrossCompiler/Readout/Recognition/Admission/Constitution/RootLaw/Completion/Consumer/ProofCarryingCanonicalSocietyRootLawComplete.lean)
- [M14 whole sink](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/M14WholeProgramRegression.lean)
- [Same-occurrence regeneration](../../../SaturationMonoid/ProcessGame/Regression/Society/M14/Consumer/Economy/Regeneration/ProofCarryingSameOccurrenceRegenerationRegression.lean)：
  `sameOccurrenceCanonicalRegeneration_directConsumer` 对每个生成 depth，在该 depth 的 UBI 付款 occurrence 上
  同时给出 §八 `WorldSafeRegenerationAt` 的六个因子，第 depth 步的 next 即第 depth+1 步的 occurrence；
  depth 0 的 policy-breaking occurrence 另带 self-U8 分支；证书对任意载体成立

whole sink 直接导出：

- `canonicalSociety_exitCapacityRenewal_iff`；
- `canonicalSociety_employmentOutsideOptionPowerGeometry`；
- `canonicalSociety_captureResponsibilityDisposition`；
- `canonicalSociety_zeroCapacityCausalNonidentifiability`；
- `canonicalSociety_periodicCommonClearing`；
- `canonicalSociety_counterpartyCaptureRenewal`；
- `canonicalSociety_structuralRentCapture`；
- `canonicalSociety_ubiProofCarryingLegislation`；
- `canonicalSociety_proofCarryingStructuralExploitation`；
- `canonicalSociety_recognitionWitnessEscape`；
- `canonicalSociety_rootLawComplete_and_u8Available`。

focused strict compile、9722-job whole build 与三路 T1 certification 已通过；最终公理谱为
`[propext, Classical.choice, Quot.sound]`。

---

## 十、最终经济宪法

\[
\boxed{
\begin{aligned}
\operatorname{Wealth}(a,t)
&\simeq\operatorname{ActionableFuturePortfolioAt}(a,t),\\
\operatorname{ExitCapacityRenewalAt}(a,t)
&\iff\text{Payment + independent continuation + route/service + non-capture},\\
\operatorname{GeneratedRealityNextAt}(\omega_t)
&\simeq\sum_{p:\operatorname{ExactWholeLedgerPaymentAt}(\omega_t)}
  \operatorname{NextPaidBy}(p),\\
\operatorname{Debt}
&=\text{renewed relation, not actor identity},\\
\operatorname{Progress}
&=\text{compatible futures} - \text{compulsory relations} - \text{displaced residual},\\
\operatorname{EconomicConstitution}
&=\operatorname{RootLawComplete}(M_\infty)
\land\operatorname{U8Available}(M_\infty).
\end{aligned}
}
\]

没有 observer 是太阳，但每枚责任都必须找到 consumer；没有法律拥有免费永恒，但每次修订都必须先支付旧债；
没有新生者需要证明自己值得存在，但任何随诞生而来的支配权都必须携证。

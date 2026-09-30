# 总体实在与结构归属

> 状态：稳定原理 / mechanism card，非 active route，非 checkpoint 战报。
>
> 职责：从比 `NoMagic` 更弱的正向概念推出无外部补写，而不是把结论塞回定义。

## 非循环推导

框架不把 `NoMagic` 定义成“现实没有无根据事实”。它先区分六件可以独立实现的结构：

```text
Actuality
+ StableReference
+ RealDifference
+ RedundantPresentation
+ StructuralIdentity
→ InternallyDetermined
```

`InternallyDetermined` 是正向证据：一枚 actual、stable、real difference 连同它在整体中的
`StructuralIdentity`。它不是 `¬Magic`、`¬ExternalSupplement` 或任何同义否定。

一枚所谓 `MagicBit` 声称：差异实际成立、不是冗余 presentation，却没有任何正向 internal
determination。因此它先生成精确的 `ExternalSupplement` obligation：

```text
ActualDifference b
+ ¬ Redundant b
+ ¬ InternallyDetermined b
→ ExternalSupplement R b
```

`TotalRealityAt R` 的正向 mouth 也不提 magic。它要求每枚 actual difference 都被定位为：

```text
Redundant b ∨ StructuralIdentity b
```

于是：

```text
TotalReality R
→ ¬ ExternalSupplement R b
→ ¬ MagicBit R b
```

第一支与 `nonredundant` 矛盾；第二支原生构造 `InternallyDetermined`，再与其否定矛盾。整条证明
不使用排中选择、quotient equality 或逻辑等价铸成相等。

权威抽象接口是
[`LivingLawTotalRealityKernel.lean`](../../../../SaturationMonoid/LivingLawTotalRealityKernel.lean)。

## 准入条件，不是结论改名

抽象层允许单独谈`ActualDifferenceAt`、`InternallyDeterminedAt`与`ExternalSupplementAt`；因此
`InternallyDeterminedAt`没有循环定义成`NotMagic`，`TotalRealityAt`也没有`noMagic`字段。机器链严格是：

```text
actual + stable reference + real difference
+ nonredundancy + no positive structural identity
-> external supplement

positive total-reality location
-> redundant presentation | positive structural identity
-> external supplement impossible
-> magic bit impossible
```

`TotalRealityAt`不能由consumer提交后冒充world authority。它在抽象文件里只是表示定理的目标接口；合法
living-law讨论域必须由sealed root的actual occurrence、stable reference与structural identity原生实现它。对象若
没有这条realization，在本框架中只是尚未取得`lawful world`的操作性准入身份；这不裁决其数学真值，
也不把未登记命题自动判成魔法。

## 与 source-native root 的连接

抽象 `TotalRealityAt` 本身不授予 world authority。具体 living-law 世界必须从更低的 sealed root
生成它，不能让 consumer 把 totality classifier 当 premise 塞进 theorem mouth。

[`LivingLawRootTotalRealityAdapter.lean`](../../../../SaturationMonoid/LivingLawRootTotalRealityAdapter.lean)
给出第一枚构造性 realization：

- difference 是同一 source-native ledger root 内两枚 lawful temporal visit；
- actuality 由两枚 canonical temporal-visit compiler receipt 支付；
- stable reference 是两侧 exact registered root occurrence；
- real difference 是 visit inequality；
- redundant presentation 是 registered occurrence equality；
- structural identity 是 registered occurrence inequality。

finite、cofinal 与 post-cofinal state 共用同一 `registeredOccurrence_ne_of_ne`；它从 actual state
difference 生成最后一项，所以 root 的
`TotalRealityAt` 是 theorem，不是新字段。额外包装的 `Bool` 若不改变 root occurrence，就无法进入
`ActualDifferenceAt`；若它真实改变世界，则必须先成为新的 registered occurrence、residual 或 U8
责任。

该realization直接索引同一source-native root；旧constructive-representation facade已删除，
consumer直接读取generated causal support，不再保存`closed`组件或重新签发totality。root本身继而派生：

```text
exact temporal root occurrence
-> positive TotalRealityAt
-> no ExternalSupplementAt
-> no MagicBitAt
-> every actual nonredundant arithmetic decision is structurally grounded
-> no admissible arithmetic naked terminal
```

这里没有给representation增加`NoMagic`字段，也没有接受totality classifier、terminal decision或completed future。
零号律因此成为共同root proof graph的derived law，而非constructive integration facade中的相邻import。

## 本体边界

这不是“每件事都有更早原因”。结构归属可以表现为时间生成、同时关系、全局约束、结构必然、
自指闭合或与整体共同成立。它只排除一件事：某枚差异既声称足以区分两个现实，又拒绝任何
carrier、relation、incidence、trace 或 structural identity。

因此准确口径是：

> 凡实际成立的差异，必属于现实的整体结构。

否定者若能稳定指称该 bit、区分其有无并让断言不同于否定，就已经给出了 reference 与 relation；
若这些全都不存在，该 bit 也无法构成反例。Lean 层不把这段实行性论证当作公理，而以
`SourceNativeLedgerRootClosure → TotalRealityAt → ¬MagicBit` 的正向 producer chain 实现它。

## 数学与证明不在现实之外

数学实践、证明项、计算、符号、观察者及其解释映射都是actual occurrence；数学关系则是已固定结构的刚性
后果。因而数学模型不能成为账外魔法的避难所：同一结构与law epoch下，已成立的证明关系不会无登记地改口。

这不把所有可定义对象宣称为完成库存。`Nat → State`可以作为由同一write逐项生成的field/readout；它不能仅凭
函数类型取得current-atom authority。类似地，`Fin (n + 1)`是合法的条件结构，但“现实恰好在`n`终止”若要取得
actual-terminal authority，仍须由source-native terminal occurrence、同一source/current/law epoch的actual continuation
exhaustion（直接读exact root branch）、complete ledger discharge、结构闭合或typed semantic change支付。这里约束的
是实际standing与world claim，不是禁止纯数学研究假设结构。

## 现实前提的 grounding 律

条件假设只打开对应的数学 fibre。它的 authority 覆盖该 fibre 内的推演，不自动覆盖运行世界的
source、current、occurrence、disposition 或 next root。对任意 `h : P`，合法用法分为两类：

```text
h : P
-> 在条件 fibre 中推出 Q
-> theorem 最终返回 P -> Q 或消去 h 得到 False

actual source/current
-> exact emitted occurrence
-> compiler-generated grounding receipt for P
-> P 可以参与 actual evolution
```

一枚 premise 若会改变 actual evolution，它的 grounding 必须已经属于以下来源之一：

1. 当前 source state 的字段，并由该 source 的注册身份固定；
2. exact actual occurrence 的 canonical compiler image；
3. sealed root 的 positive structural identity；
4. 反证局部上下文，并在 public theorem 结束前被完全消去。

裸 `Prop` proof、classical choice、调用者提交的 classifier 或带参数 structure 只提供条件推演能力。
它们不能单独签发 actual event、选择 world disposition、改变 source identity，或让 hypothetical root
取得现实 standing。给定义加上 `sourceGenerated` 名称也不改变这条 authority 边界。

这条 law 封住“假设洗实”：先在数学上下文任意加入 `P`，再让依赖 `P` 的 source constructor
获得 actual authority。现实的绝对刚性同时约束 theorem 结论与 theorem mouth；现实差异所依赖的
premise 也必须由现实内部赚取。

固定 source process 内这条边界已经由 registered-current 反射性闭合：完整 current 相同则 exact
answer-and-next `HEq` 同一；next world 若不同，当前 registered current 必先不同。裸 premise 因而只能
留在条件 theorem 中，或显式生成另一枚 source/current identity；不能在同一 fixed world 内暗改 evolution。
领域 producer 仍须把实际影响写入 source state 或 exact occurrence，而不能把条件证明误报为该固定
source 的 authority。

## 一证永证的精确含义

形式证明一旦实际固定命题、定义、对象、域与推演结构，它就成为已登记的 structural fact。后来
可以发现当时证明的是另一命题、用了错误 translation 或改变了 law epoch；这些都必须登记 semantic
change。不能在完全相同的结构身份下保留原证明关系，又凭空补入相反 outcome。

无时态真理内容不需要续费；某份证明在运行世界中的 standing 则仍需 faithful survival 或 actual
renewal。二者不可混写。

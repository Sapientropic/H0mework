# Source operation semantic derivations

## 原始推导与生成合同

`Expr` 与实际 environment 决定一次有限运算。`Derivation environment left right : Type`
保存可重放的对象级推导树；构造子只有源变量绑定、常量上的实际 add/additive/bilinear 运算、
运算 context 与等价闭包。构造子不接收任意语义等式。

```text
source bindings + actual operations
→ recursive normalize : Derivation env e (const (eval e env))
→ sound / typed substitution
→ finite raw relation words + existing scalar relations
→ complete semantic kernel
→ existing coimage / exact complex / actual history fibre
```

`normalize` 逐语法构造子生成证明数据；`subst` 在变量绑定处运行被替换项的 normalization，
不用外加 commuting equation。`of_eval_eq` 与 `nonempty_iff` 刻画已有端点等式的语义 fibre，
是 transporter；normalization 与 raw relation producer 不调用它们。

## 完整关系核

`Formal_R = Expr →₀ R`；系数来自实际 `CommRing R`，值保留原 `Module R`。
`RelationIndex R` 是源推导树的两端与既有 `ScalarRelationPresentation.RelationIndex R` 的和。
前者生成 `[left]−[right]`，后者经 constant embedding 保留原值 carrier 的全部加法/标量关系。

`normalizationCertificate` 给每枚形式对象生成有限的推导词，直接证明：

```text
relationMap (normalizationCertificate word)
  = word − constantMap (valueMap word)
```

既有 scalar `presentedEquiv` 消费右端值关系，得到
`range relationMap = ker evaluation`。这里的完整性是固定实际 environment 的有限操作语言
语义完整性；它没有决定未知端点是否相等。既有 coimage 精确保留全部 fibre，
`presentationComplex_exact` 由该等式生成 exactness。

先前 update boundary 仍是原来的 boundary；它的像进入这个完整生成关系核。
不能据此把原 update-boundary homology 改写成零。

原 primitive 仍只有 AddMonoidHom/bilinear-additive 要求；formal 线性化不把 primitive 升格为
R-linear。Effect、MixedTrace 和 raw normalize 直接复用；旧 ℤ APIs 只作同一 producer 的特化。

原 Proper-Mellin incidence 的 `actualDegreeOneMap/presentedDegreeOneMap` 直接消费新 ℂ evaluation
和 scalar certificate，原 observation/stage/root、degree-one differential 与完整 C-readback 同 proof
保留。生成的 `[const(I • value)]−I[const value]` 是原 ℂ-module 的关系，不是仅做整数 base change。
既有 conjugateFreeReadout 区分 addition 与 complex scalar laws；ZMod 2 的零 effect 与原整数
effect=2 保持为不同系数模型，不作非零输运。

## 完整 inventory 与原 root

`liftExpr` 把原 carrier 送到 `(old, effect)` 配对模型。双线性作用原生生成：

```text
(a, da) ⋆ (b, db) = (a⋆b, a⋆db + da⋆b + da⋆db)
```

`evaluation_liftMap` 精确等于已付 `updateInventory`，保留两个有序 cross 与 joint increment。
因此上述同一个关系 producer 覆盖完整 old/effect fibre，未遗忘实际更新。

原 Fock root constructor 的 `operationDerivation` 由同 `nativeWrite` 的 source/target 生成。
`OperationDerivations.source_update` 消去该 receipt，再消费原 coimage，给原 state 更新。
cofinal stage 直接消去已安装的 receipt，不重新运行 normalization。
`stage_derivation_factorizes` 同 proof 消费 receipt、installed readout、occurrence、whole-ledger 与 next。

`envelope_fibre_generated` 把原 envelope 的全部 fibre 精确改写为每个实际 material stage 的
生成关系范围；bounded index 覆盖来自同 sealed history。原 source 非零/零关系均保留，
没有把普通 semantic equality、raw proof word 或数学归约当作 base debt 的 strict payment。

## 实际模型 scope 与量词证据

`SourceOperationLogic.Scope e` 复用原 coimage，`q` 是其 canonical quotient；
`scopeEquivRange` 只识别 `e` 的实际 image。exists/pullback/forall 直接消费既有
`Set.image / preimage / kernImage` 三联伴随，substitution 直接消费已有 differential square。
`fibreDecomposition` 与 sigma/pi equivalence 保留全部源代表；没有选单代表的接口。

对原 `sourceMap depth`，`generatedWordEvidence` 从有限 syntax 与每个实际 stage 原生生成
normalization certificate；`allModelEvidence` 把这个算法放回每个完整模型 fibre。
它不接收完成的 witness table。`actualTermEvidence` 则直接消费原 root 已安装的 proof tree，
存在见证同时保留原 source word 与该证据。dependent elimination 用被保留的 proof.sound
读出原 state，再在同 proof 中消费 occurrence/whole-ledger/next。

实际 source 点的每个代表都经完整语义 fibre 读取同一 target。
一般谓词/Type family 的伴随与传输不自行生成真值；这里的 witness、归约覆盖和 state 读回
来自具体 source 算法。Formal→完整 envelope 未被证明满射，量词不越出实际 coimage scope。
沿实际 update、完整 prefix 与 retained source 的动态量词/下一拍见证见
[witnessed dynamics](source-operation-witnessed-dynamics.md)。


## 承重 forward 证明运输的实际 Trace

`Execution.Substitution.Source`逐原forward Step/Trace重放source binding。bind运行现成execution(body)，其余primitive和context逐Trace运输；Var可改变，Sorts/Value/原单位保持。完成费用来自展开后源语法，完整relation边界从该actualTrace生成，无目标等式或normalizer输入。

`Native.Context.Execution`运输原forwardStep的sort，源observer binding实际执行，再由原native binding重放。原Fock读已有sourceTree/runtime真实next的完整pair并认回same target Type；raw10的actualTrace13含所有中间primitive。Type proof/旧receipt与新Trace分别保留，不因同值/同boundary/费用相等强HEq历史。

`Substitution.Installation`逐suppliedo保存原whole/physical材料、源binding/replay/raw与Fin(B＋1)全部gen/patch/cert/Box。before-emitter reader交原Shared Programme；normal读完整rebound old/effect，sourcechargedState/whole经原cofaces认回并实际strict付款，母全countQuery/Answer/debtCurrent/next保持。generic binding是源语法data，live Physical固定原Context.binding/原General.initial。

binding1→3、constant1→0；同值0的常量与读取后作用费用0/2不同，不能同值压缩来源。现成cofinal、逻辑fibre与Model直接消费该runtime/σ源词，各依原稳定机制。

权威：`GenericFoundation/Operations/Execution/Substitution/{Source,Installation/Family,Installation/Mother,Installation/Physical}.lean`、`Native/Context/Execution.lean`及原Fock`.../Context/Execution/Source.lean`。

## 权威源码

- `GenericFoundation/Operations/Derivation/Reduction.lean`：原 coefficient-independent 推导树。
- `GenericFoundation/Operations/Scalar/{Relations,Boundary,Complex,InventoryLift,Presentation,Exact}.lean`
- `GenericFoundation/Operations/Derivation/`、`Cochain/`、`Relations.lean`：原 ℤ specialization。
- `GenericFoundation/Operations/Regression/Derivation.lean`
- `GenericFoundation/Logic/SourceScope.lean`
- `NoIslandNoMagic/CanonicalRiemann/QRich/OperationScalarRelationConsumer.lean`：原复 cochain 的直接消费。
- `NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/State/OperationDerivation.lean`
- `NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/Cofinal/OperationDerivation.lean`
- [operation effect / cochain / cofinal / envelope](source-operation-effect-trace.md)

实时责任只见 [maximum active route](../../../handoffs/no-island-no-magic-mathematics-active-route.md)。

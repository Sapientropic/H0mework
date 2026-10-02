# 原作用、观察 fibre 与动态闭包

实际作用 `A : C →ₗ[R] C` 与原观察 `e : C →ₗ[R] B` 直接消费已有
scalar differential coimage `q : C → C/ker(e)`；无需先提交目标作用或交换方块。

```text
完整 source / actual A / 原 e
→ actionDefect := q ∘ A ∘ ker(e).subtype
→ 原同 fibre 的 next 差额 = actionDefect(left − right)
→ jointObservation := (e, e ∘ A)
→ joint coimage 的 current / next 两枚限制
→ 原 installed face、whole ledger 与 literal next
```

## 生成合同

`actionDefect` 保留整个旧不可见子模，而非挑选一枚代表。商作用存在且唯一恰当
`actionDefect=0`；正支由已有 quotient universal factorization 生成。非零坐标直接证明
原 action 把旧 fibre 分开，不改原 source 或把普通 residual 报成 U8。

联合观察的完整 fibre 恰是原 `e` 和实际 `e∘A` 两 fibre 的交。`jointCurrent` 与
`jointNext` 从这枚 coimage 生成两读，不从当前标量猜下一标量。完整 future Model 的
最大不变核与原作用继续使用既有 [自主 Model](../algebraic/source-generated-observation-history.md)。

## 完整 operation field 的逆 fibre 恢复

设 E、E_next 是同一原 source 的当前及 literal next 完整 cofinal completionMap，
J₀ 是当拍完整 `(old,effect)`。原 successor_source 支付 differential square，其
sourceMap 为 Id；完整核生成 `ker E = ker J₀ ∩ ker E_next`。既有 FibreLift 的
`LiftingResidual = ker E_next / range(kernelMap)` 因而线性等价于
`range(J₀|ker E_next)`，无需选择代表或补空间。

`recover_liftingResidual` 严格恢复 `J₀(target−source)`；recover 单射，residualEquiv
满射到实际像。原 stage 更新方程又生成恢复两值之和为零，但旧 fibre lifting
恰当整对为零。原 Native.Field 保存完整 State 点，installed Fock action 认回
原 updateInventory；原 receipt、facade、整账与 next 联消。

任意 depth 的源 selector 词在整个 next future 为零，当拍却为 `(point,−point)`；
其现成 liftingResidual 非零，排除从薄 next field 直接恢复旧 field。完整 parent
history 仍保留旧发生；这是忠实表示内的逆问题残差。

## 原 prime action 的直接消费

原 `ParticleWaveFockRuntime` 的 installed payload 保存 `nativeRuntimeAction`，由原
canonical unit process 的 successor 生成。它作用在完整 source 自由词上，且在本次
原 source 点读回 `nativeWrite.actionTrace` 所生成的 target；原 emitter、receipt、
operation inventory、Fock 方程和账行共同保留。

任意 prime、stage 和完整原词生成精确方程：

```text
sourceRow(p,stage)(A word)
 = sourceRow(p,stage)(word)
   + if cut(p)≤stage then 0 else word(cut(p)−stage−1)
```

`cut≤stage` 时原 mass 守恒生成商作用。`stage<cut` 时原
`δ_(cut−stage−1)` 当前读 0、作用后读 1，排除旧单读口的商作用；联合 fibre 完整保留
这枚系数。该方程消费原 `certificate_push`，没有输入非零、cancellation 或 terminal。

`runtime_action_joint_fibre_ledger_next` 从同一 `.particleWave` face 取 action，消费
`coversAt_factorizes`，联合保留原 nativeWrite、wave/particle 状态更新、整账与 next。
原 unit 行预算为零、处分仍是原 transfer；新观察消费不记作 strict debt payment。

## 原 prime 的有限全未来实现

原每个 prime 的作用还生成 `e_p A^n=sourceRow(p,n)`，从 `cut p` 起等于原 mass；
最后一项为 1 的原系数因而给出饱和递推。既有 `FiniteRecurrence` 直接生成 `0..cut`
prefix action 与全未来 kernel/fibre。`modelWindowRead/recoverWindow` 在实际窗口像上
恢复该 prime 的 Model，并保存原动作；任意更短 prefix 的原词全读零、下一读一，
所以长度精确。不同尾源点仍可落入同一单 prime Model，不宣称这枚读口恢复完整源。

`runtime_finite_model_material_ledger_next` 从原 generated material history 逐拍读
真实 samples，并联原 Fock receipt、整账、literal next 和 history target。

## 原 Physics 函数环 span 的动作消费

`MotherNativeQuery.ActionFeed` 从原 declarationSource 的 installed RawAt 消元 evaluator；
四字段保留原 exposure/seed/continuation/evaluator。完整 `State×Generator` 的原函数环
系数词只由原 process.successor 推进 occurrence，generator 与任意函数系数保持。
`whole_value_slice/whole_action_slice` 认回当拍原 valueWordEvaluation 和 literal next。
既有全未来 Model 直接消费此作用与 evaluator，生成 exact future fibre；原 coimage
recovery 再读回当前切片，并联原 inquiry residual、整账和 next。

范围为原 sealed unit-emitter 链。原其他正 duration 库存保持；normalizer 的 soundness
是语法读出。旧 query 属于其 exact parent occurrence，原 materialHistory/installedProjectionRead
已能恢复；跨不同发生的 closure/relation transport 须有原作用律。这枚新消费不作为
strict payment 或 controller advance。

## 权威源码

- [通用 action fibre](../../../../SaturationMonoid/GenericFoundation/Operations/Observed/Action.lean)：
  `action_exists_unique_iff`、`fibre_action_equation`、`joint_fibre_iff`。
- [原源方程](../../../../SaturationMonoid/NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/SourceHistory/PrimeField/Action/Equation.lean)：
  `source_action_equation`、`coimageAction`、`invisible_word_current/next`。
- [原安装消费](../../../../SaturationMonoid/NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/SourceHistory/PrimeField/Action/Consumer.lean)：
  `joint_fibre_retains_increment`、`runtime_action_joint_fibre_ledger_next`。
- [原 facade](../../../../SaturationMonoid/NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/Root/LivingLawCanonicalParticleWaveFockRootRuntime.lean)：
  `RootGeneratedParticleWaveCurrentAt.nativeRuntimeAction`、`coversAt_factorizes`。
- [原饱和递推](../../../../SaturationMonoid/NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/SourceHistory/PrimeField/Action/Saturation.lean)、
  [实际窗口恢复](../../../../SaturationMonoid/NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/SourceHistory/PrimeField/Action/FiniteModel.lean)、
  [原 material 消费](../../../../SaturationMonoid/NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/SourceHistory/PrimeField/Action/MaterialConsumer.lean)。

- [原 Physics span source](../../../../SaturationMonoid/PhysicsCore/Stage10/SourceUniqueness/Formation/Declarations/NativeQuery/Action/Source.lean)、
  [原 Model/coimage/inquiry consumer](../../../../SaturationMonoid/PhysicsCore/Stage10/SourceUniqueness/Formation/Declarations/NativeQuery/Action/Consumer.lean)。

- [完整field源方块](../../../../SaturationMonoid/GenericFoundation/Operations/Runtime/Fibre/Source.lean)、
  [原lifting residual无损恢复](../../../../SaturationMonoid/GenericFoundation/Operations/Runtime/Fibre/Recovery.lean)、
  [原Fock inverse-fibre consumer](../../../../SaturationMonoid/NoIslandNoMagic/CanonicalArithmeticState/ParticleWave/Fock/Runtime/SourceHistory/Operation/Fibre/Consumer.lean)。

实时责任只见 [maximum active](../../../handoffs/no-island-no-magic-mathematics-active-route.md)。

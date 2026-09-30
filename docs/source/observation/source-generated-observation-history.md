# Source-generated autonomous observation model

## 同一个 action 的完整观察

原 `A : C →ₗ[R] C` 与 `o : C →ₗ[R] B` 生成
`eₙ(x)(i) = o(Aⁱ x)`，其中 `i≤n`。prefix restriction 删除末项，
`Compatible` 来自同一个 evaluator；没有外领未来表。

```text
C ──sourceMap──→ completion(A,o)
│ A                    │ generated endomorphism
▼                      ▼
C ──sourceMap──→ completion(A,o)
```

既有 `Scalar.Cofinal.Tail` 和 `Morphism` 实现这个作用：前者移动观察层级，
后者以 `generatorMap=A`、`stageMap=dropFirst` 删除内容首拍。
对每个 completion 元素，作用后的第 i 项就是原第 i+1 项。

## 自主模型与精确残差

`K∞ := ker(sourceMap) = ⋂ᵢ ker(o ∘ Aⁱ)`。
`kernel_is_largest_invisible_invariant` 证明它是 `ker(o)` 中最大的 A 不变子模。
当前读数相同未必同属 K∞；保留全部未来读数才能使观察对演化闭合。

`Model := C / K∞` 直接使用既有 differential residual coimage。
源方块生成 `modelAction`，第0项生成 `modelReadout`；canonical quotient 的满射
直接供给原 `SurjectiveRestrictionActionAt`。旧 quotient-action consumer 消费生成结果，
不再要求此模型的 caller 提交 targetAction 或 action_square。

这里只对实际 coimage 使用满射；completionMap 没有被宣布满射。
模型点相等精确等价于全部未来观察相等。


## 原 Hilbert 几何与完整恢复

当实际 A/o 为 CLM 时，所有 o∘Aⁿ 的连续性直接证明同一个 K∞ 闭。
原空间完备性给 K∞ 正交投影；现成 quotientEquivOrthogonal 实现同一个 Model 的原商范数。
不接受新 metric、isometry、闭核证明或目标恢复值作为 source 输入。

令 π 为既有 projection，R 为从商恢复的 K∞ᗮ 代表，D 为 K∞ 上的原正交残差：

```text
D x + R(πx) = x
‖x‖² = ‖D x‖² + ‖πx‖²，  ‖Rm‖ = ‖m‖
o(Aⁿ R(πx)) = o(Aⁿ x)，  o(Aⁿ D x) = 0
R(πx) = x ↔ D x = 0
‖modelAction m‖ ≤ ‖A‖ ‖m‖，  ‖modelReadout m‖ ≤ ‖o‖ ‖m‖
```

一般 A 的恢复作用是 R∘π∘A∘R。若原 A 自带对称性，既有核的不变性与正交补律进一步生成
R(modelAction m)=A(Rm)、D(Ax)=A(Dx)。恒等读者恢复原值；零读者的 D 保留原值。
[原 Riesz 消费者](../../arithmetic/riemann/original-riesz-dynamic-observation.md)直接消费原作用、
源能量、全部未来读数和完整 L² 分解。这份固定空间实现不擦除其他原 K/T 的变化测度索引。

原K/T跨变化测度时，直接进入[依赖观察与完整恢复](../probability/source-temporal-observation-recovery.md)；
既有cofinal/coimage保留索引并生成后继，原时间与观察残差共同重建原源。

## 原生发生与直接控制

原 `SourceOperationNative.sourceAction` 与任意 raw observer 直接特化该算法。
`sourceAction_pow_point` 把每个幂读回原 `runtime.advance`；`modelAction_point`
把模型后继读回原 `tick.next`，同 proof 保留 occurrence、whole-ledger 与 next。
没有从一般模型或 completion 点选择 native State。

原 Fock process 的 runtimeAt 0、1 在 `state / 2` 下当前同值而下一拍异值，
机器拒绝仅凭当前读数的后继函数；完整模型则区分这两个原点。
这扩展观察与作用 consumer，原 controller/base row 保持。

## 权威源码

- `GenericFoundation/Operations/Observed/{History,Kernel,Coimage,Native}.lean 与 Hilbert/{Core,Action,Symmetric}.lean`
- `GenericFoundation/Operations/Observed/Regression/Source.lean`
- [完整 native 入口](source-native-operation-entry.md)
- [既有逐 runtime field 后继](source-operation-witnessed-dynamics.md)

实时责任只见 [maximum active route](../../../handoffs/no-island-no-magic-mathematics-active-route.md)。

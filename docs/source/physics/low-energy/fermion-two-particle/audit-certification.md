# 原252模费米双粒子链独立认证

**Verdict: certified。** 七个冻结 Lean 模块的跨模 CAR、真实正规序、双占据 direct/exchange、原实源顶点及非零源消费者均成立，没有候选修复项。

## 对象与信任检查

候选为 `scratch/LowEnergyFermion/{CAR,NormalOrder,TwoParticle,MatrixElement,Hermitian,Source,Consumer}.lean`，以及上一层 README／Audit／聚焦回执。七模块 fresh `--trust=0 -DwarningAsError=true` 均 EXIT0；原候选 Audit 的80个公开声明全部重查，仅使用 `propext`、`Classical.choice`、`Quot.sound`。本审计另有4个独立 Lean 消费者，严格检查与公理检查也全部通过，共84项。

无 `sorry`、新 axiom、`native_decide` 或不可能域。mouth attention 仅提示仓库已有的 `autoImplicit false`。原 source、修复 Dirac-dual action、actual、controller root/current/next 保持。本链消费已存在的 `QuantizationCheck.Fermion`，是从属有限 CAR 制备消费者，没有把它指定为原理论唯一的统计／外态实现。

## 跨模符号与正规序

原 `create/annihilate` 未替换，符号仍由 acting mode 之前的占据数生成。`CAR` 对任意线性序与全部 Fock 态证明三组反交换关系；同模使用原接口，异模逐占据状态处理，没有靠两粒子特例供应跨模 CAR。

`NormalOrder.quantize_apply` 实际回到旧 `secondQuantize`。四算子项定义为

```text
N(A,B)=Σijkl Aij Bkl ci† ck† al aj,
dΓ(A)dΓ(B)=dΓ(AB)+N(A,B).
```

其中乘法是线性映射复合，右侧 aj 最先作用；第二次交换两个 annihilator 的负号抵消前一次正规序负号。A、B 的顺序及收缩 AB 都保留。N 是真实四算子有限和，未被定义为需要证明的差值。

`TwoParticle` 从 `c†(u)c†(v)|0〉` 出发，证明 `aj ai` 的系数为 `ui vj−vi uj`。`MatrixElement` 消费原 Fock 配对，左槽明确带共轭，实际导出 determinant 配对和四项矩阵元

`Aij Bkl−Bil Akj−Ail Bkj+Bij Akl`。

本组的全称性来自 Lean 定理，不来自小维枚举。独立位算法另检查4模全部16个占据态、全部256种 matrix-unit 正规序词。在两个不同模上取 A=B 为交换矩阵时，真实正规四算子期望是−2；该非零纯交换反控制同时作为独立 Lean 消费者通过。一粒子上的原乘积为1而正规四算子项为0，拒绝丢掉 dΓ(AB) 收缩项。

## 完整252源与 Hermitian 实顶点

`Source` 的 index 是完整 `Quantum.Index`，其顺序由该完整类型到 Fin 的等价生成；没有调用八维压缩或删去外幂级。原 `Quantum.operatorMatrix`、`matrix_composition` 和完整 coordinate pairing 被直接消费。

复 canonical 读数使用 bra 中的原 S；实密度使用

```text
K(s,V)=s·HermitianPart(SV)=s/2·(SV+(SV)†).
```

`realVertex_response` 对每个完整 matter 给出原 `s Re[J(ψ)(Vψ)]`。`currentVertex/scalarVertex` 再乘真实 `|det e|`，`original_real_current` 与 `original_real_scalar_source` 分别等于原 `Exchange.current/yukawaSource`。这些恒等式明确属于 `χ=s J(ψ)` 的制备子类，未将独立 dual 的整个字段域改成共轭变量。

Hermitian 部分在这里代表原实双线性源，并未把原 Dirac／Yukawa 动力算子替换为 Hermitian completion。独立 Lean 消费者取原上手征 SpinPair 分量和 V=I：正确含 S 的实读数为0，裸坐标内积为2，直接拒绝漏掉 S。

独立程序从当前源 γ、Pauli、外幂基重建全252顶点。三个真实颜色空间 current 和全部35个 scalar 基顶点的 Hermitian 性、原 right-chiral placement 均核验。另有具体跨 Λ2／Λ6 的一粒子基向量组合，使正确 scalar 实源非零，而省去 S 后读数为0；见 [independent-receipt.json](independent-receipt.json)。

## 原非空双占据与幅度

消费者取 `u=spinPairMatter(1,0)`、`v=spinPairMatter(0,1)`。原完整252配对给出 `〈u,u〉=〈v,v〉=2,〈u,v〉=0`，所以

```text
Ψ₂=c†(u)c†(v)|0〉,
〈Ψ₂,Ψ₂〉=4,
〈Ψ₂,N(Kfirst,Ksecond)Ψ₂〉=216/125.
```

这里4是**范数平方**；乘以1/2后的态范数平方为1，读数为 `54/125`。没有重复使用密度或把 one-particle 幅度当成已归一。Lean 直接消费源 `spinPairDual_generatorKinetic`、actual coframe、`N²=54/125` 和 `spinScale²=2`。

独立程序在252个真实基坐标上保留稀疏双占据振幅，按原四算子逐步作用，未用 Wick 四项公式或 `dΓ(A)dΓ(B)−dΓ(AB)` 定义结果。全部九组颜色轴读数均重新得到216/125与54/125，并另核验它们等于带收缩的原乘积差。双占据态有四个非零占据配置，非空性得到实际消费。

`sourcePair_prepared/prepared_normal_response` 保留任意两个原实幅度：态系数为4ab，配对读数系数为16a²b²。重复相同制备的 pairing 为0已作为独立 Lean 消费者通过；原创造算子的位算法也实际得到零态。两份不同相位的单位制备及非单位幅度另作精确核验。

签收的是原有限 CAR 载体上的正规序源顶点矩阵元。它没有被扩写成已收缩所有交换核的散射幅、衰变率，或原量子理论唯一统计实现。

## 证据

- [focused.json](focused.json)及七份 `*-strict.log`：全部冻结模块 fresh strict EXIT0。
- [candidate-axioms.log](candidate-axioms.log)：80个候选公开口全部为标准公理。
- [独立 Lean 消费者](Consumer.lean)、[严格输出](consumer-strict.log)：交换负号、重复制备、原 S 与裸内积的4项消费全部通过。
- [独立位与源检查](independent_check.py)、[输出](independent-check.log)、[回执](independent-receipt.json)：全部原有限算子、full252顶点、非空数值与关键反控制全 PASS。
- [mouth attention](attention.log)：只有既有 autoImplicit 提示。
- 审计仅新增本目录内容，没有修改候选或提交。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/fermion-two-particle/audit/independent_check.py --root .
cd Lean
lake env lean --trust=0 -DwarningAsError=true ../Verification/physics/low-energy-phenomenology/fermion-two-particle/audit/Consumer.lean
```

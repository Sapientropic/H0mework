# 原源全三动量旋转运输认证

Verdict: **certified**。冻结三份 Lean 候选及 generators / finite / quotient_transport / catalog 程序链、JSON、README、日志的明确范围成立。候选未改、未提交。

## 同源与完整字段

本组消费[已认证原289作用符号](../../audit/certification.md)、原112约化方程、[恰好九个源方向的 faithful103 商](../../quotient-audit/certification.md)及[完整轴向除子](../../propagation-audit/certification.md)。原 source、修复 Dirac-dual action、actual、visit 10 / tick 16 / materialEntry 与 tick17后继保持。本组是从属有限旋转及谱运输，没有新增 runtime authority。

[独立检查](independent_check.py)没有 import 候选模块。它直接读当前 Lean 的 Gamma、Pauli、四项真空字面量，重建 native P286 基、真实 Λ⁴ Lie 作用与九维 scalar J 坐标；再独立生成全部 **289×289** 字段生成元。原 coframe、gauge A、Lorentz connection、gravity B、multiplier、gauge B 的各个坐标/内部指标都参与；primal 与 independent dual 分别使用 `M` 与 `−Mᵀ` 的真实实化，未替换成共轭场。

原九场背景逐项固定，实际手征时间相位与 matter 旋转对易。原 Λ² 表示与源 Hodge 的空间对易身份、三个完整生成元的 Lie bracket 及每个 tensor 指标的正负号均核对通过。

## 有限旋转的双重证据

原程序 fresh 重放，逐整数系数证明三个轴的

```text
S(z)ᵀ H289(R(z)ᵀp) S(z) = H289(p)
S(z) S(−z) = I289
S112(z)ᵀ H112(R(z)ᵀp) S112(z) = H112(p)
T(R(z)ᵀp) U(z) = S112(z) T(p).
```

全部四个形式动量保留，清分母后的 z 次数上界为24；不是轴向或数值抽样。原系数域为 `Q(√2,√15)`，primitive element 最小多项式为 `X⁴−34X²+169`。实际 field 分母常数三轴均为1，参数分母为 `(1+z²)^4`；spatial / U 分母为 `(1+z²)^2`，在全部实 z 上严格非零。

独立算法改走精确微分代数验证：它重算 H289、H112 的全部系数 Lie 恒等式以及九列 T 的 Lie 恒等式，再逐多项式系数验证

```text
(1+z²) S′ = 4 G S,   S(0)=I
(1+z²) R′ = 4 M R,   R(0)=I
(1+z²) U′ = 4 V U,   U(0)=I.
```

R 是同一空间生成元 M 的有理矩阵；U 是三个 `R3ᵀ` 块，V 是三个 `M3ᵀ` 块。微分上述有限 congruence 与 `S⁻¹T(Rᵀp)U` 后，独立已验收 Lie 恒等式使其导数为零；它们作为特征零域的有理函数等于 z=0 初值。因此独立验证覆盖全部实有限参数，未将无穷小等变直接当作有限等变。另逐系数直接检查完整 field 逆多项式、R 的正交性及 determinant 1。

实际运输的 T 列严格为 **0–8**：三个原色 SU2、三个 Lorentz boost、三个 Lorentz spatial 方向；U 为9×9。历史标签中附带的四个 diffeo 候选未进入运算或商。这里使用固定参数的全局空间/spin/color 联合作用，没有引入一般局部 diffeomorphism 不变性。

## Lean 的任意动量生成与原 Hodge

三个候选 `Hodge.lean`、`Circle.lean`、`Alignment.lean` 全部 fresh `--trust=0 -DwarningAsError=true` **EXIT 0**。

- `orthogonal_hodge_pullback` 直接消费原 `coframeGaugeSpacetimeHodgeLinear`、原 exterior-square coframe 与 `Matrix.inv`；由真正正交条件生成逆等于转置，没有把目标 Hodge 等式作 premise。
- `circle_surjective` 为每个 `c²+s²=1` 生成有限实 parameter。`c=−1` 用 parameter 1 单独支付；其余分支由正平方根生成，所用分母非零。
- `momentum_alignment` 对每个 `k≠0` 生成 y、z，满足 `R=Ry(y)Rz(z)`、`RᵀR=I`、`det R=1`、`Rk=|k|e3`。横向半径为零的轴点与负 z 轴均在证明内处理。`k=0` 有独立恒等旋转消费者。

[Audit.lean](Audit.lean) 直接消费同一见证，将原 Hodge 拉回、正 k 与负 k 的对齐放在同一个 R 中；另给出负轴非空实例、零模实例与半周有限参数实例。量词是逐 k 生成同一对 ±p 所用的 frame，不要求重新为 −p 选择另一 frame。

最终 Audit 严格 **EXIT 0**。26个候选公开声明及4个直接消费者，共 **30 项**传递公理均为 `{propext, Classical.choice, Quot.sound}`。首轮 Audit 的负轴常量索引未被自动化简，属于审计消费者局部 elaboration；显式归约 Fin 索引后通过，失败与修复记录保留在日志，候选没有修改。

## 乘法顺序与 faithful consumer

由源有限身份逐次代入，Lean 所生成的几何顺序
`R=Ry(y)Rz(z)` 对应字段顺序

```text
L = Sz(z) Sy(y),    L⁻¹ = Sy(−y) Sz(−z).
Lᵀ H(pk) L = H(pa),
pa=(λ,0,0,i|k|),   pk=(λ,ik1,ik2,ik3).
```

独立检查使用非交换有理参数 `y=1/2,z=1/3`，生成三个空间分量均非零的真实 momentum，消费原112矩阵及冻结103接口，逐项核验

```text
Ck = L112 C
Qk(pk) = Qa(λ,|k|) L112⁻¹
Qk(−pk) = Qa(−λ,−|k|) L112⁻¹
Qk Ck = I103
H112(pk) = Qk(−pk)ᵀ Ka(λ,|k|) Qk(pk)
H112(pk) Ck = Qk(−pk)ᵀ Ka(λ,|k|).
```

负 momentum 的完整对称式也实际核验。这个消费者确认抽象组合推导的顺序与真实 source index 接口相接；普遍性来自前述全部参数/全部动量的有限恒等式，任意实方向的到达性由 Lean 生成。

对每个固定实 k，L 与逆都独立于 λ、处处可逆，所以不增删时间极点及局部重数。沿固定空间射线也可固定同一 frame，包括该射线的零点。`k=0` 直接取 identity，保持既有 q=0 因子与原点部分重数。相容源逆 `Ck Ka⁻¹ Ckᵀ` 按同一原112相容源条件解释。

反控制实际拒绝 `Sy Sz` 的错误字段顺序，以及用字段转置代替真实逆；同时检测到 z=1 与 z=−1 的 spatial 矩阵相同、完整字段 lift 不同。因此保留 spin/color lift 的选择，没有宣称它是只由 SO(3) 矩阵决定的单值表示。

## 全实三动量除子

独立检查消费全部22个冻结轴向因子，核对 q-reflection 配对、每个精确系数与重数，并逐项验证

```text
P(x,w)|x=u²,w=q² = 相应一枚因子或一对 q↔−q 因子的乘积
x = λ²/(2N²) = 125λ²/108
w = (k1²+k2²+k3²)/2.
```

22枚因子完整覆盖为 **14 个乘积块**，总时间次数 **126**。每个块的 w=0 特化保持，原点重数原样保留。有限源 congruence、真实九方向运输和任意 k 对齐共同支付其全实三动量身份，不是仅把轴向公式中的 k²换名为范数。

## 回执与准确范围

- [replay.log](replay.log)：四个冻结程序依次消费本轮 fresh 输出，全部 **EXIT 0**；JSON 除 finite 各轴计时外完全一致。
- [lean-audit.log](lean-audit.log)：三候选 fresh 严格检查及最终30项公理/消费者回执。
- [independent-check.log](independent-check.log)、[独立回执](independent-receipt.json)：独立源 tensor、有限微分代数、实际字段/商消费者、反控制与完整因子读回，**EXIT 0**。
- [attention.log](attention.log)：mouth attention 仅提示现有 `autoImplicit false`，无语义缺陷；候选无 `sorry`、`native_decide` 或自定义公理。

Lean 签收原 Hodge、圆参数全覆盖和任意实动量生成；全289/112矩阵身份与径向除子为独立复验的精确程序证据。14项是原因子的乘积块，未宣称其全部不可约，也不把 determinant 零点计为物理 states 或所有指定外源响应的未约分极点。

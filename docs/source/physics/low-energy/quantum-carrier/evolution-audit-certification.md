# 原非线性九场配置的完整载体响应认证

**Verdict: certified。** 2026-09-19，独立核验
`scratch/LowEnergyQuantum/{Preparation,Readout,Density}.lean`。
分类为同一已生成非线性配置的 **quantum response / density readout**。
沿用已签收的 Carrier、Compression 和泛初值 Evolution，不重开这些关口；候选未修改。

原 source、Dirac-dual form-native action、visit 10 / tick 16 / materialEntry 与
visit 11 / tick 17 后继保持；本组没有新增 action 项、外供波函数或 runtime authority。

## 原配对、实际 dual 与完整操作次序

`coordinatePair_full` 将完整 252 坐标 Hermitian 配对精确识别为原四个 Dirac 分量上的
`fullInternalPair`，其内部仍是原 Λ⁶、Λ²、Λ⁴ 配对。
`spinExchange` 直接来自原 `diracAdjointSpinSwap`，在完整 carrier 上自伴且为 involution。
`canonicalDual_full_response` 保留原 Dirac adjoint 中这一显式 spin swap。

`preparedSpinor amplitude angle` 使用原 `spinPairMatter` 与两套相反相位。
其范数平方为 `4 amplitude²`，幅度 `1/2` 的配对精确为 1。
`prepared_normalization` 给出原物质向量与这个归一化向量的确切倍数；
`prepared_dual` 再证明当前准备的 independent dual 就是 real density 乘原 canonical adjoint。
该身份在 Readout 中由实际 configuration 的 matter、conjugateMatter 两字段共同消费。

写 `a = flow.pointState point 0`、`θ = flow.pointState point 6`，任意原 End A 满足

`χ(Aψ) = (4 spinScale / a³) · normalizedRead θ A`。

其中 `normalizedRead θ A = ⟨ψ̂θ, S A ψ̂θ⟩`，S 是原 spin exchange；
两字段各自的 `(a√a)⁻¹` 因子精确生成 `a⁻³`，没有丢弃一个 matter/dual 因子。
`moving_composite_response` 保留 `M(S) (M(A) M(B))`：先在完整 carrier 中作用 B、A，
再完成同一个原 dual 配对。中间没有使用八维压缩。
`source_joint_and_response` 将这条读出与原完整九场零残差接到同一个 generated configuration。

## 实际密度与非线性反馈

`densityProfile` 定义为原字段的 `Re[χ(Sψ)]`，不是另外构造的密度替身。
因为 `normalizedRead θ S = 1`，其读回为

`ρ(t) = 4 spinScale / a(t)³`，且 `a(t)³ ρ(t) = 4 spinScale`。

这里的 volume 是三维空间尺度因子 a³。一般 `normalizedRead` 是任意 End 的复响应；
本组没有将它或 ρ 声称为归一化概率。Audit 进一步核验原 seed 上 `ρ(0)=4 spinScale>1`，
而同一 spin-exchange 的归一化读数为 1，显式保留两者的区别。

`densityProfile_derivative` 使用条带内原响应的 eventual equality 消费真实导数。
原径向 seed family 上

`ρ′(0)=0`，`ρ″(0)=2 spinScale · Contact.Stress.weight · (Contact.Slice.impulse parameter)²`。

其中 weight 是原 scalar 方向的平方范数，impulse 为原 `parameter * growthRate`。
二阶公式消费同一轨道的 clock、坐标导数和 `generator_seed`；
从 densityValue 转回实际 χ(Sψ) 时使用局部函数及导数的 germ equality。
parameter 非零时二阶导数严格正，故该实际密度不在任何原点邻域恒定。
Audit 同时核验 parameter=0 时二阶导数为零，保留非零假设的准确强度。

## 直接消费者与严格结果

[Audit.lean](Audit.lean) 的七个公开消费者实际核验：原生成 dual 身份、同源九场与完整复合读出、
归一化及实际密度区别、正密度和空间体积因子、真实二阶反馈、零冲量控制，
以及 parameter=1 的正时间条带九场解与非恒定原响应的共同实例。
消费者由 `initialSolution`／`solution` 的已证存在性给出源对象，没有外供目标残差。

Preparation、Readout、Density 与 Audit fresh 执行
`lake env lean --trust=0 -DwarningAsError=true`，全部 **EXIT 0**；
三候选 `.olean` 同次生成，无宽构建。
42 个候选公开声明加七个消费者，共 **49 项**传递公理检查，
全部属于 `{propext, Classical.choice, Quot.sound}`。
无 `sorry`、`admit`、`native_decide`、自定义 axiom 或新增信任绕过。

mouth lint 提示为仓库惯用的 `autoImplicit false` 及局部非恒定声明的 negative-mouth 标签；
后者由严格正二阶导数证明，scope 为这条实际密度，不承担全局 no-go 或 controller 处置。
真实命令与输出见 [lean-audit.log](lean-audit.log)。未发现源替换、操作顺序反转或目标 premise。

按上述原非线性响应与密度读出口径可晋升。本认证不把该消费者等同于完整量子理论完成。
未 stage 或 commit。

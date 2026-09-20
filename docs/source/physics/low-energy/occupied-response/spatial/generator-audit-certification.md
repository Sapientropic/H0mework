# 独立认证：完整生成元域、原偏导弱方程与 mild 唯一性

Verdict: **certified**。六个冻结候选未发现声明或来源缺陷。

范围为 `GeneratorCore / GeneratorDomain / GeneratorSchwartz / Weak / Uniqueness / RawWeak`，依赖已正式认证的 `LowEnergy.MatterSpace` 九模块。本轮只新增本目录审计证据；未修改候选、根文档或提交。

## 机器验收

- 六个候选 fresh 默认预算 `lake env lean --trust=0 -DwarningAsError=true` 全部 EXIT 0。
- generator 子包 33 个、weak 子包 12 个公开口及独立消费者 5 个口通过严格公理检查：总计 50，集合均包含于 `propext / Classical.choice / Quot.sound`。
- 独立原系数 Gaussian 消费者及五项号数负控制全部通过。
- `focused.json`、`trust-summary.json`、各 strict 日志保存实际命令与结果。

## 完整双向域身份

签收的 `source_domain_iff` 是整个位置空间 L² 载体上的精确身份：

`f ∈ Domain(Hgenerated) ↔ [ξ ↦ h(2πξ) fhat(ξ)] ∈ L²`。

这识别的是乘子作用后仍在 L² 的算子域，输入没有偷换为某个能量期望值有限的较弱条件。

正向生产强导数时，`fiber_difference_bound` 由真实纤维时间导数、幺正性及均值估计生成；差商范数以 `‖h(k)f(k)‖` 控制，误差平方以 `4‖h(k)f(k)‖²` 控制。该控制函数的可积性来自显式乘子能量的 L² 身份，没有全动量有界前提。

反向由原 L² 轨道的真实强导数产生差商 L² 收敛。审计进一步读取了 Mathlib 的 `tendstoInMeasure_of_tendsto_Lp` 和 `exists_seq_tendsto_ae'`：本次使用的方向不要求有限总体积。生成的时间子列趋于零点的穿孔邻域；其可数多个代表元等式通过 `ae_all_iff` 同时成立。随后同一纤维差商的极限唯一性恢复 `g(k)=−i h(k)f(k)`，再从 `g∈L²` 生成乘子可积性。没有将所求 a.e. 恒等、域成员或目标极限作为 premise。

通过实际 Plancherel 运输后，`source_hamiltonian_fourier_ae` 给出同一 Hamiltonian 的乘法表达。独立消费者 `arbitrary_domain_fourier_readback` 从任意**已有真实域向量**提取乘子可积性，再通过证明无关性认回原域点和原 `spatialHamiltonian`；调用者不需额外提供 finiteEnergy。`finite_energy_iff_derivative_exists` 同时消费两向，核对能量条件与真实强导数存在的等价。

## Schwartz 与原 Dirac 的实际接缝

`sourceDifferential` 是 Schwartz 空间中的真实算子

`D_H f = h0 f − i Σ Hj ∂j f`。

Mathlib 的 `fourier_lineDerivOp_eq` 支付 `∂j ↔ 2πiξj`，其与 `−i` 相乘恰为 `2πξj`。该身份生成全部 Schwartz 测试的乘子可积性、真实域成员和 `Hgenerated f = D_H f`，没有将这些结论当作外部测试资格。

`diracTimeRead_constant / diracTimeRead_spatial` 及 `sourceDifferential_from_original_connection` 实际消费正式的原连接读回：

`D_H f = N γ0 [occupiedDiracConstant f + i Σ γj ∂j f]`。

这里 `occupiedDiracConstant` 包含已正式支付的共转项 `+(ω/N)γ0Q`；由 `γ0²=−I`，乘以 `Nγ0` 后变成 `−ωQ`，正是 `h0`。原物理场的 `Horiginal=h+ωQ` 和 `exp(−iωtQ)` 仍由正式 Phase 接口读回。源 lapse、源频率与原时间没有更改。

独立 `actual_schwartz_connection_readback` 消费生成元等式与原连接等式，得到真实 Hamiltonian 测试向量的 a.e. 原 Dirac 表达。

## 弱方程和同一 mild 发展的唯一性

`Weak` 先把同一空间群从配对右侧移到左侧，再分别对真实域测试轨道与 Bochner 积分求导。复内积左参数共轭线性与 `H=iA` 给出准确的

`d〈v,u〉/dt = −〈Av,u〉+〈v,f〉 = −i〈Hv,u〉+〈v,f〉`。

`RawWeak` 实际消费上述 Schwartz 域成员与 Hamiltonian 身份，得到原空间偏导测试式；`duhamel_original_dirac_test` 给出同一测试算子的原连接表达。连续 L² forcing 是本来方程的输入，响应本身没有被预设为强域向量。

`Uniqueness` 从同一群生成任意 L² 初值的发展，支付初值和强 interaction 方程；其唯一性范围正是这个 mild/interaction 方程。任意解减去实际积分后的 interaction 差函数导数为零，初值固定该常量。没有输入唯一性或完整发展本身。

独立消费者先验证显式候选 `u(t)=(1+t)U(t)v` 对任意 L² 向量 v 满足初值 v 和 forcing `U(t)v` 的真实 interaction 方程，再用 `spatialDevelopment_unique` 将它认回实际 producer。另一消费者将同一连续非零源类交给 `duhamel_source_differential_weak`；该程序并非仅反复引用原定理名。

## 独立源函数与反控制

`gaussian_check.py` 从原 Gamma、原颜色 Pauli 矩阵和原连接常数重建 h0 与三个 Hj，并逐项吻合已认证的占据符号。选原单位准备向量 w 与

`f(x)=exp(−|x|²)w`，`‖f‖²=(π/2)^(3/2)>0`。

程序核验这个非零函数的完整三个空间导数、实际 Gaussian Fourier 变换、原 `Nγ0` Dirac 读回和非零 Hamiltonian 输出。另以显式 Hermitian 矩阵和复向量检查共轭线性左配对，实际弱导数为 `5−i`。

五项负控制分别改变 `2π`、空间 `−i`、lapse N、共转 `ωQ`、弱配对的 i 号数，均与真实结果不同。它们核验声明的物理坐标和号数；完整无限维域与弱发展证明仍由上述 Lean 定理承担。

## 证据与固定来源

- `Consumer.lean`、`consumer-strict.log`：任意真实域读回、原 Schwartz 连接读回、强导数存在等价、独立 mild 解和真实偏导弱消费者。
- `gaussian_check.py`、`gaussian-check.log`、`gaussian-receipt.json`：非空源函数与号数反控制。
- 六份文件 strict 日志、两份公开口日志、`focused.json`、`trust-summary.json`。
- 两份 mouth lint 只提示仓库使用的 `autoImplicit false`，无目标偷运发现。

原 `positiveSmoothUnifiedSource`、修复后的 Dirac-dual 母作用、SpinPair、Stage10 root/current/next 保持不变。本次闭合的是该固定来源的完整传播域、原偏导弱方程和同一 mild 方程的唯一发展。

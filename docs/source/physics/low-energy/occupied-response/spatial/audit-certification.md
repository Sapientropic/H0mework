# 独立认证：原占据物质的完整空间传播

Verdict: **certified**。

本证书覆盖冻结的 `Source / Connection / Multiplier / Continuity / Spatial / Duhamel / Phase / Resolvent / ResponseBound` 九模块及 `source_coefficients.py`。未读取或纳入后续 `Weak`、`Uniqueness`、`GeneratorCore`、`Domain`、`Schwartz` 候选。本次仅新增本目录证据，未修改候选或提交。

## 已签收的机器事实

- 九文件 fresh `lake env lean --trust=0 -DwarningAsError=true` 全部 EXIT 0；候选 `Audit.lean` 的 123 个公开口和独立 `Consumer.lean` 的 7 个消费者通过同一检查。公理集合均包含于 `propext / Classical.choice / Quot.sound`。
- 原精确程序 fresh 重放 EXIT 0，结果与冻结 `source-receipt.json` 完全相同。
- 独立程序由原 Clifford 字面矩阵、原 SpinPair 系数表、原 P286 生成元的 Λ² 作用重新生成 48 个力与电流顶点及实际 seed，逐项吻合父回执。完整特征空间核验、两侧响应顺序与四个负控制全部通过。

## 来源与声明责任

`Connection.occupiedConnection_readback` 直接消费 `actual.gravityConnection`、`actual.gaugeConnection` 和源 spin lift；`sourceConstant_from_original_connection` 从真实连接常项得到 `h0`。原 lapse、spin/gauge 常数及 `frequency` 没有被调用者替换。`Source` 的全部空间系数为 `−N γ0 γj`，真实 `h(k)` Hermitian，且与原 `Q` 交换。源矩阵口属于 source producer/readout。

`Multiplier` 从有限维矩阵指数的幺正性支付逐点范数守恒，再生成可测 L² 类、线性等距、显式 `−t` 逆和群律。`Continuity` 的支配函数是固定源向量的 `4‖f(k)‖²`，其可积性来自该向量的 L² 身份；没有暗加 `sup_k ‖h(k)‖ < ∞`。这是任意连续 Hermitian 矩阵族上的真实传播 producer。

`Spatial` 实际消费向量值 `Lp.fourierTransformₗᵢ`，通过 Plancherel 运输同一动量群。Mathlib 的 `Real.fourier_eq` 使用 `exp(−2πi〈x,ξ〉)`，源乘子明确为 **`h(2πξ)`**；独立负控制确认少掉 `2π` 会改变原空间系数。

实际生成元来自旧 `Quantum.Generator.Core.domain`：域是同一轨道在零点真实可微的向量，生成元为该轨道的 `deriv`，物理 Hamiltonian 定义为 `i` 乘生成元。`Averages` 由时间积分生成域向量，并以时间平均趋于任意源向量支付稠密性；`Weak / SelfAdjoint` 从伴随配对生成弱轨道积分与真实强导数，使伴随域回到原域，进而得到闭与自伴。该链没有接收目标自伴算子、目标稠密域或目标微分方程作为 premise。

因此本九模块签收的是**这个具体强连续空间群的真实稠密导数域及其闭自伴 Hamiltonian**。把该域进一步辨认为显式 Fourier 乘法域、或组装原偏导 Euler 方程，是后续独立接口，不由本证书代填。

## Duhamel 与原时间读回

`Duhamel` 的积分是完整 `L²(R³,C¹²)` 中的 Bochner 区间积分。连续源给出真实 interaction 导数、连续扰动、零初值、零过去、retarded 积分身份及未来范数界。声明没有将任意 L² 初值放进无界 Hamiltonian 的强导数域。

独立 `Consumer.lean` 消费真实群律和积分，证明对任意 L² 向量

`Duhamel[s ↦ U(s)v](t) = t U(t)v`，

其范数为 `|t|‖v‖`，相位读回恰为 `t Uoriginal(t)v`。文件还用单位球指示函数构造一个实际非零 L² 向量，并证明该受迫响应在 `t=1` 非零；没有用常量空间背景冒充 L² 向量。域上消费者明确检查 `dU(t)f/dt = −i U(t) Hf` 的符号，并消费实际时间平均进入域的生产口。

`Phase` 先对 Schwartz 函数证明常数内部算子与 Fourier 交换，再通过稠密性与连续性扩展到全部 L²。源 `[h,Q]=0` 支付指数因式分解，得到 `Uoriginal(t)=exp(−iωtQ)U(t)`。读回保范数、可逆并保持零过去；物理时间与源 `ω` 原值保留。

## 全动量响应的范数

`Resolvent` 由 Hermitian 内积虚部生成 `η‖v‖≤‖((E+iη)I−H)v‖`。有限维与 `η>0` 随后生成两侧逆及实际 Hilbert 算子范数 `≤1/η`。独立 Lean 消费者在**原 `sourceHamiltonian k`** 上实例化该两侧逆与范数口。

`ResponseBound` 是明确的两项算子复合定理。原源的实例化为

`H+ = h(k), H− = −h(−k)^T`，

`B+ = Bseed†, B− = Bseed^T, T+ = Tseed, T− = conjugate(Tseed)`。

这些字典、全实动量双方 Hermitian 与实际 `Bseed=−√2 Q Tseed` 已由精确程序及独立重建核验。原准备 seed 的范数平方为 4，未误用单位准备态的幅度。

独立程序从各特征核构造正交投影，支付完整谱分解、投影和为单位阵以及最大值被达到。`Tseed Tseed†` 的谱为

`2[1], 4[4], (108/25)[1], (648/125)[4], 6[1], (756/125)[1]`。

由此得到真实欧氏 Hilbert 算子范数平方 `756/125` 与 `1512/125`，不是逐项最大值或 Frobenius 范数。两有序项共同给出

**`‖Π(E+iη,k)‖ ≤ 1512√2/(125η)`，所有实 `E,k`，`η>0`。**

在实际 `k=0,z=iω` 上，独立重算完整响应给出非零 `Π00=40√30/27`。去掉反向项、用 T 替换原电流 B、漏掉反向动量、漏掉 Fourier 的 `2π` 均触发负控制。

这里通用逆与范数定理、原连接口及 L² 传播由 Lean 内核支付；完整 48 路矩阵、源 Gram 常数和两有序项实例化由精确矩阵程序支付。没有把该传播包签成空间 CAR 真空或量子圈完成。

## 证据

- `focused.json`、九个 `*-strict.log`、`candidate-axioms.log`。
- `Consumer.lean`、`consumer-strict.log`、`trust-summary.json`。
- `source-replay.log`、`independent_check.py`、`independent-check.log`、`independent-receipt.json`。
- `mouth-lint.log`：只提示仓库一致使用的 `autoImplicit false`；无目标偷运发现。

本包保持 `positiveSmoothUnifiedSource`、修复后的 Dirac-dual 母作用、原 SpinPair、Stage10 occurrence/controller 及其 next 不变；它是同一固定 root 下的从属传播 producer 与 readout。

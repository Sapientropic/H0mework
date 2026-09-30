# 原完整物质时间生成元与独立 dual

这是固定 `positiveSmoothUnifiedSource`、repaired Dirac-dual action、
`SpinPair.actual` 下的 subordinate producer。原 root、Stage10 tick 16/17、
作用、旧物理时钟及源准备保持；四模块已独立认证并晋升；[认证证书](audit/certification.md)保存60项标准公理回执。

## 可消费结构

`Source.lean` 直接从原 coframe、spin/gauge connection、标量与空间 Fourier jet
生成完整 252 维符号

\[
D=C_0\partial_t+L(k),\quad A=-C_0^{-1}L(k),\quad H=iA.
\]

`drift_original` 接回原 holonomic raw-time-velocity；`actual_spatial_jet` 和
`actual_drift` 支付原 prepared 的真实实例。空间动量是原物理坐标的 `k`，没有换钟。
变化 coframe 时同一 constructor 重算 temporal principal 的逆。

`Evolution.lean` 生成所有实时间的 `U(t)=exp(tA)`、群律、双侧逆及真实导数。
独立 dual 同时生成

\[
\chi_t=\chi_0 C_0U(-t)C_0^{-1},\qquad
\dot\chi_t=\chi_tL(k)C_0^{-1},\qquad
\chi_tC_0\psi_t=\chi_0C_0\psi_0.
\]

任意完整插入，包括任意已经组合好的算子词，都由
`original_Stage10_insertion` 读回原 `quantumClosure.sourceResponse`，保留实际幅度
`4 spinScale`，不在中间压缩到八维。

`CAR.lean` 使用旧有限 Fock 的完整算符，生成逆矩阵配对的 annihilator/creator，
支付全部模式的反对易关系与原 Hamiltonian 交换子。标准单位 CAR 动量的行归一为
`−i Vol χ C0`，所以 raw dual 的 CAR 权重保留 `(i/Vol) C0⁻¹`。
`normalizedMomentum_original_kinetic` 将原 canonical-dual 初图精确读回
`s γ5`；没有替换成 `s γ5 Q`。`FockEvolution.lean` 进一步由同一 `dΓ(H)`
生成全部有限占据扇区的全实时间演化与真实 Schrödinger 导数，不另选真空。

这些是原系数冻结于一个接触点的完整物质 Fourier 模演化。它们支付完整 primal、
independent dual 和代数 CAR 时间口；正 Hilbert 的 * 动力识别以及耦合 boson 场发展
是不同责任，不由此有限模群替代。

## 精确源计算

`compute.py` 重读原 scalar/Clifford/source coefficients，并消费已有 full-phase、
matter-modes、158 vertices 回执。`receipt.json` 给出完整矩阵及以下等式：

- `C0⁻¹=i N γ0`，`H=Nγ0(B+Y)`，原 primal/dual 两侧方程严格相消。
- 全 70 个实标量顶点的时间矩阵两两乘积为零；非零实际顶点范数见证为 `108/125`。
- 实际源 `H` 与原 `Q` 对易，原 prepared 上的导数等于旧源 phase 导数。
- 全 252 的 `sγ5Q` 有 238 正、14 负方向。原 canonical 初图的动力缺陷矩阵非零，
  在实际 prepared 上为零；这保存旧源 actual 轨道而没有推广为所有态的图不变性。
- 原 `P216` 对 40/48 gauge、68/70 scalar 原顶点发生泄漏；24 Lorentz 和16 coframe
  的该矩阵测试为零。coframe 顶点仍含原 `p0`，没有被当作独立瞬时 Hamiltonian。
- 固定原标量的完整 `H(k)` 在 `k=(0,0,3√2/2)` 满足
  `H e207=N(e63+e65)≠0`、`H²e207=0`。这里 `N=3√30/25`。

最后一项拒绝该动量上的忠实固定正内积自伴表示。Lean 的
`symmetric_no_jordan` 支付一般正内积论证；实际大矩阵见证由精确程序支付。
`faithful_positive_representation_obstruction` 还直接从原非零平方零 Yukawa
时间顶点拒绝其固定正 Hilbert 自伴表示。没有据此裁决完整源理论。

`U(-t)†G0U(-t)` 的正配对运输可以由已有双侧逆直接得到，但它是可逆流的配对读出，
不会自动等于原 `sγ5` 动能、原独立 dual 图或原 boson variation。本包不以这个运输
替代剩余的正量子动力责任。

## 重放与认证口

在仓库根运行 `python3 Verification/physics/low-energy-phenomenology/full-quantum/check.py`。
它严格检查四个正式模块、五个 actual consumers、全部公开定理的公理依赖。
精确程序使用已有缓存环境：
`uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/compute.py`。
机器回执见 `focused.json`、`logs/` 和 `receipt.json`。

源码仅为 `Lean/SaturationMonoid/PhysicsCore/LowEnergy/FullQuantum/{Source,Evolution,CAR,FockEvolution}.lean`。
当前证明使用默认 elaboration budget、`--trust=0`、`warningAsError=true`。

`promotion.json` 记录四模块、公开口、原与独立消费者的正式迁移复验。

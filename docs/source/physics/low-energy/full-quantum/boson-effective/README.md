# 原玻色有效核、低动量系统与动态度规响应

本包消费原 289 方程、已认证辅助场／Ward／103 截面和 FullCurrent 的原物质 Schur 项，生成新的 **55 维玻色核**、保留轻物质方向的 **61 维二阶有效系统**，以及原动态 `g00` 的完整响应。原 source、作用、物理时间、独立 dual、准备态与 controller 不变。

## 实际消元次序与 55 维核

原链为

`289 → gauge_B72 → gravity_B+multiplier72 → Lorentz24 → 121 → Ward scalar9 → 112 → 源对称9 → 103`。

103 截面删除的九个坐标全属玻色字段，因此保留完整 48 实物质坐标。将其实际分块为

\[
K_{103}=\begin{pmatrix}K_{bb}&K_{bm}\\K_{mb}&K_{mm}\end{pmatrix},
\qquad
S_{55}=K_{bb}-K_{bm}K_{mm}^{-1}K_{mb}.
\]

`compute.py` 从原非零支撑分块计算 `K_mm` 的真实逆作用与完整 `48×55` 回写，生成所有轴向 `lambda,k` 的有理矩阵 `S55`。它保持原形式转置律 `S55(-p)^T=S55(p)`。

最后的 Lorentz 消元与物质存在交叉腿，真实改变了物质核。因此本包先核对原未约化 `Pi` 恰等于第一次 matter Schur 贡献，再实际支付辅助场先消与物质先消的两个次序。两条路线在共同可逆域产生同一核；原复频点的 168 维辅助逆、48 维改变后的物质逆及两侧 Woodbury 恒等式全部精确通过。**`Pi` 只消费一次，没有作为附加自能再加回原 289。**

`Order.elimination_order` 在异维真实 block 类型上证明两种 Schur 逆完全一致；相应的 primitive 逆条件由本包源矩阵程序支付。`Schur.full_response` 同时回写玻色行和独立物质行。

## 原 289 的全符号传播消费者

`readback.py` 从原辅助场回写构造 `F289×55(p)`，从已认证 `Q(-p)` 与 Ward 切向独立构造源射入 `J289×55(p)`，然后逐项核验

\[
\boxed{H_{289}(p)F(p)=J(p)S_{55}(p).}
\]

`J` 没有通过 `H F` 反向定义。它保留 **32 项原 scalar_J 源系数**，物质和辅助场源均为零；因而没有把一般截面电流误称为原 A-only 强迫。任何真实 `S55` 逆 `R55` 由 `Readback.original_source_response` 产生全 289 行解 `F R55 j`。

`propagator.py` 在与原 FullCurrent 一致的非空复频点

\[
u=\frac35(1-3i),\quad q=\frac3{10}
\]

生成完整 55×55 双侧逆及全部 289×55 场传播列，直接验证原源方程。这里始终使用

\[
\lambda=N\sqrt2\,u,\qquad k=\sqrt2\,q,
\qquad K_{103}^{\rm normalized}=S^T K_{103}^{\rm original}S/N.
\]

源约束与截面保持原轴向范围；原任意方向的 rotation producer 是已有下游运输口，本包不重算它。

## 真正的低动量有效项

约束后 `K_mm(0)` 的实际秩是 **42**。本包由其真实独立列选择非零的 42×42 主 minor，保留另外六个物质坐标。它们经实际重块回写才参数化六维零模图；六个坐标轴本身都不是 K_mm(0) 的零向量。本包没有在原点倒置整个 48 维块。

令源生可逆块为 `A+delta`，`G0=A^-1`，其中 `delta(u,q)` 为实际一次式。真实二阶逆为

\[
G_{[2]}=G_0-G_0\delta G_0+G_0\delta G_0\delta G_0.
\]

`Taylor.inverseJet_exact` 支付精确三阶余项；`Analytic` 从 `||G0 delta||<1` 原生生成逆域及

\[
\|G-G_{[2]}\|\leq\|G_0\delta\|^3\|G\|.
\]

这给出包含 **55 玻色＋6 轻物质** 的完整 61×61 二阶核，保存全部 `1,u,q,u²,uq,q²` 系数。`low_readback.py` 将实际场的二阶回写与独立源射入送回原 289 方程；所有二阶及以下余项消失，首个余项总次数恰为三。常数 61 核的秩为 **56**，保留原五个零方向。

“重块”在这里明确指源原点可逆的物质块；其选择来自实际矩阵，没有输入实验质量表。完整 55 玻色有理核保留非局部物质反馈，61 变量系统提供其可用的局部低动量形式。

## 新的动态 g00 响应

取原源项 `+J00 delta g00`，`dynamic.py` 从实际 source 的 canonical 图生成 25 维动态块，求出真实解并验证全部 **33 个原独立块方程及 289 个原源方程**。这种限制使用已付 canonical79 成本，结果未丢弃独立 dual 行。原 `g00` 读数的分子／分母另由 `cofactor.py` 的实际 determinant/cofactor 算法重建，两种结果完全相同。

下式是 `g00 H^-1 g00` 的逆响应；原有符号约定下，外源诱导场响应为它的负号。完整动态有理函数及原 289 场列保存于 `dynamic-receipt.json`，未把整个源 determinant 当作分子。

沿 `u=r q` 的低动量极限为

\[
\boxed{\lim_{q\to0}G_{00,00}(rq,q)
=\frac{54\sqrt{30}\,(297r^2-125)}{3125\,(162r^2-125)}}
\quad(162r^2\ne125).
\]

完整二阶射线项也已生成。静态原点极限为 `54 sqrt(30)/3125`，时间轴原点极限为 `99 sqrt(30)/3125`，两者不同。`Metric.source_ray_limit` 证明实际系数函数的 punctured `Tendsto`，`two_directional_limits_differ` 内核证明其方向依赖。

低动量分母的首阶除子对应原时间坐标中的 `lambda²=k²/3`。其分子首项为 `625/6≠0`，证明这项首阶响应未被消去；它不是所有非零 k 的精确色散线，完整分母沿此线仍有 q⁴ 阶非零项。原静态有限响应因此不能作为联合低频、低动量的单一局部常数；上述六个保留方向有实际传播责任。

## 证据与范围

- `receipt.json`：完整55核、48物质回写、消元次序、非零 Lorentz 反馈、42／6 分解及全部61二阶系数。
- `readback-receipt.json`：全符号 289 场／源映射及 `H F=J S`。
- `propagator-receipt.json`：实际55双逆和全289传播列。
- `low-readback-receipt.json`：低能61系统回原289、三阶余项与原点秩。
- `dynamic-receipt.json`、`cofactor-receipt.json`、`infrared-receipt.json`：新动态度规传播、分子核验和实际低频项。

源基本字段与完整背景 SHA 均核对。六个 Lean 模块位于 `Lean/SaturationMonoid/PhysicsCore/LowEnergy/BosonEffective/`；前五个支付异维 Schur、真实逆、余项与原方程回写机制，`Metric` 消费原程序生成的具体动态多项式。具体55／61／289矩阵身份属于精确源程序证据，没有宣称整个原作用 Hessian 已内核化。

重放核心检查：

```sh
python Verification/physics/low-energy-phenomenology/full-quantum/boson-effective/check.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/boson-effective/compute.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/boson-effective/readback.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/boson-effective/low_readback.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/boson-effective/propagator.py
```

动态全解与不同算法的分子核验分别重放 `dynamic.py`、`cofactor.py`；`metric_coefficients.py` 比较它们并检查冻结 Lean 系数正文，默认不修改候选。前两项较慢，已有完整实际日志。`focused.json` 记录六模块、32 个公开声明及七个直接消费者全部通过默认限制下的 `trust=0`、warning-as-error；[独立认证](audit/certification.md)另有四个新消费者，共 43 项仅标准三公理；正式迁移后的六模块、原消费者及独立消费者通过。

这是从原量子 current／经典 Schur 同一贡献生成的有效响应，不新增真空圈测度、经验单位或新的 source occurrence。本包已通过独立认证。

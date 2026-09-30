# 原完整五维轻核与传播首项

本包从已认证原61变量系统的常项 rank56/null5 出发，生成可逆56补块、真实五维零模图、
完整二阶轻核和全部289字段的源回写。再从**同一原103矩阵**直接消去98个静态可逆方向，
两条消元路线产生完全相同的轻核。原物质 Π 没有重复加入。

## 源图与完整字段

原61常项的实际主元给出56×56双侧逆，余下的五个原字段索引为
`94,100,106,112,118`。它们的保留坐标经重块补偿构成真实零模图 E0；程序验证
K61(0)E0=0 及 rank E0=5。`Graph` 支付零模图的单射、满覆盖和原分块核恒等式，
不把裸坐标轴当作零向量。

原源已发出的五种扰动依序是：

1. vector_real_rescaling；
2. vector_phase；
3. axial_real_rescaling；
4. actual_homogeneous_axial_phase；
5. imaginary_independent_dual_rescaling。

`modes.py` 用原 Q 和字段缩放读出它们在同一五图中的坐标。坐标变换 M 的 determinant=4；
它不仅恢复 faithful103 坐标，而且在原点**完整恢复这五列原289字段**。
这五坐标保留原 independent dual 及其动力配对；粒子身份由后续外态读出负责。

完整两阶场／源对象保存在 `receipt.json`，满足

\[
H_{289}(u,q)F_{289\times5}(u,q)
=J_{289\times5}(u,q)S_5(u,q)+R_{\ge3}(u,q).
\]

原源射入 J 从上游独立 Ward/Q 射入限制而来，没有用 HF 反向定义。
全矩阵余项及其首个次数均保存，所有二阶及以下系数逐项为零。

## 真实轻核的两个时间尺度

以下使用上述**原五扰动幅度**，即 Ksrc=MᵀS5M。原时间与空间坐标仍为

\[
\lambda=N\sqrt2\,u,\quad k=\sqrt2\,q,\quad N^2=54/125.
\]

一次项只有 Ksrc(2,4)=−8u、Ksrc(4,2)=8u（索引从0开始）。
因此它的秩是2，连接原轴向实缩放与独立对偶虚缩放；其核恰由原矢量实缩放、矢量相位、
轴向相位组成。`source_first_kernel` 内核证明这个精确核条件。

该三维核上的二次作用为

\[
\operatorname{diag}\left(
\frac{16}{9}(5q^2+3u^2),\quad
\frac{32}{737}(55q^2+67u^2),\quad
\frac{20}{81}(125q^2-162u^2)\right).
\]

其中后两项原样恢复既有 SoftPhase 的源相位归一化。
完整5×5二阶矩阵含所有混合腿，保存在 `modes-receipt.json` 与 Lean `Source.pencil`；
`coefficients.py` 从源回执只读比较全部 Lean 系数。

同阶缩放 (u,q)↦(tu,tq) 时，首个非零行列式项总次数为8：

\[
\boxed{\frac{655360}{537273}\,
u^2(5q^2+3u^2)(55q^2+67u^2)(125q^2-162u^2).}
\]

`Scaling` 给出真实矩阵行因子 t,t,t²,t²,t²，`Characteristic.source_ray_leading`
证明除以 t⁸ 后的实际 punctured 极限。保留坐标基下的前因子为40960/537273；
两者相差 (det M)²=16。

u² 因子的后续传播由不同缩放直接判定：令 u=σq²，五核整体首项为二次矩阵。
其静态三维补块有显式双侧逆，实际消元给

\[
\begin{pmatrix}-40/3&-8\sigma\\8\sigma&-10/3\end{pmatrix},
\qquad
\lim_{q\to0}\frac{\det K_{\rm src}(\sigma q^2,q)}{q^{10}}
=\frac{512000000}{439587}(36\sigma^2+25).
\]

因此 σ=±5i/6；此 u² 因子并不代表整条非零动量的 u=0 零线。
`source_quadratic_leading` 支付该真极限，两个复频率根通过内核检查。
二阶轻核已决定这两种首阶传播尺度，无需用未计算的高阶项填补退化。

`direct.py` 另从原103的完整已认证行列式因子提取同阶 degree8 和
时间权重2／空间权重1下的 degree10，除以源生98常项 determinant 后逐项恢复上述结果。
所以这两个首次特征式不是把截断矩阵冒充完整源后产生的根。

恢复原时钟的三个线性首阶特征斜率为

\[
\lambda^2/k^2=-18/25,\quad -594/1675,\quad 1/3;
\]

平方动量频率支则为 λ²/k⁴=−3/20，即 λ=±i√15 k²/10 的首阶。
这些是源坐标中的传播首项；有限非零 k 的精确色散线由完整原核决定。

## 原 g00 源的可见性

原 g00 一次 reader 在三维二次核上为 `(0,0,−36u/25)`，独立反向源腿为
`(0,0,36u/25)`。因此它直接读取原轴向相位，保留原 p／−p 次序。
`source_metric_solution` 从该源腿解出实际三维响应；`source_axial_visible`
证明 u≠0 时该原 reader 非零，另两个方向的首阶读数为零。

原静态补块接触是 18N/125。与轻响应相加，得到

\[
\frac{18N}{125}+
\frac{486N\,u^2}{25(162u^2-125q^2)}
=\frac{18N(297u^2-125q^2)}{125(162u^2-125q^2)}.
\]

此式精确恢复原动态 g00 的低动量射线响应。已有 λ²=k²/3 首阶除子现在定位在
**同一原五核的轴向相位通道**，其原源可见性也直接支付。
静态补块的“可逆”指原点线性算子的代数性质，不输入实验质量或稳定真空。

## 证明与回执

六个候选模块位于 `Lean/SaturationMonoid/PhysicsCore/LowEnergy/LightKernel/`：

- `Graph`：真实静态零模图与覆盖；
- `Jet`：原一次／二次补块的逆、精确余项及已有 Neumann 可逆域；
- `Source`：原五扰动的完整二阶系数及真实块读出；
- `Scaling`、`Characteristic`：8阶与10阶首次行列式及真极限；
- `Metric`：原源双腿、g00接触和物理时钟除子。

具体56／98／103／289矩阵身份与原源模式恢复由精确程序支付；通用消元及具体5核的
代数与频率极限由 Lean 支付。没有声称全部原 Hessian 已完整 Lean 化。
空间范围保持原轴向 q；原源、作用、Stage10 与 controller 不变。

从仓库根复跑以下5个程序及严格检查：

```sh
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/light-kernel/compute.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/light-kernel/propagation.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/light-kernel/direct.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/light-kernel/modes.py
uv run --offline --with sympy python Verification/physics/low-energy-phenomenology/full-quantum/light-kernel/coefficients.py
python Verification/physics/low-energy-phenomenology/full-quantum/light-kernel/check.py
```

[focused.json](focused.json) 保存六模块、62公开声明与7个直接消费者的
默认限制／trust0／warningAsError通过回执，公理为标准三项。

[独立认证](audit/certification.md)签收六模块、74项标准公理声明。独立nullspace／Feshbach、原五扰动字面路径、完整103行列式及新非零点真逆复核通过；正式迁移仅替换导入路径。

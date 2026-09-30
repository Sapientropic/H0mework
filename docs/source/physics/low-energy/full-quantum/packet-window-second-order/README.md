# 保留 sharp 球窗后的真实二阶系数

**状态：strike 解析构造完成，冻结待独立认证。**
同一原准备、原 289 source seed、原实对称 Q 与物理测度保持；未换平滑 regulator。
本包不修改上游 boundary／seed／moments 包，不自行作独立认证或提交。

令 `a_i(k)=W_i(k)J(k/(2π),0)` 为**没有指示窗**的原 seed 场，
`f=1_{B_R}a`，`d=(2π)^−3`。在原物质 Hilbert 空间的 289 重直和上，

\[
B_Q(a,b)=\sum_{ij}Q_{ij}\operatorname{Re}\langle a_i,b_j\rangle
\]

是连续、对称的实双线性配对。
它不要求 Q 正定，且 `|B_Q(a,b)|≤||Q||F ||a||||b||`。
消费已签 outgoing-current 身份，设

\[
\mathcal L(p):=\operatorname{Re}L(p)
=\frac d2\int B_Q(f(k),f(k-p))\,d^3k.
\]

对称性与平移保测也允许用 `f(k+sv)` 写第二腿。
以下全部二阶陈述针对这个真实**实读数**。

## 结论与符号

对单位物理方向 v、s↓0，原窗口首项为

\[
c_v=\frac d4\int_{\partial B_R}|v\cdot n|B_Q(a,a)\,dS.
\]

保留同一移动边界后，真实展开是

\[
\boxed{\mathcal L(sv)=\mathcal L(0)-c_v s+K_v s^2+o(s^2),}
\]
\[
\boxed{K_v=\frac d4\int_{B_R} B_Q(a,\partial_v^2a)\,d^3k.}
\]

因此若研究的是**损失扣除窗口首项**，准确口为

\[
\frac{\mathcal L(0)-\mathcal L(sv)-c_v s}{s^2}\longrightarrow -K_v.
\]

不能把这两个符号混用。上述 K 是响应的 s² 系数，响应的二阶导数系数是 `2K`。

## 球弦推导：移动端点没有被删去

分解 `k=y+tv`，其中 `y∈v⊥`、`|y|<R`，
`h(y)=sqrt(R²−|y|²)`。当 `2h≥s`，该弦的原积分为

\[
I_y(s)=\int_{-h}^{h-s}B_Q(a(y+tv),a(y+(t+s)v))\,dt.
\]

简记该弦上的 `b(t)=a(y+tv)`，
`c(t)=B_Q(b,b)`、`e(t)=B_Q(b,b′)`、`g(t)=B_Q(b,b″)`。
只展开第二条真实外腿并保留上限：

\[
I_y(s)=\int_{-h}^{h-s}\left(c+s e+\frac{s^2}{2}g\right)dt+o(s^2).
\]

补回上端尾段时，c 项产生
`−s c(h)+s² c′(h)/2`，s e 项产生 `−s² e(h)`。
原 B 对称给 `c′=2e`，所以这两个**移动端点二阶项精确相消**。
同时 `∫e=[c(h)−c(−h)]/2`，得到

\[
I_y(s)=I_y(0)-\frac s2[c(h)+c(-h)]
 +\frac{s^2}{2}\int_{-h}^{h}g(t)dt+o(s^2).
\]

这不是把边界设为零，而是保留后明确消掉该展开中的两项。
`compute.py` 以具有任意实对称 Gram 的三次 Hilbert jet 精确核验该式的零、一、二阶。

短弦 `2h<s` 没有重叠。其横向投影面积与原球内体积精确为

\[
\pi s^2/4,\qquad \pi s^3/6.
\]

因此缺失的零阶弦积分和首项端点积分都只贡献 O(s³)，不贡献 s²。
Fubini 给出上面的 K；两端点在球面的投影面积公式给
`∫[c(h)+c(−h)]dy=∫sphere|v·n|B_Q(a,a)dS`，保留原各向异性的球面值。

## 足够的源正则性和可控余项

要求 a 在闭球邻域为强 C²；等价地，本证明只使用球内两阶连续方向导数及其连续边界值。
不要求 windowed f 为 H¹，更没有对指示窗作普通函数微分。

令

\[
M_j=\sup_{\overline B_R}\|\partial_v^ja\|\quad(j=0,1,2),
\qquad
\omega_2(s)=\sup_{|x-y|\le s}\|\partial_v^2a(x)-\partial_v^2a(y)\|.
\]

紧性与 C² 给 `omega2(s)→0`。对未乘 d/2 的 autocorrelation，余项 E(s) 可取

\[
\begin{aligned}
|E(s)|\le\|B_Q\|\bigg[&
\frac{\operatorname{Vol}(B_R)}2M_0\omega_2(s)s^2\\
&+\pi R^2\left(\frac56M_1^2+\frac43M_0M_2\right)s^3
 +\frac{5\pi}{12}M_0^2s^3
 +\frac{\pi}{12}M_0M_2s^5\bigg],
\quad0<s\le2R.
\end{aligned}
\]

第一项来自真实第二腿的二阶积分余项。
长弦三个尾段分别使用
`|c″|≤2||B||(M1²+M0M2)`、`|e′|≤||B||(M1²+M0M2)`、
`|g|≤||B||M0M2`；短弦则使用上面两个真实面积／体积。
乘 d/2 即为物理响应的余项界。

若 a 为 C³，第一项还可改进为 `Vol(B_R) M0 M3 s³/6`，因此得到实际 O(s³)。
原 `packet-seed-regularity` 给 W 在闭球附近解析，`packet-current-moments` 的原全阶位置矩
给 J 对物理转移的强 C∞；固定有限 Q 下 a=WJ 因而满足所需条件。
这些依赖是同一原源的已生成正则性，不是另行提供目标边界系数。

方向也可统一处理：在紧单位球面上使用强二阶导数的统一模量，
本二阶项是 `sum_ab p_a p_b K_ab`，其中
`K_ab=d/4∫B_Q(a,partial_a partial_b a)`。
这是扣除原方向相关的一次齐次窗口项后的二阶 Peano 项；本包不额外宣称已形式化新的二阶 Fréchet 定理。

## 分部积分必须保留球面通量

原常系数 Q 与散度定理给

\[
\boxed{
K_v=\frac d4\left[
\int_{\partial B_R}(v\cdot n)B_Q(a,\partial_va)\,dS
-\int_{B_R}B_Q(\partial_va,\partial_va)\,d^3k\right].}
\]

这一次球面项一般不为零；它与上一节弦端点展开中的抵消是不同表达方式中的不同项。
没有 Dirichlet 条件可将它删除，也没有把原 sharp cutoff 改成平滑 regulator。

## 原 WJ 的全部复交叉项

在同一物质 Hilbert 空间写 `a_i=W_iJ`，内积共轭第一变量。
定义原源标量

\[
\beta=W^\dagger QW\in\mathbb R,\quad
\alpha=W^\dagger QW_v\in\mathbb C,\quad
\gamma=W_v^\dagger QW_v\in\mathbb R,\quad
\zeta=W^\dagger QW_{vv}\in\mathbb C,
\]
\[
N=\langle J,J\rangle,\quad
\theta=\langle J,J_v\rangle,\quad
\eta=\langle J,J_{vv}\rangle.
\]

Q 的对称性不使 alpha、theta、zeta、eta 自动为实。完整原表达式为

\[
\boxed{B_Q(a,a_{vv})=
\operatorname{Re}\zeta\,N
+2\operatorname{Re}(\alpha\theta)
+\beta\operatorname{Re}\eta.}
\]

用 `beta_v=2Re alpha`、`beta_vv=2Re zeta+2gamma` 改写后：

\[
\boxed{B_Q(a,a_{vv})=
\left(\frac{\beta_{vv}}2-\gamma\right)N
+\frac{\beta_v}{2}N_v
-2\operatorname{Im}\alpha\operatorname{Im}\theta
+\beta\left(\frac{N_{vv}}2-\|J_v\|^2\right).}
\]

对应分部积分的两部分是

\[
B_Q(a,a_v)=\frac12\beta_vN+\beta\operatorname{Re}\theta,
\]
\[
B_Q(a_v,a_v)=\gamma N+\beta\|J_v\|^2
+2\operatorname{Re}(\overline\alpha\theta)
=\gamma N+\beta\|J_v\|^2
+\beta_v\operatorname{Re}\theta+2\operatorname{Im}\alpha\operatorname{Im}\theta.
\]

在原源上，已签有限配对给 `beta=2(gSame_fixed+gOpp_fixed)`；
这里并未借此删掉 W 的梯度或原不同 current 导数之间的交叉内积。
原 J 必须按物理 k 求导：若接口使用 h，则 `partial_k=(2π)^−1 partial_h`。
同一 shifted spectrum 的两因子分别为
`beta−s alpha+s² zeta/2` 和 `N−s theta+s² eta/2`；
其二阶乘积恰给 `alpha theta`。这也直接把原有限顶点 Taylor 与 current Gram 的导数责任区分清楚。

## 真实三维球例子与反控制

程序读取原 289×289 Q，选择原坐标向量 `b=e9+e259`，直接得到 `B_Q(b,b)=4`。
以下是验证通用式的明确测试场，不替换实际 WJ：

| 测试场 a(k) | 精确二阶系数 K_v（v=e3） |
|---|---|
| b | 0 |
| `[1+(2+i)k3]b` | 0 |
| `[1+(1+i)k3+(2−i)k3²]b` | `R³(R²+2)/(3π²)` |
| `exp(iκ k3)b` | `−κ² R³/(6π²)` |

所有积分都是真正三维球／重叠球的精确积分，乘原 d/2。
相位例子从
`L(s)=d·B(b,b)·cos(κs)·Vol(B∩(B+sv))/2` 直接取得非零 K。
常量和仿射给零 K；仿射场的非零球面通量与梯度能量恰相等，
只保留负梯度项会错误地产生非零结果。

程序还对任意复 W、Wv、Wvv 与 J、Jv、Jvv 的两维 jets，
以及任意实对称 Q 的所有系数，精确检查上节三条复恒等式。
反控制取 `W=e^(2iz)b`、`J=e^(−2iz)`，完整 a 实际为常量：
真实 `B(a,a_vv)=0`，若丢掉虚部交叉项则错误得到 **−32**。

## 重放和下一数值责任

```sh
uv run --offline --with sympy==1.14.0 python \
  Verification/physics/low-energy-phenomenology/full-quantum/packet-window-second-order/compute.py
```

当前构造回执为 **1.504 秒 EXIT 0**；`receipt.json` 保存原源输入 SHA、精确三维例子、
球弦系数、复交叉展开和余项合同。解析证明是本 README 的弦 Fubini／一致 Taylor／短弦控制；
有限符号程序负责其精确代数与判别性例子，不把它冒称新的 Lean 积分定理。

同一原源 K_v 的实际积分值尚未计算。后继可直接取
`Re(zeta)N+2Re(alpha theta)+beta Re(eta)` 作为原整体积分被积函数，
由已经生成的 W 与原强 current 导数做严格积分及中心展开误差控制。
本包不填造该数值，也不把此 initial outgoing-current 系数称为 1PI 或 beta。

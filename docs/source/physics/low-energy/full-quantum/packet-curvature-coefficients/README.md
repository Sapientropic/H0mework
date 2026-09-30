# 原波包曲率积分的全方向源系数

**strike 构造完成，待独立认证。** 本包从已经签收的原 289 场 seed 和原
fixed `A1(S01)` 二阶 current 矩阵 Q 生成完整复系数张量与严格整球误差界。
没有改变原准备、independent dual、FullPhase 或物理时间。

## 同一个原 seed 和 current

消费 `packet-seed-regularity/receipt.json` 中的 87 行非零全球分子及
`packet-field/current-data.json` 中原实对称 Q。其余 202 行恒零。

\[
 W(k)=-\sum_{\sigma=\pm1}\ell_\sigma(-k)
      =\frac{N(k,U,T)}{D(U,T)},\qquad
 T=|k|^2/2,\quad U=T\,r(T).
\]

这里 k 是物理动量，r 是原完整 θ 因子生成的根。
N 是已认证的全球多项式分子；代入真实根之后的 W 是解析场。
两个负逆极点、各自的 own derivative、原 clock 因子 c 都已在 W 中，
本包不再另乘 c 或另改 Fourier 号。

原场 a(k)=W(k)J_k 的真正曲率被积函数为

\[
 I_v(k)=\operatorname{Re}\delta_v(k)\,\nu(k)
 +2\operatorname{Re}\!\left(\beta_v(k)\theta_v(k)\right)
 +\alpha(k)\operatorname{Re}\eta_v(k),
\]
\[
 \alpha=W^\dagger QW,\quad
 \beta_v=W^\dagger Q\partial_vW,\quad
 \delta_v=W^\dagger Q\partial_v^2W,
\]
\[
 \nu=\langle J,J\rangle,\quad
 \theta_v=\langle J,\partial_vJ\rangle,\quad
 \eta_v=\langle J,\partial_v^2J\rangle.
\]

本包的 β 对应 `packet-window-second-order` 推导中的 α；此处始终使用上面的定义。
Q 先与实际源分子收缩：188 个原 Q 条目中有 **56 个**与两端非零 seed 相交。
所有估计都在收缩后进行，没有使用原 289 矩阵的 Frobenius 粗界。

## 真实根导数和全张量

令 `Fhat(U,T)` 为原完整偶多项式 F，
`cf=-100383300000000`、`f=Fhat/cf`，则实际 D=f_U。程序从该完整因子生成

\[
 S=U'=-f_T/D,\qquad
 C=U''=-\frac{f_{TT}+2f_{UT}S+f_{UU}S^2}{D}.
\]

没有用首阶色散替代有限 k 的根。生成的中心值是

\[
 S_0=125/162,\qquad C_0=-76325/78732.
\]

设下标 a、b 表示 N 对其显式 k 变量的偏导，R 为径向微分
`S ∂U+∂T`。因为 `∂aT=k_a`，真实组合导数是

\[
 \partial_aN=N_a+k_aRN,
\]
\[
 \partial_a\partial_bN=N_{ab}+k_aRN_b+k_bRN_a
 +k_ak_b(S^2N_{UU}+2SN_{UT}+N_{TT}+CN_U)+\delta_{ab}RN.
\]

D 的相同公式没有显式 k 偏导。对 W=N/D 使用完整商法则，特别保留
`C N_U` 与 `C D_U`。`receipt.json.tensor_polynomials` 给出 α、全部 3 个 β_a
及全部 6 个对称 δ_ab 的精确分子，分母分别为 D²、D³、D⁴；
其系数编码在有理基
`[1,√2,√15,√30,i,i√2,i√15,i√30]` 中。

中心值先从这些真实收缩计算，再与独立中心消费者比较：

\[
 \alpha_0=\frac{1944\sqrt{15}}{390625},\qquad
 \beta_a(0)=0,\qquad
 \delta_{ab}(0)=\frac{144\sqrt{15}}{78125}\delta_{ab}.
\]

## 闭轻球上的严格界

使用同一个原共同域

\[
 |k|\le\sqrt2\varepsilon,\qquad
 \varepsilon=5234375/294988800512.
\]

原根给出 `0≤T≤ε²`、`0≤U≤(1331/1620)ε²`。直接估计 D−1 的系数和，
生成正下界 `Dlower=1−error`。先在多项式层消去
`−f_T−(125/162)D` 的常数项，得到

\[
 |S-125/162|\le3.09374932\times10^{-10},\qquad
 |C|\le11.211290904.
\]

这保留真实的根斜率小量；把 S 当成任意 `|S|<1` 无法支付同一中心误差。
程序中的估计使用未四舍五入的有理数，输出界只向上取整。

对全部实单位方向 v，生成

| 原系数误差 | 严格上界 |
|---|---:|
| `|α−α0|` | `2.54913989×10⁻¹⁰` |
| `|β_v|` | `3.169153940416×10⁻⁶` |
| `|δ_v−144√15/78125|` | `6.14562710075×10⁻⁷` |
| `|δ_e1−144√15/78125|` | `6.95643105×10⁻¹⁰` |

完整精确分数在 `uniform_errors`；全方向界分别由 3 维系数向量范数、
3×3 张量的 Frobenius／绝对值行和生成。不是对 289 维原 Q 再作粗估。

α 整体实值，但 β_y、β_z 及 δ 的若干分量有真实虚部。
本程序保留所有虚部，并估计完整复模长。
特别地 `Re(β θ)=Reβ Reθ−Imβ Imθ`，不能删除后一项。

## 另一个原源消费者及反控制

`controls.py` 使用新的非零 q=1/262144、k=√2q e3，
在完整 F 的代数商环中计算本包张量。Sturm 隔离支付所选原 θ 根，
不先代入近似根。

它与已经独立认证的 `packet-current-taylor` 原 native-circle 构造比较：

\[
 \alpha=\sum_{\sigma,\tau}\ell_\sigma(k)^TQ\ell_\tau(-k),\qquad
 \beta_{e1}=0,\qquad
 \delta_{e1}=4(C_2^{same}+C_2^{opp}).
\]

最后一个 4 来自四种符号排列以及 `二阶导数=2×p²系数`。
右腿保持完整径向根与 own derivative 的变化，第一条腿固定。
这与全球多项式的链式微分是不同的源生成路径。

程序同时生成完整特化因子的互素反控制：冻结真实 S 为中心 S0、
少乘二阶因子 2、用旧同步路径系数替代固定内部动量的二阶式，均改变实际根上的值。
另一个符号中心反控制把 S0 错写为 1，δ_e1 的差是
`−10755974√15/4150390625≠0`。

## 下游积分接口

令上表误差为 eα、eβ、eδ，d0=144√15/78125。
对全部单位 v，可以直接消费

\[
 |I_v(k)-(d_0\nu_0+\alpha_0\operatorname{Re}\eta_{v,0})|
 \le e_\delta\nu_{max}+d_0|\nu-\nu_0|
 +2e_\beta|\theta_v|+e_\alpha|\eta_v|
 +\alpha_0|\eta_v-\eta_{v,0}|.
\]

例如原 current 的共同混合导数界 B1、B2、B3 给出
`|θ_v|≤√νmax B1`、`|η_v|≤√νmax B2`，以及沿球内直线
`|η_v(k)−η_v(0)|≤|k|(B1 B2+√νmax B3)`。
这里没有把量子 current 的 Hessian 或积分值作为本包前提。

同一 sharp 球的已推导系数是
`K_v=(2π)⁻³/4 ∫ball I_v(k) dk`；移动边界已在
`packet-window-second-order` 中保留。此包支付其中的实际源系数，
量子 current Hessian、整球积分包围由下游同一原准备消费者完成。

## 重放

```sh
uv run --offline --with sympy==1.14.0 python \
  Verification/physics/low-energy-phenomenology/full-quantum/packet-curvature-coefficients/compute.py
uv run --offline --with sympy==1.14.0 python \
  Verification/physics/low-energy-phenomenology/full-quantum/packet-curvature-coefficients/controls.py
```

`receipt.json` 使用紧凑 JSON 保存全部精确稀疏系数，`controls.json` 保存另一个
源构造的非空消费者。`construction.json` 只登记冻结构造文件与重放状态，
独立认证另写 `audit/`。

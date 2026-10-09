# 原本构current的完整频域一阶响应

本包将同一原源的三个实际变化共同接入：联合本构路径的传播两腿、原native reader
接触，以及固定准备下的量子source变化。全部48 reader回到同一原theta与原物理频率，
raw、connected及实际均值分别保留；22个总响应严格非零。

## 真实输入与字段变化

取已签原非轴向kin、`rho=1/131072`、同一输入theta小根和
`lambda=6c(1−i)`。背景方向是恒定 `a=dx1 S01`，规范辅助场同时按原图变化：
`b=−star D_Aa/sigma`。

本次X1读取 `JointMomentumJet` 的 **外动量s零阶列**。它是场对背景幅度ε的一阶
变化；不是场对外动量s的一阶导数。输入根U和准备不随ε另选。
程序同时核验原完整两套方程

\[
 H_0X_0=I_0,\qquad H_0X_1+V_{a+b}X_0=I_1,
\]

以及真正共轭左腿的对应289行。I1已由独立Noether源producer在解场前生成，
没有用目标X1反定义外源。

## 原native reader及完整参数接触

原局域Euler reader由已签本构二阶回写给

\[
 Q_b^{eff}=Q_{A_b}+\sum_i(b_b)_iQ_{B_i}.
\]

双时间左右导数分别为 `ell=(conj(lambda),−ik)`、`r=(lambda,ik)`，因此其弱测试
导数固定为 `−ell−r=(-12c,0,0,0)`。这保留原局域Euler的辅助场导数项。
原Bg二阶回写的time边界由 `ReducedCurrent` 实际支付；原scalar与matter也仍在Q中。

reader随同一本构背景变化的 `Qeff'_b` 直接消费 `ReducedContact` 的完整48表，
包含真实Bg／coframe接触与原scalar124。后者在本实际theta上为零的事实保持，
新native接触的16项非零则保留。

对同一实ε参数，真正共轭左场的导数为 `conj(X1)`。令

\[
 C_b=\tfrac12\bar X_0^TQ_b^{eff}X_0,
\]
\[
 C_b^{[1]}=\tfrac12\left[
 \bar X_1^TQ_b^{eff}X_0+\bar X_0^TQ_b^{eff}X_1
 +\bar X_0^T(Q_b^{eff})'X_0\right].
\]

三项逐项生成；原共同分母为theta分母的模平方。所有C、C¹均为实数，完整Fhat的
互素判据与严格根区间支付实际读数，不以某个浮点近根替代。

## 同准备source及非零均值

原物质Hamiltonian不含Bg，所以原 `H+εV` 的current与source变化直接消费既有
`PacketGaugeNoise`／`PacketGaugeDynamics`。ψ、P和归一化保持原值。

在零current探针，两向量的真实全时间常量给

\[
 N_{0,c}=\nu_0/|\lambda|^2,\qquad
 N_{1,c}=\nu_1/|\lambda|^2,
\]
\[
 N_{0,raw}=(\nu_0+\mu_0^2)/|\lambda|^2,\qquad
 N_{1,raw}=(\nu_1+2\mu_0\mu_1)/|\lambda|^2.
\]

这里μ1是实际原均值导数。对于本次非零探针−kin，程序消费投影前的真实全时间
probe差界并生成严格区间，而不是把零探针值直接搬过来。
若同权Laplace向量误差为dJ、dC，零探针未变化向量范数小于1，变化向量的
connected／raw范数分别小于4/7、5/7，则完整两腿误差为

\[
 E_0=2dJ+dJ^2,\qquad
 E_{1,c}=2(dC+4dJ/7+dCdJ),
\]
\[
 E_{1,raw}=2(dC+5dJ/7+dCdJ).
\]

这些界包含原复交叉，两腿没有被重新正交化。实际 `|lambda|²=7776/125`、
η>5与原位置矩共同支付所用常数。

## 全48的同源拼合

频域组合由真实乘积法则给

\[
 \boxed{\Pi_{b,c}=C_b^{[1]}N_{0,c}+C_bN_{1,c},\qquad
 \Pi_{b,raw}=C_b^{[1]}N_{0,raw}+C_bN_{1,raw}.}
\]

原S01/dx1的读数为：

| 项 | 原单位下的系数 |
|---|---:|
| 两条native传播腿 | 0.00000126430346751984050150… |
| native reader接触 | −0.00000000000033718773176… |
| 系数总变化C¹ | 0.00000126430313033210873783… |
| connected总响应 | 0.00000687773579079874… 至 0.00000690962882564981… |
| raw总响应 | 0.00001594516391724132… 至 0.00001598060415122198… |

全部48 reader中，22个connected总响应及22个raw总响应得到严格符号。
本包保留实际频率代数的准确范围；`JointCausal`／`JointFamily` 直接消费这些源表，
把它们识别为同一原时间核和有限本构参数族的双时间current变化。
双Laplace读数不被改称对角单Laplace，当前单动量读数也不代替完整空间积分或beta。

`response.py` 回放两套289场方程、全部原reader及完整严格区间；冻结入口
`construction.json`。无新增Lean声明。

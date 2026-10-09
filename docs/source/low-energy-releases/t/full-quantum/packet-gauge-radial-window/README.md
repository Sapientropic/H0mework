# 原两传播项的直接径向球窗

本包直接消费SpatialCurrent在p_out=0、source／observer同半径B时的两传播窗口。
固定incoming重新编号后，两球是`B_B ∩ (B_B+σ s n)`。对角向只可测有界、沿半径和
真实外s满足下述源生正则性的核Φ，得到无需微分角向frame的二阶积分口。
原source／root／whole-ledger不变；这是完整空间响应的从属积分consumer。

记|n|=1、u=n·ν，Φ_j(k)=∂s^jΦ(k,0)，并保留原物理测度
`dμ=d³k/(2π)³`、`dσ=dS/(2π)³`。定义

\[
I(s)=\frac12\sum_{\sigma=\pm1}
 \int_{B_B\cap(B_B+\sigma sn)}\Phi(k,\sigma s)\,d\mu(k),\qquad s\downarrow0.
\]

则真实单侧展开为`I0+s I1+s² I2+O(s³)`，其中

\[
I_0=\int_{B_B}\Phi_0\,d\mu,\qquad
I_1=-\frac12\int_{S_B}|u|\Phi_0\,d\sigma,
\]

\[
\boxed{I_2=\frac12\int_{B_B}\Phi_2\,d\mu
 +\frac12\int_{S_B}u\Phi_1\,d\sigma
 +\frac14\int_{S_B}
 \left[u^2\partial_r\Phi_0+\frac{3u^2-1}{B}\Phi_0\right]d\sigma.}
\]

复核逐项成立，实际两个有序传播腿合成后取Re。原cos半幅和quadratic半幅给每条有序
分支1/4；两场腿的原Hermitian重排给上式的1/2双分支平均，不另除二。
compute.py从原source窗口表实际读取每个σ的中心，并验证固定incoming重排。

## 球帽直接生成二阶项

固定ν写k=rν。移动球条件的正径向端点是

\[
r_\sigma(s,u)=\sigma s u+\sqrt{B^2-s^2(1-u^2)}.
\]

真实积分上限为min(B,rσ)。对于固定负半球σu<0，

\[
\delta r=r_\sigma-B=\sigma su-\frac{s^2(1-u^2)}{2B}+O(s^4/B^3).
\]

将完整径向Jacobian一起展开，丢失条带的有符号积分是

\[
\delta r B^2(\Phi_0+\sigma s\Phi_1)
 +\frac{\delta r^2}{2}(2B\Phi_0+B^2\partial_r\Phi_0)+O(s^3).
\]

其二阶系数为
`B²[u Φ1+u² ∂rΦ0/2+(3u²−1)Φ0/(2B)]`。
两个负半球互补，平均后便得到上述两项球面贡献；body给`∫Φ2/2`。
这份推导在每条正射线上完成，没有平移角坐标。

真实开关发生在σu=s/(2B)，而非严格在赤道。额外belt
`0<σu<s/(2B)`的球面面积≤πsB，径向深度≤s²/B；每支体积≤πs³。
因此对有界Borel Φ，belt真实保留在O(s³)余项，不能偷换成一个二阶球面项。

准确正则性为：外s的全球三阶Taylor余项有统一界；靠近r=B，Φ0沿半径有统一二阶界，
Φ1沿半径有统一一阶界，Φ2有界。以上Taylor估计、有限球体和球面measure直接给可积的
O(s³)余项。角向仅要求Borel及上述一致界，允许真实jump。

## 同一原frame与实际传播核

正式文件`LowEnergy/PacketField/PositiveRay.lean`直接从原firstNonzero、lineSign、
representative和指定circleParameter证明：对所有r>0和全部k，包括k=0，

\[
\mathrm{lineSign}(rk)=\mathrm{lineSign}(k),\qquad
\mathrm{pairedParameters}(rk)=\mathrm{pairedParameters}(k).
\]

原pairedRotation及两个实际circleAction直接消费这些等式。九枚定理以默认预算、
`--trust=0 -DwarningAsError=true`通过；它证明原旋转部分沿正射线恒定，没有声称整个
poleColumn恒定。后者仍沿原radialPoint／完整隐根演化。

对实际波包，固定ν后原bandOrientation也恒定，UniformSpatialContact中的有符号轴向
参数为`ρ=−lineSign(ν) r/√2`。因此所有径向微分都落在原ρ、U(ρ²)、矩阵逆和真正移动
probe上，frame不贡献导数。原全局theta多项式与隐根导数、统一完整逆／源表、
ProbeLaplace的全时间位置矩给上述实际径向／外s界。原均值、mixed Gram和物理measure
继续进入Φ，当前积分没有替换任何source或准备态。

若Φ0另外具有真实球面W¹,¹ trace，球面分部积分给

\[
\int_{S_B}u\partial_n\Phi_0,dS
 =\int_{S_B}\left[u^2\partial_r\Phi_0+
       (3u^2-1)\Phi_0/B\right]dS.
\]

这识别旧角向写法与本径向写法。径向公式本身不需要该附加条件，故不会把Borel frame
误当全局可微。CurrentSeam的实际读数相容仍保持其独立能力。

## 完整积分消费者

程序以一般复二次空间核加真实s／s²项，先对整个三维lens的圆盘与两段z弦精确积分，
再读出前三系数，完整复数与径向公式一致。该消费者保留Φ1的非零贡献，未仅检查常数核。

另取有界角向jump核`Φ0(ν)=ν1 1_(ν3>0)`，n=(3/5,0,4/5)，Φ1=Φ2=0。
在未附物理measure因子的几何积分中，真实二次系数为`9πB/50`；若误用两片内的普通
角向导数，得到`3πB/50`，相差`3πB/25≠0`。半球单项式积分精确复现两数。
它说明角向jump确实会破坏那种直接替换，而本射线证明仍合法。

本包的球窗定理是解析证明配合精确有限系数与完整lens消费者；正射线frame身份由Lean
单独核验。没有将一般积分解析论证冒充已形式化的Lean测度定理。

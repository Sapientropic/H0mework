# 原双jet current与联合插入的完整旋转接线

本文件消费本包source.py实际返回的原密度、Hodge、curvature与72个QB；
左右四动量ell、r的八个分量始终独立。它生成原9个空间SU(2)方向的完整native reader
有限协变，以及固定world `A1=S01`在同一原incoming frame中的确切九权重。
原source、独立dual、物理时钟和全部289字段保持。

## 原密度而非二次Hessian的替代

按axis.py同一顺序取

`mu=1,2,3`，每个mu依次为 `S01`、`A01`、`Cartan01=D0−2−(D1−2)`。

source.py的真实接口 `main(return_native=True)`给出原bare双first-jet槽、
`D_A(p)`、原star和全部QB。native-covariance.py由它们直接生成

\[
B_a(\ell,r)=-\star_eD_A(-\ell-r)a/\sigma,
\]
\[
Q_a(\ell,r)=\widetilde Q_{A_a}(\ell,r)
 +\sum_j[B_a(\ell,r)]_j Q_{B_j},\qquad\sigma=1/2.
\]

这里B嵌入原289的gauge-B行。所有scalar槽和独立dual槽均参与系数运算；
没有先令ell=−r，也没有用已有Hessian的旋转恒等式代付该三次密度。

原系数为实，且完整slot exchange逐项成立：
`Q_a(ell,r)=Q_a(r,ell)^T`。所以取ell=conj(r)时得到真正Hermitian reader，
这个实化双jet身份不把原independent dual改成primal bra。

## 三个实际生成元的全系数恒等

令J为原289字段生成元，S为相应四维空间旋转生成元（时间分量不动）。
原九方向嵌入E9满足 `J E9=E9 J9`。全部9方向、3个生成元及8个独立动量变量上，
程序直接核验

\[
J^TQ_a+Q_aJ+
D_{(S^T\ell,S^Tr)}Q_a+Q_{Ja}=0,
\]
\[
D_{(S^T\ell,S^Tr)}B_a+B_{Ja}=JB_a.
\]

每一项都来自原bare density与真实Bg图。原矩阵有289行、289列；没有投影到theta后
才验零，也没有丢掉time slots。

令原circle为L(t)、R(t)。其实际系数分别支付

`L′(t)=4J L(t)/(1+t²)`，`R′(t)=4S R(t)/(1+t²)`，且两者在0为单位。
因此对上式沿实际circle微分并消费同一初值，得到

\[
\boxed{L(t)^T Q_{L(t)a}(R(t)^T\ell,R(t)^Tr)L(t)=Q_a(\ell,r),}
\]
\[
B_{L(t)a}(R(t)^T\ell,R(t)^Tr)=L(t)B_a(\ell,r).
\]

这保留的是同一source-generated circle；ODE所需的每个系数和初值也在本程序中重放。
多项式恒等允许ell、r取复数，因而直接覆盖实际双Laplace参数。

两个直接特化分别为：

- 联合source插入：`ell=−pout,r=pin`，真实b的动量是 `pout−pin`，得到完整V。
- native current：`ell=conj(pout),r=pout`，weak reader为 `−conj(pout)−pout`。

第一式不要求两腿时间频率相同；第二式保留原conjugate频率，不能换成opposite口。

## 原固定world probe的九个权重

三个color方向均使用原未减半的native矩阵：

\[
[S01,A01,Cartan01]=2[sourceColor_0,sourceColor_1,sourceColor_2].
\]

由原native pairing直接算得这组三方向Gram为 `2 I3`。Cartan列必须是索引6减索引7，
没有额外1/2。

更强的有限系数身份对每个原circle都成立：

\[
L_{axis}(-t)E_9=E_9\,[R_{axis}(t)\otimes R_{axis}(t)].
\]

程序逐项比较其全部degree0至8系数；不是从数值点推断。对原有序字

\[
L=L_z(t_z)L_y(t_y),\qquad R_{sp}=R_y(t_y)R_z(t_z)
\]

相乘便得

\[
\boxed{L^{-1}(A_1S01)=E_9\,\mathrm{vec}(vv^T),\qquad v=R_{sp}e_1.}
\]

这里vec按空间方向i在外、color方向j在内排序，正是axis.py的九方向顺序。
因此轴向9×9 source/reader张量由 `w_(ij)=v_i v_j` 在两边收缩。
同一固定incoming frame中的外物理动量为
`d_axis=Rsp d_world`；不存在额外sqrt2、2pi、Fourier测度或Taylor因子。
原密度的Taylor半因子由原current消费者保持，不由旋转重新产生。

等价的body reader公式为

\[
L^TQ_{a_{world}}(p_L^{world},p_R^{world})L
=Q_{L^{-1}a_{world}}(p_L^{axis},p_R^{axis}),
\quad p^{world}=R_{sp}^Tp^{axis}.
\]

固定incoming做external d微分时，L与v保持固定，左右动量及真实Bg图按上面的全slot口微分。
因此该接口可直接消费axis.py的15个真实radial/external jets，无需微分一个随输出变化的frame。

## 原源消费者与反控制

`(ty,tz)=(1/5,1/3)` 的全289反向作用精确回读 `v⊗v`。
把空间字写成Rz Ry或把Cartan减半都产生非零原字段差。
另一个非轴复频率点上，全部九个profile中：

- native reader和opposite-slot矩阵确实不同；
- 删除真实Bg reader项也确实改变原矩阵。

这两项是对原密度读回的反控制，并不把bare密度自身的协变误报为失败。
源码、有限代数与上述ODE推导构成本接口的证明；没有新增Lean声明或source更换。
准确执行结果和全部校验口见native-covariance.json/log。

重放：

```sh
uv run --offline --with sympy==1.14.0 --with python-flint==0.8.0 python \
  Verification/physics/low-energy-phenomenology/full-quantum/packet-gauge-spatial-propagation-curvature/native-covariance.py
```

同包其他文件由构造者拥有；本责任只写native-covariance四个前缀文件，交其总包独立认证。

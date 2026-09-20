# 原主符号作用归一独立认证

**Verdict: certified。** 原48个规范分量的完整二阶主符号、原Hodge辅助消元、固定背景proper clock换元、252／70维主符号及实际weak横向与自由态电流消费者全部通过。没有候选修复项。

## 对象与权威

冻结对象为上一层 `compute.py / receipt.json / README.md / exact-check.log`。fresh replay EXIT0，完整JSON与冻结回执相同；审计只新增本目录，候选未改，未提交。

来源保持 `positiveSmoothUnifiedSource`、实际Dirac-dual form-native母作用、原actual，以及 `Stage10.Runtime` 的 `SpinPair.visit 10 / materialEntry / tickAt 16` 和tick17后继。本组是从属作用／特征归一producer和readout，不产生新的controller authority。

已认证输入为 [原活跃作用](../../active-gauge/audit/certification.md)、[FullPhase](../../full-phase/audit/certification.md)、[完整标量交换](../../scalar-exchange/audit/certification.md)、[空间弱交换](../../weak-exchange/spatial/audit/certification.md)、[自由物质源](../../matter-modes/audit/certification.md)及[原物质顶点](../../matter-vertices/audit/certification.md)。关键新计算由本组独立重建。

## 原作用、Hodge与native配对

[`independent_check.py`](independent_check.py) 不导入候选程序。它直接读取原定向二形式槽 `(01,02,03,23,31,12)`、原Hodge列表及wedge互补索引。原Dirac-dual母作用确实调用同一 `generatedFormNativeGaugeDensityAtBoundary`。

对正lapse的一般对角coframe `e=diag(N,1,1,1)`，由实际源码的

```text
star=(∧²e)⁻¹ J(∧²e)
```

重新生成 `star(E,B)=(B/N,−NE)`。原wedge矩阵W满足W·star对称、star²=−I。直接微分原作用

```text
L=bᵀW F−(σ/2)bᵀW star b
```

得到真实辅助Hessian `−σW star` 及实际解 `b=−star F/σ`。把该解代回原作用，而后再次求Hessian，精确给出

```text
Lreduced=N/(2σ) Σκ(Ei,Ei)−1/(2σN) Σκ(Bi,Bi)。
```

这里没有在topological BF项外额外乘体积；N来自原Hodge。二次项的1/2由实际两次微分保留。

native κ直接按源定义的SU3迹、SU2迹及单个hypercharge乘积生成，没有先取母迹再凭名称识别。原Y方向的native值为1、母SU7迹为2；完整κ的本征值为 `1[2],2[9],3[1]`，包括两个color Cartan方向的非对角配对。

## 全48主符号与原289消元

独立计算原curl矩阵 `T(p)A=(pμAν−pνAμ)`，使用真正的有号导数转置 `T(−p)ᵀ`，得到

```text
Kprincipal(p)=Kspacetime(p)⊗κ。
```

该48×48矩阵的224个非零条目、336个二阶单项式逐项等于原121矩阵，而非挑选单个轴或单个生成元。

审计还从原H289读取72维gauge B常数块，核对实际逆的左右乘积；两侧一次导数块与源BF完全相同。它们的真实Schur项 `−HAB HBB⁻¹ HBA` 再次恢复同一336个二阶系数。因而已支付原作用→辅助消元→全部主符号的连接。

`Kspacetime(p)p=0` 是该主部的恒等式。原完整121算子作用于相同weak梯度方向实际非零，反控制拒绝把此恒等式改称完整背景的十二个规范对称。

## 同一固定背景的proper clock

原度规为 `eᵀηe`，固定空间位置的 `sqrt(−g00)=N>0`。审计分别支付

```text
τ=Nt，∂t=N∂τ，At=N Aτ，dt=dτ/N。
```

一形式curvature的电分量得到N倍、磁分量保持；动作积分密度另得到1/N。全部4×4 Hessian同时满足实际congruence

```text
Kτ(ν,p)=diag(N,1,1,1) Kt(Nν,p) diag(N,1,1,1)/N。
```

结果确为

```text
Lτ=N²/(2σ) κ(Eτ,Eτ)−1/(2σN²) κ(B,B)，
1/gE²=N²/σ=108/125，1/gB²=1/(σN²)=125/27，
gE²=125/108，gB²=27/125。
```

这里 `1/g²` 的定义对应作用中的 `κ(F,F)/(2g²)`。这是对**同一固定原背景作用**的钟坐标重写；换元后把原lapse参数直接重置为1会给出不同矩阵，已作为反控制拒绝。两项系数不是独立拟合的源参数。

## 原传播主部与真实消费者

从当前Lean γ字面量重新生成全部252维 `Cμ=iΓμ/eμ`，逐项匹配FullPhase并证明

```text
(ΣpμCμ)²=(p0²/N²−Σpi²)I252。
```

原完整70实标量算子的二阶齐次部分经真实 `p0=N√2u,pj=√2rj` 读回，同样等于该多项式乘I70。

原121的A34、S34两个横向通道均直接满足

```text
Kweak T=−4N(λ²+k²/N²−1/2)T。
```

审计进一步生成其原gauge B回写，并把两个实际横向字段lift送入**全部289行**，所得只有该精确原横向方程；没有用商空间任意forcing代替原场。上式保留完整常数项−1/2。

其特征速度在原坐标中分别为物质／标量N、weak横向1/N；同一proper clock下为1与 `1/N²=125/54`。该数是速度之比，proper clock下速度平方比为 `(125/54)²`。它来自最高导数特征，未把有限动量完整色散或群速度替换成同一个常数。

最后从原A34 fundamental矩阵、实际外幂作用及Γ1独立生成原空间顶点 `V=N iΓ1ρ(A34)`，和冻结顶点完全一致。原prepared实电流矩阵

```text
Cfree=F†[√2(SV+V†S)/2]F
```

自伴，实际 `(24,30)` 条目为 `6√15 i/25`。取真实单位自由向量 `ψ=F(e24+i e30)/√2`、独立dual读回 `χ=√2ψ†S`，直接得到

`Re(χVψ)=−6√15/25 ≠ 0`。

这使空间weak current消费者明确非空。认证未添加全场LSZ、单一Lorentz不变物理beta、实验粒子或模型no-go结论。

## 验收证据

- [`replay.log`](replay.log)：冻结程序fresh EXIT0，完整receipt相同。
- [`independent-check.log`](independent-check.log)、[`independent-receipt.json`](independent-receipt.json)：独立原作用、72维逆、336系数、完整clock congruence、252／70主符号、两条全289消费者及真实非零电流全PASS，34.894秒。
- 反控制拒绝辅助解翻号、母迹替代native U1、丢失二次1/2、换钟后重置lapse，以及主部梯度核冒充完整背景对称。

本候选没有新Lean声明。新增矩阵与作用归一身份按精确符号程序证据签收，所消费Lean源口和标准公理集沿用上游认证；无新axiom，也未冒称新Lean端到端定理。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/principal-normalization/compute.py --root . --out /tmp/principal-normalization-audit.json
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/principal-normalization/audit/independent_check.py --root .
```

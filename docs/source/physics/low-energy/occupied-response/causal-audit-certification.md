# 原占据态零动量因果电流独立认证

**Verdict: certified。** 五个源谱投影、完整48脉冲的正时间／跳跃方程、2304项因果读数与正阻尼变换，以及复频率原48维Schur消费者全部成立，没有候选修复项。

## 冻结对象与依赖

对象为上一层 `compute.py/README.md/receipt.json`。fresh replay EXIT0，除运行耗时外，完整 JSON 与冻结回执一致。

本组消费[原占据响应认证](../../audit/certification.md)和已认证、已迁入正式路径的 [FockDynamics](../../../fock-dynamics/audit/certification.md)。原 H12、actual 制备、完整规范顶点、独立 dual、原时钟及 source/action/root/current/next 保持。

本包没有新 Lean 声明。实际矩阵由精确程序核验；真实有限演化与正阻尼可积积分由 FockDynamics 已签收的公开口消费，没有新增公理或宣称这些矩阵已成为新的 Lean 全矩阵定理。

## 原谱的独立生成

[independent_check.py](independent_check.py) 不导入候选程序。与候选的多项式投影算法不同，它先由原 `h0/ω` 的特征多项式求出全部实有理根，再实际求各个 `ker(h0/ω−rI)`，用其 Gram inverse 构造正交投影。

五个投影逐项等于冻结结果，分别支付 Hermitian、幂等、相互正交、本征身份、秩和完备性：

| 速率／ω | 物质投影秩 | 合并current留数秩 |
| --- | ---: | ---: |
| −2 | 3 | 6 |
| −3/2 | 2 | 4 |
| 0 | 2 | 0 |
| +3/2 | 2 | 4 |
| +2 | 3 | 6 |

按原时间 `phase=exp(−iωt/2)` 组装有限谐波 U(t)，再核验双侧幺正性、U(0)=I、`U′=−ih0U` 和 `U(t)w=w`。原 prepared 的两相位分支分别保持原频率±ω，不把共转h0替换为原完整Hamiltonian。

## 原脉冲、双侧电流与source jump

Tseed与Bseed由原48个 T／B 实际作用于 `ψ0=2w` 重算。每个频率的前向和反向权重都直接读取原矩阵，再形成

`Rr=Dr−A−r`。

原幅度平方4包含在ψ0中，B始终是原current `−sQT`。

审计用频率系数字典，而非依赖候选整体 Laurent 式的一次消去，重建

```text
δψr = −i Pr Tseed,
Yr = L Split⁻¹ [δψr; conjugate(δψ−r)],
χr = −i Rr.
```

L是父包原canonical-dual实图。对每个频率独立核验 `conjugate(Yr)=Y−r`、`conjugate(χr)=χ−r`，因此真实primal和independent-dual坐标一并恢复。

原 H289 的48物质块在零空间动量下是 `M0+p0M1`；mg与gm由其真实gauge/matter交叉块直接读取。逐频率支付

```text
(M0−iωr M1)Yr=0,
gm Yr=χr,
M1 ΣrYr+mg=0.
```

这分别给出 t>0 的全部48条原物质方程、全部2304个current读数，以及零过去选择下的原delta-source跃变。M1实际非奇异，matter右跳跃非零；没有把初始source强迫删除。delta写回使用通常Heaviside导数及上述精确跳跃系数，没有冒称新增了Lean分布方程定理。

current右跳跃另由所有原发生器／读数逐项重算为

`4i w†(Tc Bb−Bb Tc)w`，

其非零条目恰为44。把matter跳跃改号，原source系数不再相消，独立反控制非零。

## 零率消去保留了什么

审计明确验证：`R0=0`，但原 `P0` 的秩是2、`P0w=w`，零率 `δψ0` 与其48实坐标图 `Y0` 都非零；`D0`、`A0` 也各自非零。

因此消失的是两个非零current权重的合并留数，原母物质零模及静态物质响应并未删除。只保留±2ω也不能代表整个48×48时间current；±3ω/2的非零矩阵权重仍在。

## 正阻尼的全部2304项积分

FockDynamics 的 `retardedMode_integrable/finite_retarded_transform` 对实际实频率ωr及η>0，支付每一项真实 Ioi0 积分。审计逐项消费其值

`i/(E+iη−ωr)`，

并对全部矩阵条目核验

```text
∫₀∞ exp(iEt−ηt)χ(t)dt
 = Σr Rr/(E+iη−ωr)
 = Bseed†(z−h0)⁻¹Tseed
    −Bseedᵀ(z+h0)⁻ᵀconjugate(Tseed),
z=E+iη.
```

两个12维spectral inverse的左右乘积都精确为I12。全部频率为实数，η>0时每个分母虚部为η，因而该整个上半平面都处于真实可逆域。

审计还把 **matter脉冲本身** 作同一有限Laplace变换，并对任意E、η>0直接验证

`(M0−izM1)Yhat+mg=0, gm Yhat=Pihat`。

因此既核验current公式，也核验其背后的原独立dual物质响应。signed transpose关系 `Rrᵀ=−R−r` 与 `Pi(−z)ᵀ=Pi(z)` 保留；将η改成−η得到不同结果。

## 真实复频率与非零条目

在 `z=(3+i)ω`，独立算法从原M48直接求完整inverse，核验其左右乘积I48，再生成 `−M48⁻¹mg`。全部原matter行及2304个current条目与冻结结果、有限Laplace脉冲完全相同。`z=3ω` 还逐项恢复父包实频率消费者。

第00条目只有±2ω两个谐波，其系数直接读为 `−4is` 与 `+4is`，所以

```text
χ00(t)=8√2 sin(2ωt),
Pi00(z)=−16√2 ω/(z²−4ω²).
```

它在父包 `z=3ω` 给出同一非零读数。实轴避开实际pole时，有限有理式连续给出η→0+读回；没有将这扩写成分布边界存在或整个时空场的无阻尼积分。

本证书范围为原prepared、k=0、零过去及正阻尼下的因果规范响应。未另选真空、Feynman处方、圈积分测度，也未将原外加脉冲读回称为完整boson自洽解。

## 证据

- [replay.log](replay.log)：冻结程序 fresh EXIT0，完整数据除耗时相同。
- [独立程序](independent_check.py)、[输出](independent-check.log)、[回执](independent-receipt.json)：零空间算法、全部谐波原方程、jump、2304积分／resolvent及复频率full48逆全部 PASS。
- 已认证 Retarded 的严格证明支付真实可积性和有限求和积分交换；没有仅用CAS不定积分代替这项责任。
- 仅新增本 audit 文件，没有修改候选或提交。

```sh
uv run --with sympy==1.14.0 python -u Verification/physics/low-energy-phenomenology/occupied-response/causal/audit/independent_check.py --root .
```

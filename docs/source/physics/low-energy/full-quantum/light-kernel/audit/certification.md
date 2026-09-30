# LightKernel6 独立认证

**Verdict: certified，可按当前声明范围晋升。** 未发现候选缺陷。

对象：`Lean/scratch/LowEnergyLightKernel/{Graph,Jet,Source,Scaling,Characteristic,Metric}.lean` 及其冻结精确胶囊。原 source、Dirac-dual 作用、`SpinPair.actual`、物理时间、Stage10 current/next 不变；本包为原低能读出的 subordinate producer/consumer。

## 内核事实与声明计数

六模块、原 Audit/Consumer、独立 [Consumer.lean](Consumer.lean) 已 fresh 执行 `--trust=0 -DwarningAsError=true`，默认限制全部 EXIT0。**74 项声明**＝62 个候选公开声明＋7 个原消费者＋5 个独立消费者，仅使用 `propext`、`Classical.choice`、`Quot.sound`。证据见 [focused.json](focused.json)、[trust-summary.json](trust-summary.json)。mouth lint 只有允许的 `autoImplicit false` 提示。

五个独立消费者核验：同阶特征式在 u=0 消失时二次时间尺度仍非零；g00 静态接触与时间轴极限不同；原 reader/source 两腿反号且错号给不同读数；源 lapse/spinScale 将慢频率平方转换为 −3/20；二阶逆近似不等于真逆。

`Graph` 从真实补块逆生成零模图、单射与完整核覆盖。`Jet` 给出非交换二阶逆及**精确**余项，`source_complement_inverse` 从明确的小范数条件生成真可逆域；没有把近似逆声明成精确逆。`Source` 的具体 5×5 系数、`Scaling` 的精确行因子、`Characteristic` 的复数穿孔极限和 `Metric` 的原双腿读回均已内核检查。

## 独立原矩阵重建

[independent_check.py](independent_check.py) 核验原 26 份源码，并采用与候选不同的构造：

1. 从原 K61(0) 的**完整 nullspace**生成归一化零模图，验证秩五、保留坐标恒等、全部零方程及真实 56 主补块的双侧逆。把五个裸坐标轴当零模会留下 3 个非零矩阵项。
2. 从字面 `SpinPair.spinPairCoefficients`、`diracGammaFive` 和五条实际 primal/independent-dual 参数路径取导数，重建原 289 维五列。经实际 Q 和字段缩放得到坐标变换 M，`det M=4`；真实图完整恢复原 289 五列，未以商空间名字替代原场身份。
3. 对固定零模图 E 作常坐标变换，以独立 Feshbach 二阶式

   `S1=EᵀK1E`，`S2=EᵀK2E−EᵀK1 B (BᵀK0B)⁻¹ BᵀK1E`

   分别计算 61 和原 103 两条路线。原 98 主补块双侧逆由实际 K103(0) 生成；两条路线给出同一完整二阶 5 核。
4. 从这次生成的 103 场 jet 和原辅助场回写生成全部 289 场。原注入独立解负动量的 symmetry/Ward 消零行，未用 HF 反向定义 J。逐项验证 `H289 F−J S`：所有次数≤2的项为零，**完整余项 172 个非零条目、首个总次数为3**，与冻结回执一致。

## 两个特征尺度与完整源

对已认证的原完整 103 行列式因子作有限幂级数卷积，显式保留并检查每个低阶系数。除以原 98 常项补块行列式后：

- 同阶缩放的 0…7 阶全部为零，8 阶系数在原五扰动基下为
  `655360/537273 · u²(5q²+3u²)(55q²+67u²)(125q²−162u²)`。
- 时间权重2、空间权重1时，0…9阶全部为零，10阶系数为
  `512000000/439587 · (36σ²+25)`。

这与具体轻核的行列式展开独立吻合。保留坐标基的两个系数分别少 **16=(det M)²**，没有丢失基变换因子。

另在原非零点 `(u,q)=(1/7,1/11)` 直接计算真实 98 双侧逆、完整 103 各源块行列式和真 Schur 核，验证源因子乘积、Schur 行列式身份和非交换逆余项。该点真轻核与二阶核有 **25** 个不同条目，明确拒绝用截断核代替全核。

三个线性首阶比值与慢频率比值分别为

`λ²/k² = −18/25, −594/1675, 1/3`，`λ²/k⁴ = −3/20`，

均按 `λ=N√2u`、`k=√2q` 生成。所有 289 行回写使用原空间 Fourier 因子 `i√2q`。在 q=1/11，对三条首阶线及 `u=(5i/6)q²` 各取实际点，完整原行列式因子均非零；这些斜率不能被改写成有限动量的精确零线。

## 原 g00 源

从原 289 场 reader 与真实 56 补块独立生成接触 `18N/125`。原五扰动基的三维二次核上，一次 reader 为 `(0,0,−36u/25)`，独立反动量 source 为 `(0,0,36u/25)`。真轻解与接触之和恢复

`18N(297u²−125q²) / [125(162u²−125q²)]`。

错用同号源腿给出不同读数；两个轴向极限分别为 `18N/125` 与 `33N/125`。该值是原逆核读数；先前签收的 `+jδg00` 作用约定继续取负逆场响应。

## 范围、回放与来源

具体 56/61/98/103/289 矩阵、原五场身份、独立注入及完整原行列式因子的接口由精确程序支付；Lean 支付通用图/逆余项机制和具体 5 核的代数、首项极限、原 reader/clock 消费。没有把实际大矩阵坐标表误签为已全量 Lean 化，也没有把真特征首项扩大为已构造的完整谱支。

本包范围是原轴向低动量展开、原 independent dual 与同一 source 规范代表。原 Π 消费一次，未新增真空、实验单位或粒子身份。

五个冻结程序均独立重放，写入定向保存在 audit，全部输出除时间外与原回执一致，见 [replay-compute-summary.json](replay-compute-summary.json)。独立检查用时 **26.948 秒**，详见 [independent-receipt.json](independent-receipt.json)。自建检查器的数域返回值转换曾发生 Python API 错误，修正仅在 audit 脚本；最终全检通过，未涉及候选数学。

所有新增内容仅位于本 audit 目录；候选、正式源码、authority 均未修改，没有提交。

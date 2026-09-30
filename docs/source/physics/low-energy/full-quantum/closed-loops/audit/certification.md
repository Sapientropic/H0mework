# ClosedLoops3 独立认证

**Verdict: certified.** 冻结 `Grading/Source/Words` 三模块在正式 Triangular 依赖上全部通过默认 `--trust=0 -DwarningAsError=true`。原 independent-dual 完整矩阵词的三角展开、任意有序闭迹、原规范/标量接口及完整 Stage10 读回正确；没有发现候选缺陷。

41 个公开声明、2 个原消费者、5 个独立声明与7个已认证联合真空支持声明，共55项精确公理回执，仅使用 `{propext, Classical.choice, Quot.sound}`。见 [focused.json](focused.json)、[consumer-focused.json](consumer-focused.json)、[trust-summary.json](trust-summary.json)。无新增公理、`sorry`、不安全求值或预算放宽。支持模块仅在临时目录原样复用证明正文，imports 对齐正式 Triangular 路径。

## 准确的 producer 与 readout

`Arrow A` 的口径是 `P6 A=A`、`A P6=0`；`Expansion A A0` 表明 A0 保持同一 P6，而 A-A0 是这条单向项。乘法定理先支付两个 Arrow 的乘积为零，再保留完整差式

`AB-A0B0=A0(B-B0)+(A-A0)B0`。

`Expansion.product` 按原列表顺序递推，不交换不同因子，也不把完整算子先换成对角块。闭迹读取最后通过有限矩阵 trace 的循环性消去单向差。空词由 identity 支付；任意长度及重复因子均在同一证明内覆盖。

这些通用定理消费每个因子的真实 Expansion。`Source` 从原 `H/H0`、真实 `R/R0`、原 C0 逆与实际 `Exchange.currentOperator` 自动生成所需实例；caller 不提供目标闭迹等式或任意分块见证。原标量方向直接由修复的右手 Yukawa 的 output/input 结构生成 Arrow。

`source_variation` 取任意两个 configuration、point、momentum 的完整 H 差，保留它们各自单向部分之差。它没有假定所有非标量变分都保持分级。闭迹的“independent_yukawa” 准确表示：在每条 line 自身固定的原系数下移去显式单向项；不同 configuration 的自由部分仍按原定义变化，并未声明 scalar 对 coframe/connection 的隐含依赖消失。

## 完整传播与原源

`GaugeLine.Regular` 同时要求原时间 principal 非特征和源自由核可逆。`GaugeLine.propagator` 消费两条条件，支付原 Dirac D 与完整 G_D 的双侧逆；`generated` 随后由完整 `i R C0⁻¹` 与原 gauge currentOperator 得到词因子。可逆域的非空 actual 实例由源 charpoly 产生，未以假域或零顶点交差。

`gauge_word_generated` 与 `gauge_loop_independent_yukawa` 对整个有序列表保持完整 propagation/vertex 构造。原 scalar 在两侧合法完整规范词之间仍是 Arrow，故闭迹为零；两条任意原 scalar 之间的合法完整规范链也支付开放算子零。它们均针对原单向顶点，不包含 reverse adjoint。

原 source readback 先组成全部 word，再进入 `insertion` 与原 Stage10。它保存 independent dual、C0 次序、真实 source 幅度 `4 spinScale`，没有在中间插入旧八维读取投影。有限 matrix trace 与该 prepared-source pairing 是不同读取；本包分别证明对应身份，没有赋予 matrix trace 一个未构造的 vacuum measure。

## 独立非空消费者

[Consumer.lean](Consumer.lean) 使用原 SpinPair 色电流的非零实际矩阵元，证明原规范 vertex 非零；再由源生成的 actual regular z 和真正 Dirac 左逆，证明同一 GaugeLine.full 非零，并消费其双规范闭迹身份。

当前标量消费者从 `actual.scalar` 读取当前 **finiteGenerationJointBreakingScalar**，复用上一轮已认证的实际右手联合质量探针：该原 scalar vertex 同时满足 Arrow、非零及闭迹零。另一消费者将当前 scalar 放在任意两侧合法完整 gauge word 中，同一项同时获得闭迹零与完整 Stage10 原源读回。证明没有把 trace=0 改写成 operator=0。

## 全158原顶点及精确反控制

[independent_check.py](independent_check.py) 在保留全部原 Fourier jet 符号的情况下，核验48 gauge、24 Lorentz、16 coframe、70 scalar 的三角 Expansion。这里消费的是已认证的 **densitized primitive vertices**；形式化 GaugeLine 则消费其明确声明的原 currentOperator，未混淆两者的体积因子。

coframe 的四个对角方向具有精确单向部分：

`delta_e00: Y`，`delta_e11/delta_e22/delta_e33: N_lapse Y`。

其余12个 coframe 方向的这一部分为零。四个非零方向均不保持 P6，程序保留了它们的原体积变分项。原 lapse 改变的 H 差同样保留非零单向部分。

两组不同原动量/复频率的完整 Dirac G 均用独立 trace-recurrence 逆核验两侧恒等及三角差。长度2、3、4的词不仅核对最终 trace，还核验整个 operator product 等于自由有序乘积加逐个单向插入之和。二、四因子闭迹非零；三因子示例闭迹为零而开放差非零。交换四因子例子的最后两个顶点会改变 trace，直接排除了无序乘积替换。

所有70个 scalar vertex 本身非零，其规定闭合插入 trace 为零。独立检查 `V_i G P6=0` 与 `P6 V_j=V_j`，覆盖全部4900个不同 scalar 对的完整链，未仅测试相同顶点。原反向伴随给出

`tr(N†N)=1296/125`，`tr((N+N†)²)=2592/125`。

因此正实观测的 Hermitian 替代或 reverse arrow 不满足本包的单向消去口径。精确证据见 [independent-receipt.json](independent-receipt.json)。普遍列表定理由 Lean 支付，有限词示例不代替其普遍性；完整物理多点态和路径权重也未由这些闭迹身份补入。

本审计只新增 `closed-loops/audit/`，未修改候选证明、原 source/root/current/next、active 或 Git 索引，未提交。`git diff --check` 通过。

# 原物理时间 Phase3 独立认证

**Verdict: certified.** 三个冻结模块的全部 32 个公开声明、四个原消费者和五个独立消费者通过默认预算 `--trust=0 -DwarningAsError=true`。没有发现候选缺陷。原作用、物理时间、source/root/current/next 均保持；本证书签收从属相位输运及其原源消费者。

候选为 `SpatialResponsePhase.lean`、`SpatialResponsePhaseKubo.lean`、`SpatialResponsePhaseDuhamel.lean`。复验见 [focused.json](focused.json)，独立消费者见 [Consumer.lean](Consumer.lean) 与 [consumer-focused.json](consumer-focused.json)。全部 74 项公理回执由 32 项候选、4 项原消费者、5 项独立消费者和原样重用的 33 项已认证控制夹具组成；精确集合均包含于 `{propext, Classical.choice, Quot.sound}`，见 [trust-summary.json](trust-summary.json)。没有新增公理、`sorry`、不安全求值或预算放宽。mouth lint 仅报告本仓约定的 `autoImplicit false`。

## 已支付的实际机制

1. **原 T/B 生成相位对易。** `gaugeCurrent_commutes_charge` 消费原 `B=-spinScale Q T` 与已生成 `[Q,T]=0`。有限算子指数、L∞×L² 的实际 ae 乘子和傅里叶变换把这一关系输运为所有局域 T/B 与 `P(r)` 的对易。公开源接口不以相位不变证书为 premise。`spatialUnitary_phase` 消费同一 `h(2πξ)`，不引入 U 的算子范数连续性。
2. **Heisenberg、原电流与 Kubo 核。** `originalHeisenberg` 由真实 `U_original(t)† A U_original(t)` 构造。其与共转算子的等式针对原局域 T/B，并由相位对易和内积等距导出。Kubo 次序保持 `+i[R_H(s),B_H(t)]`；强迫与电流仍分别采用 T 和 B。力剖面为实的假设支付自伴性；涉及实原电流密度的接口另有探测剖面的实性要求，复值代数接口没有被误报为实观测量。
3. **真实原时间积分。** `originalLocalFirstOrder` 直接使用 `∫₀ᵗ U_original(t-s)(-i R(s) U_original(s)u) ds`。积分核中 `P(t-s)P(s)=P(t)` 由源相位群律产生，然后才把固定有界 `P(t)` 移出已证可积的向量 Bochner 积分。两条原电流腿共同给出 `originalLocalVariation`；原准备与完整响应算子最终进入原 Stage10 读数。此处没有算子值 Bochner 积分或中间八维压缩。
4. **准备时刻与演化时长。** `prepared_originalFree_readback` 的准确式为 `U_original(t) P(tau)u=P(t+tau)U_co(t)u`。`tau` 是准备态的原相位，`t` 是随后演化的原时间参数；没有把 `U_co(t)` 改成 `U_co(t+tau)`，也没有平移或替换控制历史。中性响应的准备相位可从双线性核中相消，字段本身的准备相位仍保留。
5. **完整 CAR 字。** 同一相位同时作用于准备与全部测试函数，实际 Gram 保持，由已证全字递推给出任意完整有限字不变。不同时间的原测试函数逐腿为 `P(t_i)U_co(t_i)f_i`；定理保留各自 `t_i`，创建/湮灭间没有投影。

## 独立源检查与有判别力的消费者

[independent_check.py](independent_check.py) 从原 γ 矩阵、色 Pauli 生成元、SpinPair 系数和原 P286 基重建四个 Hamiltonian 系数及全部 48 组 T/B；逐项匹配父胶囊，核验 96 个相位对易式。以 `z=exp(i omega t/2)` 为 Laurent 参数，分别从 `h0` 与 `H_original` 的实际谱生成指数，得到通式 `U_original=P U_co`。原 `omega=18 sqrt(15)/125` 未换标尺。精确结果见 [independent-receipt.json](independent-receipt.json)。

- 实际 A01 时间通道在三个独立非平凡时间相位下，原准备的 Kubo 核等于共转核，非零值为 `-29941632 sqrt(2) i/17850625`。
- 原时间超荷通道给出 `T=I`、`B=-sqrt(2)Q`。从原两条演化腿直接求得 `delta_original(t)=-i t P(t)w`，并核对原 Hamiltonian 方程、初值与范数；任意漏掉一条演化腿的相位都会改变积分核。
- 带电矩阵 S 的原 Heisenberg 算子确实改变。实际准备 w 的不同时间 CAR 测试给出 `i/4`，删掉该腿相位则为 `1/4`。仅改变准备、固定带电测试也会改变读数。另以原占据位 CAR 核对 585 个字的共同相位不变，保留全部中间 Fock 扇区。
- 独立 Lean 消费者从已认证真实有界球剖面和真实 native 力构造非零原强迫，并以实际交互导数证明其原时间积分不可能恒零。真实因果 L² 准备历史进一步生成某个 `tau>0`，使随后所有原时间的准备字段范数为 1 且满足上述总相位公式。原 Stage10 回读与不同时间 CAR 两腿公式也通过内核。

精确程序是独立矩阵与反控制证据；完整 L²、任意时间与任意有限 CAR 字的普遍性由 Lean 声明支付。此包签收一阶响应及相位输运；仿射 `Uu+epsilon delta` 的有限 epsilon 幺正流没有被预支，恒等强迫的精确反控制给出范数平方 `1+epsilon² t²`。

审计只新增本 `audit/` 的文件；未修改冻结候选、生产源码、active route 或 Git 索引，未提交。临时消费者模块原样复用先前认证夹具，其编译产物在临时目录结束时删除。`git diff --check` 通过。

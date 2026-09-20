# 联合独立认证：原空间对偶弱式与 Stage10 准备读回

Verdict: **certified**。`DualPairing / DualWeak / DualField / PreparationNative` 四个冻结候选无声明或来源缺陷，可整体晋升。

本次只新增本目录证据；未修改候选、根文档或提交。Native 消费最终正式 Preparation3 与本次 DualPairing；其证明正文未改。

## 严格验收与真实终端消费者

四文件 fresh 默认预算 `--trust=0 / warningAsError` 全部 EXIT 0。Dual3 的 18 个、新 Native 的 16 个公开口，以及 Native 原带的 2 个消费者均为标准三公理。

独立 `Consumer.lean` 另外生成三个完整消费者，并原样重编译此前认证的 19 个实规范控制构造。总计 58 个公开／消费声明的公理集合均包含于 `propext / Classical.choice / Quot.sound`。

其中 `actual_native_stage10_unit` 不再保留一个任意非零 force 的调用者前提。它实际消费此前从原时间 hypercharge、实值零过去斜坡和单位球 L² 剖面生成的原规范历史，证明

**存在 t>0，使原 `tick.answer(0)` 对同一归一 preparationNative 的 responseMatrix 读数等于 1。**

另两个独立消费者把同一个 `gaugePreparationMap`、同一个 sourcePrepared 和原 `spinScale` 直接交给完整外幂 canonical-dual 弱积分式及其 raw dual 可积性定理。

`verify_consumers.py` 从已认证的 `preparation/audit/Consumer.lean` 原样建立临时支持模块并严格编译；不会把构建产物写入仓库。重放命令为 `python3 .../dual/audit/verify_consumers.py --root .`。对应日志与命令结果在 `consumer-focused.json`、`support-strict.log`、`consumer-strict.log`。

## 完整原配对，没有换 Gram 或换 dual

`DualPairing.triplet_internal_pair` 从原 Λ⁶⊕Λ²⊕Λ⁴ 的完整外幂基配对计算 triplet 槽；`triplet_coordinate_pair / triplet_euclidean_pair` 由此生成完整坐标 Gram。没有要求调用者提供等距或目标 Gram 证书。

随后直接消费原 `fullCanonicalDiracAdjoint`、原 spin exchange 和 Kinetic 密度接口，得到三个不同的对象：

`coordinatePair(lift u,lift v)=〈u,v〉`，

`fullCanonicalDiracAdjoint(lift u)(lift v)=〈u,Sv〉`，

`kineticPair(s,lift u,lift v)=s〈u,Qv〉`。

这里 `S=γ0γ5`、`Q=γ5` 在原 triplet 上。独立完整 252 维矩阵检查验证三个 restriction；也检查完整 FullPhase 的 graded charge 与完整 kinetic gamma5 在 Λ⁶ 上不同，而在本 triplet 上相同。没有从这个 restriction 推出全载体的错误相等。

原单位准备 w 满足 `〈w,w〉=〈w,Sw〉=1`，但 `〈w,Qw〉=0`；一个上手征单位坐标的 Q 自配对为 −1。另一个跨手征坐标例中普通 Gram 为 0、S 配对为 1。因此本包没有把动能配对或 canonical 对偶误称为欧氏正内积。

## 原偏导相容与 −iN

`charge_differential` 实际消费原 Fourier 乘子和已支付的 `[h(k),Q]=0`，借助 Schwartz Fourier 的单射性生成 `D_H(Q test)=Q D_H(test)`。它没有把原 Dirac gamma 单项错误地当作与 Q 对易。

`duhamel_dual_weak` 共轭真实 primal 弱方程并使用该相容性；由于左参数共轭线性，其 Hamiltonian 项为 `+i s〈u,QD_H test〉`。密度参数明确为实数，实际消费者取原 `spinScale`。

`DualField` 再消费原 `D_H=Nγ0D_original` 及原 gamma 代数

`Q(Nγ0)=−NS`，

得到完整原 dual 的 **`−iN`** 系数。独立符号矩阵计算对三个自由空间导数系数同时验证此式。非零 Gaussian 测试进一步给出原 dual 积分

`−3√2 π^(3/2)/5`，

对应弱式 Hamiltonian 项为 `18√15 i π^(3/2)/125`；将 `−iN` 改成 `+iN` 不成立。

所有积分都有实际可积性责任：普通项由两个 L² 向量的内积可积性与有界 Q 生成；Schwartz 偏导仍为 L²；raw fullCanonicalDiracAdjoint 项从同一加权可积函数恢复，并使用原 `lapse_pos` 排除 N=0。没有依赖 Bochner 积分对不可积函数的默认零值来制造弱式。

这支付的是原制备相容 canonical-dual 响应图。任意 independent-dual 字段及其 current 仍由正式 GaugeCurrent 保留；没有将独立变量域重定义为该图。

## 准备向量到原 Stage10 原生读数

`original_prepared_triplet` 同时消费原 `actual.matter(0)=2 embed(w)` 和原 `FullPairing.actual_eq_twice_prepared`，确定原 FullPairing.prepared(0) 正是该 w 的自然完整坐标。`tripletFiberLift_pair` 使用刚生成的完整 Gram，未重新选择制备或坐标内积。

`nativeMother` 用原 triplet lift/read 的真实左逆生成完整 252 维母算子。对空间算子 A，候选先形成完整 `K† A K`，再生成这个母算子，最后才调用原 `Compatibility.responseMatrix` 和原 `Stage10.Runtime.tick.answer 0`。

审计沿 `FullPairing.source_gram` 继续追到原 `Stage10.Recovery...quantumClosure.sourceResponse`：原 independent dual 经 `pairedMother` 的一次 spin flip 补偿，完整 adjoint 组合后才读取旧八维坐标。这不是另造一个名字相同的 response 函数。

由此，

`原 sourceResponse(preparationNative(A)) = 〈Kw,A Kw〉`，

`原 actual.conjugateMatter(0) 的读数 = 4 spinScale × spatialResponse(A)`。

归一版本使用实际生成的 `‖Kw‖⁻²` 缩放同一完整组合，恰好回到同一个 normalizedFunctional。原 source 在固定原点读取被拉回的完整观测；准备时间 t 仍位于 K 的真实历史中，并未替换原 runtime 或实际时间坐标。

## 组合顺序反控制

独立程序按原 `responseMatrix(M)=S8 E8† M E8`、原 full spin swap 和原 w 显式计算最终读数，验证 Native 全组合读回及 `4 spinScale` 幅度因子。

此外在同一真实 triplet 和原 w 上进行两个精确代数反控制：

- 一个颜色方向先送出旧两颜色子空间再返回。完整乘积读数为 **1/2**，中间先作旧八维压缩再相乘得到 **0**。
- 对普通准备拉回，拉回完整乘积的读数为 **2**，把两个分别拉回的算子相乘则为 **8**。

第二项是拉回代数的反控制，不声称该有限测试 K 就是某个指定规范历史的 Duhamel 值。它确认不能凭当前定义增添乘法同态结论。候选仅要求先在完整空间组成 A，再一次性计算 `K†AK`，没有偷渡中间压缩的多点等价。

## 证据与固定来源

`focused.json`、候选及原消费者 strict 日志、`trust-summary.json` 保存全部精确范围；`independent_check.py`、`independent-check.log`、`independent-receipt.json` 保存完整配对、号数与组合顺序反控制。

原 `positiveSmoothUnifiedSource`、修复后的 Dirac-dual 母作用、SpinPair、Stage10 root/current/next 保持不变。新增签收为：同一原控制准备的空间响应满足原 canonical-dual 弱积分式，并由原 Stage10 sourceResponse 完整读回；空间真空或量子圈测度未被加入这些定义。

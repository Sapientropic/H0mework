# 独立认证：源准备的空间 CAR 全词与原 Stage10 读回

Verdict: **certified**。冻结的 `SpatialCARAlgebra / Words / Span / Adjoint / State / Native` 六模块无声明或来源缺陷。

本次仅新增本目录证据，未修改候选、根文档或提交。

## 严格机器证据

- 六候选 fresh 默认预算 `--trust=0 / warningAsError` 全部 EXIT 0。
- 84 个公开口、原带 4 个消费者、独立 5 个消费者／构造及原样复验的 19 个 native 控制构造，共 112 个声明，公理集合均包含于 `propext / Classical.choice / Quot.sound`。
- 独立位占据算法与另一条 Gram 外积收缩算法比较了 1747 个完整 Fock 状态及读数，全部一致；真实载体扩张、伴随、正性与组合顺序反控制也全部通过。

`focused.json`、`consumer-focused.json`、strict 日志和 `trust-summary.json` 保存实际检查；`verify_consumers.py` 仅在临时目录原样编译此前已签收的 real native 控制支持模块，随后删除构建产物。

## 共同载体由实际测试生成

`carrier` 是实际空间向量 `prepared` 与全部 `tests i` 的 span，`Modes` 是它的真实 finrank。准备向量通过 `family none` 明确进入同一载体；测试不要求正交、独立、互异或非零。

`stdOrthonormalBasis` 提供有限计算坐标，`coordinates_pair` 从其真实等距性读出**原空间内积**。随后 `spatial_car` 的标量是该内积；没有把任意测试误当正交模式并套用 Kronecker delta。

全部 oneParticle、creation、annihilation 仍调用原 `QuantizationCheck.Fermion.Fock` 及其算子。source_preparedFock_unit 消费原 K 生成的非零准备范数，未另给一个单位 Fock 状态。零准备的空词读数仍是 0，不被当作真空单位态。

## 全词递推没有中间投影

`wordOperator` 在完整有限 Fock 载体上组成全部乘积，右侧字先作用。`interpretation_word` 不只核对标量读数，而是证明 Gram 外积表达式解释成的**完整 Fock 向量**等于真实算子字作用。

创建在 exterior list 前端加入字段；湮灭由真实 CAR 生成交替符号收缩。只有整个字完成之后，`pairing_exteriorKet / expressionEvaluation` 才按原 oneParticle bra 读取终点。没有先删去真空、两粒子或更高占据的中间分量，没有输入 Wick 规则或目标全词响应。

`SpatialCARAdjoint` 的单模伴随证明用原 insert/erase 之间的真实双射重排全部占据基。波函数创建与湮灭正确处理复共轭，完整字伴随交换创建／湮灭并反转顺序。`allWord_positive` 再将每个 `W_i†W_j` 读数认回真实向量 `W_i|prepared>` 的 Gram，故正性由 Fock Hilbert 配对生成。

独立程序另从原源码的 occupied-mode parity 建立精确位算子，并与有序 exterior list 收缩计算交叉比较。它覆盖复数、非正交、重复和零测试，以及长度达到 9 的字；同时检查完整状态和最终读数，包含真空及两／三粒子分量。

## 所有字的扩张一致与源占据

`allWord_embedding_invariant` 的通用 Gram 条件在 `spatialMoment_embedding` 中由同一实际 E 的 inner 和 `sameTests` 支付。增加测试改变真实 span 和所选正交基，但全部旧字读数保持。

它还允许合并真实相同的测试标签；独立 Lean 消费者专门用 `Fin 2 → Fin 1` 的非单射映射验证所有字的重复标签合并。条件是实际测试相同，没有伪造两个不同字段的相等。

独立程序把原共同空间从维数 3 扩大到真实维数 5，并对旧向量使用不同的正交坐标。对应 Fock 空间由 8 扩到 32 维；1747 个旧字读数全部一致。新增的两个测试确实增加维数，非空的“扩张”不是原空间重新命名。

二点与四点直接作用于原 oneParticle 状态。`source_twoPoint_occupation` 和 `source_connected_fourPoint` 消费原 `preparedOccupation=|v_a><v_a|`，得到

`ω(c_i a_j)=〈f_j,P_a f_i〉`，

`ω(c_i a_j c_k a_l)−ω(c_i a_j)ω(c_k a_l)`

`=〈f_l,P_a f_i〉〈f_j,(I−P_a)f_k〉`。

独立检查支付 81 组四点、729 个完整伴随 Gram 字对及非零正二次型。P 来自同一个实际 K 和归一准备，未另供占据权重。

## 原 sourceResponse 在完整词之后读取

`testFockRead` 的 J 由实际共同载体的正交投影、真实正交坐标和原 oneParticle 映射构成。`testFockRead_family` 证明它对源准备与测试的准确作用。

候选先在完整 Fock 空间组成 W，再生成 `J†WJ`；随后才调用正式 PreparationNative 形成 `K†(J†WJ)K`、完整母算子和原 Stage10 responseMatrix。两次非乘法拉回均位于完整乘积之后。

独立反控制给出：

- 同一单位准备的完整 `c(v)a(v)` 读数为 **1**；若分别压回单粒子空间再相乘，读数为 **0**。
- 一个独立两粒子中间态的 `a(f)c(f)` 读数为 **34/25**，不是被截断的零。
- 非正交测试的 CAR 系数为 2；忽略其 Gram 得不到原恒等。
- 不反转伴随字顺序会改变完整算子。

这些反控制与源码中的真实组合顺序一致。`wordObservable` 没有被签成单个 letter 的乘法同态。

## 从真实规范历史到非空 CAR 原生响应

独立 `Consumer.lean` 原样复用已认证的原时间 hypercharge 通道、实值零过去斜坡与单位球 L² 控制。原规范力在时间 1 对 sourcePrepared 非零，原 Duhamel 非空定理因此给出某个正时间。

在这个同一时刻，测试取实际生成的归一空间准备 v。`real_native_history_original_CAR_response` 内核检查：

**原 Stage10 对完整 `c(v)a(v)` 的 sourceResponse 为 1，对反序 `a(v)c(v)` 为 0。**

该终端结论没有调用者提供的目标波包非零、单位态或目标读数前提，也不止验证空字。中间真空态保留，归一因子来自同一个 K，原 source 原点及实际时间参数保持。

## 精确责任

本包强签收任意有限 L² 测试族的真实 CAR 全词递推、伴随正性、所有旧字的扩张一致，以及源准备态的原 Stage10 完整读回。有限性是每次有限观测的实际共同载体，原空间传播仍在完整 L² 上。

它保持原 root/controller、Dirac-dual 作用、原 P/K 来源及时间相位；没有因此指定任意真空或 Feynman 圈测度。

mouth lint 除 `autoImplicit false` 外，将 `wave_empty` 标为零值口。这是创建算子的真空分量恒等，已由 `pairing_exteriorKet` 和全词解释直接消费；没有被提升成任何路线级 no-go。

其余证据见 `independent_check.py`、`independent-check.log`、`independent-receipt.json`、`Consumer.lean` 和对应严格日志。

# 完整发生恢复与仪器读口

## 同一源的完整观察和作用

[SourceHistory.lean](../../../../../../Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/SourceHistory.lean)
从原 `Runtime.visit = SpinPair.visit 10` 和 `Runtime.event.occurrence` 生成 `visitAt/currentAt/eventAt`。
既有 `ActualFormation.commonOccurrence` 保留整棵发生树；constructor 与完整九场由同一
`nativeAction/fullObservation` 生成的观察模型读回。没有新 actor、替代 root 或 caller 硬件参数。

完整 future Model 直接消费 `SourceGeneratedActionObservationHistory.model_fibre_iff`；
当拍／下一拍联合读口直接消费 `SourceGeneratedObservationAction.jointObservation/joint_fibre_iff`。
原 native points 的完整读口恢复 current、原 writer、whole-ledger 和全部 installed projections；
原 joint action 保留 incidence。完整场限制到 occupied field，再限制到两拍 Born，
严格交换到原 tick16／17。任意积分词的核按上述 fibre 定理保留，没有被宣布为零。

[独立消费者](SourceHistoryCertification.lean)与[首认证](source-history-certification-first.json)
核49项显式声明、66项safe模块声明、15个独立consumer及标准 Mathlib 三公理。
递归runtime辅助单列，安全声明与consumer的type/value均无引用。
认证范围为已登记同源发生的完整场和作用读口，不把公开 CSV 当成已输入的完整物理场。

## 已有公开字段的恢复

[hr0001.1](criterion-hr0001.1.md)于 `068b0a3db3` 冻结后，
两独立 parser 消费四个已准入 local CSV，不打开 pairs CSV、不重播统计。
全部 41,673 条本地记录的九字段与原行 SHA256 逐项恢复；867 条未配对记录保留。
原配对身份来自 mu0001.1 已付完整 join audit。

[首记录](history-first-hr0001.1.json)保存两套完整观察 commitment、原行 commitment 与访问计数；
完整记录在内存中交给 observer，raw archive 不进入 Git。
同薄读口、异时间戳／flag／comment／未配对行的控制被完整 observer 区分。
selection override 只改变已有配对视图，不能删除原记录；错误 parser owner 与不完整形似读口被拒绝。

Unix time 和 local timestamp 保持原字段单位与语义，记录顺序不定义物理作用。
`CEMs off`、`Maintenance` 保存为原注释；它们不自动指定点击编码或 active CEM 的效率。

## 三类信息责任

| 类别 | 已签事实与判定口 |
| --- | --- |
| 已有历史能显影的坐标 | 原 constructor／完整九场及其 actual next 已恢复；公开本地记录的全部字段已接入观察消费者 |
| 全部可用观察的真实残差 | 必须由同一实际作用与全部具名 observer 生成 `K∞=⋂ ker(o∘Aⁿ)`；静态 joint 纤维不承担该结论 |
| 尚未接通的字段语义 | 完整源场／实际控制作用到原子与 CEM 具名读口、记录到同一物理发生的 restriction square |

`hardware_parameter_uniqueness_certified=false` 表示实际唯一识别未获认证；
它不表示已证明完整历史无法恢复。id／fb／rf 的纤维保留各自静态 law／pulse-image 范围。

## 具名作用坐标与单位

既有 af0001 固定生成子的三个坐标直接反读原始速率。
令 `Lρ=−i[H,ρ]+jumps`，原态编号从1开始，`R=Ω12/ΓD1`、`C=Ω56/ΓD1`、
`Aion=Γion/ΓD1`：

```text
R    = 2 Im(L(E11))12 = 2 L32[4,0]
C    = 2 Im(L(E55))56 = 2 L32[30,27]
Aion =   Re(L(E22))33 =   L32[31,1]
τ    = ΓD1 (物理 pulse 结束 − 开始)
```

L32 下标从0开始；第三坐标是原态3，不与独立144实现的0起点 ion 下标2混淆。
三项不含其他 natural jump 贡献。两实现的四枚仿射基及完整32↔144限制共12,288项
纯 Fraction 系数核验通过，没有数值传播或记录读取。
`Aion` 是电离率，区别于 Rabi 面积 `∫Ω12dt`；物理角频率由以上速率乘 ΓD1 得到。

完整场生成的 coherent insertion 可消费已有
[pulse_derivative](../../../../../../Lean/SaturationMonoid/PhysicsCore/YangMills/SourceQuantum/Insertion/Action.lean)
与 [sourceInsertionMatrix](../../../../../../Lean/SaturationMonoid/PhysicsCore/LowEnergy/FockDynamics/Pulse.lean)。
其中场方向 η 是 gauge one-form；幺正插入不能代付电离 jump 或探测器效率。
同一 CEM 通道若生成无片段／有片段两枚响应 c0、c1，则固定反读为
`d=c0`、`η=(c1−c0)/(1−c0)`，沿原 detector 合法域消费。
这些式子指定已登记af模型内的作用坐标，不把完整目标生成子、目标参数或恢复能力作为输入。

## 完整空间与粗化读口

原252维是内部matter坐标；完整空间载体为 `L²(ℝ³;252-mode)`。
已有 `LowEnergy.FullQuantum.FullSpace.spatialFlow` 生成原空间作用，
`HistoryGenerator.hamiltonianSchwartz_actual` 认回既有 `freeAction` 的空间偏导Hamiltonian，
不把它扩大为完整interaction flow的生成子；
`HistoryPrepared.sourceMother_read` 在完整作用之后通过 `preparation†·A·preparation`
返读原tick.answer／responseMatrix。这条共同载体不用外领Hamiltonian或任意12态embedding。
现成的12维spin×color压缩另有自己的原生语义，同维不能代付Rb状态身份。

af的state5／6聚合F2／F′3子态，state3表示ion continuum。
因此“十二枚literal rank-one束缚态投影＋闭合Markov生成子”不是该模型的准确接口。
具名仪器coarsening及其control／环境作用必须从同一完整源生成；
粗化后不闭合的差额由既有actionDefect、joint fibre与完整future Model保留。
不要求caller补零残差、invariant projector或完整af生成子作为准入前提。
完整空间返读使用的preparedPacket是源向量的固定归一unit-ball表示，不冒认实际Rb束缚态。

## 原控制的后继时钟观察

[原公开协议](https://arxiv.org/html/1611.04604v2) SI I.B规定按40 ms光子积分判定trap中的原子存在，
检测到损失时重载对应trap，再由双trap就绪及excitation／cooling重试产生下一成功BSM。
I.E规定每个成功BSM后的CEM结果记录在本地。因此后继记录的clock可联消当前pointer与
measurement后的presence／reload作用，而非只读取同一静态概率。

生成链须保存测后原子／光子状态、presence观察、对应loading或继续分支、
两trap同步就绪、BSM停止事件与storage write。公开端提供当前及后继原记录的Unix-ms、
setting／result、flag／comment和完整地址；local timestamp保留原随机数身份。
后继记录表示这段控制历史的停止事件，不等同于CSV下一行定义物理nativeAction。

长BSM等待、另一侧重载、环境损失和维护都能改变gap；典型2–3秒加载时间不是严格support界。
无click＋同一gap可来自漏检电离后重载，也可来自存活后的较长BSM等待。
时间联合观察应由原作用计算fibre，不能逐事件把gap直接标为电离，
也不能把配对窗±100ms当统一clock误差界或把Unix gap当pulse宽度。

### 已接入的时间观察

[cl0001](criterion-cl0001.md)在 `f311c0aded` 冻结后消费原档案，
[首表](clock-first-cl0001.json)由两套实现逐项交叉。
41,673条原记录的current→nextRaw地址、完整两端context与精确Unix-ms差值保留：
41,603正差、66同时间、4末行删失；320个local分组全部守恒。
20,403枚原pairs按已付唯一offset与原地址联接，生成64个完整 `(h,a,b,x,y)` cell；
每cell保两侧各自13个固定CDF计数及status，不从membership排序猜配对。
这份计数表不保存两侧clock的二维joint；有序双clock观察的commitment仍保留。

[只读clock消费者](clock_verify.py)联消原hr恢复证书、冻结源码、attempt和首表，
核原source/root/tick、全部count/status/CDF守恒与字典。
readiness沿原history开关消费这枚子结果；clock回执缺失不撤销已签原记录恢复。
6项观察控制、3项intake控制及6项history/readiness控制通过。
样本矩阵的秩和累计计数不充当population law、物理loss标签或实际效率。

### 原仪器作用的接点

`MatterSpace.controlledPreparationMap` 已从时空control profile生成Duhamel preparation；
`SpatialCAR.wordObservable/source_twoPoint_occupation` 已从同一空间载体生成CAR占据响应，
四点响应保存其connected部分。这些现成producer承担场作用与占据观察；
实际trap test mode、control profile及presence comparator须由原发生的字段生成，
不能用任意外领profile、已完成clock kernel或目标效率替代。

具体接点为原 `SourceHistory.fieldAt 0`：`matter 0` 经 `tripletFiberRead` 认回原triplet seed；
coframe／gaugeConnection经holonomic variation与 `gaugeCoefficient` 生成control coefficient。
尚未接通的是实际局域control profile的 `ℝ → Lp(Position, ControlFiber, 2)` 类型及其连续性，
和actual trap/APD mode的源限制。pointwise gauge field不能无证改成L² profile；
原12维triplet不改称Rb12。`source_connected_fourPoint` 已提供原CAR coupling residual，
因此后继消费者不需要输入零耦合。CAR占据期望也不改称40ms实际光子计数或presence comparator。

下一消费者读取原ion／CEM receipt、presence／条件reload、双trap就绪与成功BSM停止事件
生成的joint moment programme。共享control–clock分解及其真实coupling residual由该programme产生。
谱块内逆读使用observed law生成的矩阵束和归一因子；不输入已知loading kernel或响应锚。
两个herald、固定setting下的样本计数不能自行支付CEM receipt与future clock的条件分离。
actual停止事件到Unix writer字段的同发生square仍由该仪器作用支付。

## 消费

[只读验收](history_verify.py)联消完整源恢复首认证与公开记录首回执，
不读取 archive、重编译 Lean 或执行统计。[readiness](../../nist-real/readiness.py)
分别登记两端已闭合、actual field/control/record 语义桥未签和全历史不可恢复未签。

8项记录观察控制及4项readiness控制通过；正例、回执位置override、disable及形似错误来源／
强行提升硬件身份／全历史不可恢复的回执均按各自合同验收。

```sh
python3 history_verify.py --check-only
python3 clock_verify.py --check-only
python3 ../../nist-real/readiness.py --munich-history-only --output <新回执路径>
```

实时责任只见[唯一 active route](../../nist-real/nominal-replay/investigation/README.md)。

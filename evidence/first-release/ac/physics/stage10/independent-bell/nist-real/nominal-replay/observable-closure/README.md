# 公开观测消元与共同留出预言

公开Table S-II足以生成一个不依赖Klyshko、visibility、泵κ或新实测的光学源域。
四single消去源方向和损耗比，joint00生成相位；joint11的原统计域限定剩余标量损耗。
整个合法域的01/10共同预言由Gaussian与相干Fock两路径独立验收。

## 源生成机制

[ef0001](criterion.md)使用两个完整训练格的六个精确计数中心。
源族是两偏振TMSV、V-number phase-before共同实R、未知scalar losses、N5 fresh pulses与独立OR背景。
四single生成scaled source；两joint消去相位后只剩至多二次方程。
全部实根保留，留出不参与选根。两实现都得到一个效率超域根与一个coherence>1根，
所以没有合法精确中心成员。它不拒绝有限计数统计域中的整个源族。

[ef0002](criterion-ef0002.md)固定四single与joint00的五个中心，
将计数106的joint11放回原po0003 CI。对所有e=ηA∈(0,min(1,r)]，
四次phase不等式及两个二次训练不等式生成整个具名一维slice。
这是一维子域，不将五个中心视为实际真概率，也不冒称完整六维统计fiber。

两套cover各有69段：32段完整合法、35段排除、2段边界；68次分割，无cap。
两边界都留在预言外包，整个partition无缺段/重复段。
合法域outer为ηA∈[.7411896212237604,.7414274323892578]；端点附近仍标记boundary。
规范成员固定取首inside段的有理midpoint，不读取留出再选点。
它生成ηB≈.76465288593、λ≈.00409579367；这些是研究源参数，没有历史装置身份。

## 公开数据结果

两规范成员全部12项数学概率包络进入原CI；整个slice的两格预言包络也进入留出CI。
原alpha=.05、ε=.003、6runs×32767slot masks×16features×40固定界保持。
原共同N是冻结design exposure，训练选择不使用留出outcome分配。

| 留出量 | 全slice joint预言外包 | 原共同CI |
| --- | --- | --- |
| 01 | [.00015821397237, .00015855716089] | [.00014007684343, .00016712361974] |
| 10 | [.00015026944774, .00015053199993] | [.00013338547700, .00015991470701] |

两个格共同消费同一个e/相位/source，每格完整(++,+0,0+,00)保留；不拼合各格不同源。
逐分量hull用于显示，共同配对区域保存在首回执。
这是已暴露公开数据上的具名conditional-stationary源族相容性，
不是盲态验证、实际装置最优点复现或对一般漂移历史的非线性源反演。

## 内核与独立消费者

[ObservableClosure](ObservableClosure.lean)从物理Snapshot生成两phase严格正分母、
H=(1−2λ)gT、实际e二次共根与必要Sylvester零行列式；
[ClosureConsumer](ClosureConsumer.lean)直接消费共根生成全部cell的N5 OR配方。
必要resultant不作为合法源存在的充分条件。

[ScalarFiber](ScalarFiber.lean)从scaled source、合法自由e、观测seed和计算phase平方不等式
生成合法Snapshot/λ，在证明内部读回seed；
[直接consumer](ScalarFiberConsumer.lean)生成e不变means、全部同源窗口配方。
没有调用者提供的source endpoint或seed-readback等式。

[ef1证书](certification.json)357声明、四文件fresh trust0/werror与LSP通过；
[ef2证书](scalar-certification.json)440声明、六文件strict/LSP通过，均仅标准三公理。
这些是具名Gaussian law的代数源生成；新Born/vacuum身份、outcome非负分布和统计覆盖不扩大kernel范围。

[主slice](slice.py)使用有理Bernstein外包；[独立slice](independent_slice.py)用自有ratio inverse、
formal三点系数与Taylor/Horner cover，规范成员从相干Γ/Fock前缀6加原质量尾生成。
两科学首回执形成后才互读。
[独立交叉](cross-receipt.json)仅取主规范有理e，独立恢复源并核14源字段、12概率和16outcomes。
外国源字段及概率只作比较，不进入forward。

[最终验收](verification.json)重算两完整partition所有界、核来源与两证书，并消费21项focused controls。
heldout outcome/CI修改、joint11中心改变、非法source、丢段/重段/丢boundary、cap override均被核对。

## 冻结与复现

ef1合同先冻`fde5c14df3`；其两个首回执及数学稳定根修复分别保存，不覆盖原输出。
ef2合同先冻`e71683e0bf`，主/独程序先冻`1237ff2f0d`/`b1c13957ed`；
首结果冻`987866979a`/`a2816a7226`。独立交叉先冻`e5eee922ce`，回执冻`87c5feff64`。
source候选先冻`d95c4ff3f0`/`0d34a2a0e6`；独立审计最后先冻`e4d2d9d4e7`/`d800862d4f`。
验收器先冻`5738ae56ef`，验收回执冻`df904aa027`。

从本目录执行，输出使用新本地路径：

```bash
python3 tests.py
python3 slice_tests.py
python3 verify_slice.py --output /tmp/p23-ef2-verification-new.json
```

当前责任由[唯一active card](../investigation/README.md)维护。
历史五控制最优带及原readiness判决由[名义重放入口](../README.md)维护。

## 固定源的接收更新

[rx0001](receiver-criterion.md)保持整个源slice不变，消费四个公开角各±.05°舍入盒，
生成两站共同rotation及原mirror优化坐标的有限更新。更新接收角时不重新校准R/λ/K。
主角jet及独立phase-branch显式导数分别以全域Hessian中值界收紧包络；源、域和候选规则不变。
两首宽包络未认证结果保存；数学收紧均先冻结，改进结果不冒称新的盲态科学首算。

两路径都按原固定顺序生成Bob两角共同−.01°的更新：
`(a0,a1,b0,b1)=(4.2,−25.9,−4.21,25.89)°`。
整个34段源域及舍入盒的CH改善下界分别为`1.9913741453e−9`与`1.6985173040e−9`，
均超过原`1e−10`数值容差；规范源独立Fock端点改善约`3.8492559897e−9`。
mirror0/mirror1也有严格改善，共同Alice方向未认证，不删失败方向。

[接收验收](receiver-verification.json)重新计算主规范更新的全部34段Hessian界，
独立重生源及Fock端点，并核四个exact polynomial/reciprocal/trig方向控制。
这是具名源族中的有效projection更新；没有新增Born/derivative内核或实际硬件输入身份。
固定泵κ/circle/ellipse无法消去这项同源接收改善，历史最优性仍要求设计源与效果/epoch对齐。

公开[主文Fig.1](https://arxiv.org/pdf/1511.03189v2#page=3)已给名义pump方向
`cos16°H+sin16°V`，不能再把公开Drive方向写成完全缺失。
[SI §IV.A](https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.115.250402/LHFSupplementary.pdf#page=13)
把XOR3绑定主文数据并记录此前realignment；它未给逐run泵角/功率误差或设计optimizer epoch。
16°可支付具名nominal reference drive及条件κeff/ellipse，不能自动赋予逐run实测输入身份。

# 公开泵与接收控制配方

本目录保存NIST公开DAQ源码的脱敏节选和来源绑定。节选为不可执行文本；原件哈希、成员名和行号由
[sources.json](sources.json)登记。原配方在模块顶层连接硬件，不能作为纯数学库导入。
该来源由公开代码、配置与文献组成，不授予实验执行、校准计数或事件日志的身份。

## 一手来源与名义身份

[NIST code目录](https://www.nist.gov/pml/applied-physics-division/bell-test-research-software-and-data/repository-bell-test-research-0)
直接提供[bell_client.zip](https://s3.amazonaws.com/nist-belltestdata/belldata/code/daq/bell_client.zip)与
[bell_server.zip](https://s3.amazonaws.com/nist-belltestdata/belldata/code/daq/bell_server.zip)。
client为80156字节，SHA256 `2ab050486473caf71a7b991a6598ef8a139d92e52d738b5a26ac5870e59c28d7`；
server为17507字节，SHA256 `858c7bfdb2eaabdb4dec5ecd12a7f974428d5fe2c846634a4e1ff52b36c348c7`。
原[NIST来源与使用说明](https://www.nist.gov/pml/applied-physics-division/bell-test-research-software-and-data)给出通知与许可；
完整通知及Product Disclaimer保存在[NIST_NOTICE.txt](NIST_NOTICE.txt)。本节选在2026-10-02将网络端点、
设备标识、私有路径和时钟标识脱敏；保留原成员哈希、行号和物理控制规则。
两包没有单独README或LICENSE成员；相关Python头部登记2015年7–8月创建、`qittlab`作者，ZIP修改日期
为2015年12月。源码或ZIP日期不替代实验执行时间。

[arXiv v1](https://arxiv.org/pdf/1511.03189v1#page=3)、
[v2](https://arxiv.org/pdf/1511.03189v2#page=3)和
[APS正式版](https://journals.aps.org/prl/pdf/10.1103/PhysRevLett.115.250402#page=3)的Fig.1都把BD1之后
泵方向写为`cos16°|H1⟩+sin16°|V2⟩`，并将两路径重组合的产物指向同一Eq.(2)。
两版arXiv源文件的Fig.1说明在空白归一化后相同。该名义制备方向已有公开来源。

四个CH脚本还明确执行`mc_source.goto('PumpHWP',8.0)`，与泵HWP半角约定相接。
`SOURCE_PUBLIC_DRIVE_BOUND`由论文制备说明与硬件命令共同支付；代码命令不是XOR3执行日志。

## 可直接消费的源规则

| 规则 | 原成员与行号 | 身份 |
|---|---|---|
| PumpHWP=8°；设置两站三片波片 | CH_over_network.py 194–212；另外三个CH脚本同值 | 公开名义控制配方 |
| Alice HWP2=5.5°、QWP=11°；Bob HWP2=−8°、QWP=−16°+90° | CH_over_network.py 194–212 | 接收控制坐标；不添加到公布有效角 |
| Alice HWP1=offset−Angles，Bob HWP1=offset+Angles，Angles含有效角半值 | 同文件200–202 | 机械命令到有效测量角的具名接口 |
| motor绝对移动消费command+configured zero；位置读回减去同zero | RotationController.py 15–22 | 校准坐标往返规则 |
| motor_server读取motorConfig.yaml | motor_server.py 18–24、43–50 | 实际zero的输入角色 |
| 选择纯V/H路径及匹配分析器、balanced DA/AA制备 | motorScriptExample.py 50–89 | 偏振标定配方 |
| visibility=(high−low)/(high+low) | motorScriptExample.py 47–48 | 已取得计数的可见度读回 |
| 波片扫描保存theta/singles/coinc，并读二次式极值 | sweep_wp.py 25–68 | 对准观察与更新配方 |

在(H,V)单光子坐标中，取`H(t)=[[cos2t,sin2t],[sin2t,−cos2t]]`、
`Q(q)=(I−iH(q))/sqrt2`、最终V端口。PCoff时，`H(o)eV`是`Q(2o)`的本征向量，
因而`H(m)Q†(2o)H(o)eV`与`(sin[2(o−m)],cos[2(o−m)])`只差整体相位。
Bob的QWP再转90°改变这个整体相位，不改变投影。因此有效角为`2(offset−HWP1_command)`。
配方中的两组命令分别读回Alice正/负、Bob负/正的有效角。印刷4.19°/25.93°是源配方的输入，
不作为新优化目标或拟合条件。

PCon的完整Jones口另需PC本征轴与retardance。`rotateToFindPCTheta`与相伴波片函数给出对准程序，
没有在这些包中给出具名数值轴或电压到retardance的标定读回。`motorConfigExample.yaml`是通用
示例；被加载的`motorConfig.yaml`不是这两包的成员。实际zero不得从示例、目标角或字段名猜出。

`switch_path(1)`设置PumpHWP45°及有效V分析；`switch_path(2)`设置PumpHWP0°及有效H分析。
DA/AA设置PumpHWP22.5°与相应分析器。它们支付纯路径/平衡制备的操作顺序；匹配Born口仍须消费
对应PC状态与时间窗，不能只从函数标签取得资格。

## 计数、目标与归一化

`get_pockel_on_off_counts`输出`SAxy/SBxy/Cxy/SETxy`。`get_ch_two_pockels`的行序是
`00,10,01,11`；`get_ch_waveplates`的循环行序是`00,01,10,11`。
CH_over_network的PC路径以各`SETxy`作分母，`meanTrials=1`；log2版保留原计数及各setting曝光。
waveplate路径按固定时长采集，曝光采用脚本中的`INT_TIME*79e6`或`INT_TIME*80e6`，不是独立取得的
最终run曝光常量。

`calc_ch`同时返回原coin-sum减去两侧平均singles，以及coin-sum/singles。
`calculate_poissonian_uncertainty`另读计数和曝光、返回raw CH及normalized读数。
这两处的single行选择分别对应不同的行序；消费者必须先绑定branch和setting角色。
CH_over_network的normalized返回式还有缺括号的源码表达式，节选保留原样。
这些源码读回没有执行优化、p-value或从公布五参数生成argmax的算法，不能自动决定原仿真的目标。

`cmdline2.update`的`alice_eff`为`C/S_A`，`bob_eff`为`C/S_B`；
`coin_plot`则将`eta1=C/S_B`、`eta2=C/S_A`明确列出。它们是反向herald读回，物理透射身份按分母和
trigger/partner角色认回，不能按字段名赋值。`coin2`使用两侧本地single时间窗。

`singlesCalc`在激光周期内选取严格`peak−radius < tag < peak+radius`的记录；
`pockel_bool_calcs`再对PC slot/setting筛选后的detector记录求和。该路径没有把一个完整sync trial
内的所有click合并成any-click。SI Table S-II的N5 trial-OR与这份预备计数读回不能直接互换。
`client.yaml`提供具名时间窗角色，包含重复abDelay及参考光电二极管变化注释；这些默认值没有逐run
来源绑定，不能整份作为XOR3最终快照。

## 名义门禁与实际记录

原名义门禁消费公开design输入生成模型最优值。必须识别的是source/collector/channel、
Klyshko与raw loss的同物理量映射、total-pair与HH标定强度、最大态visibility到非最大态的噪声规则、
有效端口/角、count/perpulse/window读出及目标函数。以已公布pair率作输入时，绝对泵功率和实际
run时间不是这个数值重放的额外前提。

DAQ源码已提供泵与波片控制、纯路径标定、herald方向和计数接口。它不提供光学噪声密度矩阵、
最大态可见度到最终源的唯一channel公式，或这些校准输出进入原optimizer的已发生记录。
已有作者Appendix A提供Hamiltonian/bucket/dark的模型入口；其模型与DAQ控制/计数角色应直接相接，
不能以相容源slice或选择最容易通过的解释替代这项来源责任。

[SI §IV.A p13](https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.115.250402/LHFSupplementary.pdf#page=13)
将XOR3指为主文数据，Table S-II p16再次绑定N5统计。再对准被写成system realigned；
[官方文件说明p2](https://www.nist.gov/document/bell-test-data-file-folder-descriptions#page=2)同样泛指
realigned，并提及计算机整理，没有指定仅PC或泵改变。它们既不撤销名义16°，也不生成逐run硬件日志。

官方文件说明p1列出探测/RNG/GPS/sync通道，p4列出HDF5时窗/同步元数据，p5列出diagnostic统计。
[DataProcessingDescription](https://s3.amazonaws.com/nist-belltestdata/belldata/code/analysis/DataProcessingDescription.pdf)
支付分析顺序和setting异常处置；这些是事件分析的角色。小型DAQ服务器写入timetag/transfer/GPS，
所检查的写入函数不写motor位置或源校准快照。对未检查的大型analysis包和其他附件不作不存在断言。

`ACTUAL_XOR3_EXECUTION_RECORD`与实际硬件资格保持未识别；它们不升级原名义design合同。

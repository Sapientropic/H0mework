# RHA0037：同一 Gaussian 源的正向／反向右作用算子银行

原 source／SpinPair.visit10／row0／whole-ledger／tick16→17保持。
当前已核自由TP银行与登记强迫仍保原范围。本合同从同一 GaussianAtomicPulseSource
生成完整33态无跳跃传播器，供原登记作用的正时间有序子仪器消费。
不读实验档案，不重求 Ready／pump／retarded inlet，不以算子银行代付登记积分或实际成员。

## 两个同源作用读口

原物理 `K(t)=-iH(t)-R/2` 满足 `K+K†+R=0`，R为原完整非负自然loss。
正向 `G(t,a)` 由I在a生成。反向右作用取 `B(u)=G(b,b-u)`，
`B'=B K(b-u), B(0)=I`；转置后是 `W'=K(b-u)^T W`。
转置保原loss恒等式和算子收缩；它是同一物理传播器的时间读口，不求逆传播器。
Gaussian反射使用 `(b-u-c)^2=(u-(b-c))^2`，原sigma、峰值、相位、H与全部R保持。

完整算子包含D1旁观块。原D1与其他块无静态或激发耦合，其原H首个D1对角值生成
精确D1相位坐标；D2保原excitation carrier。两者都保完整坐标并在physical读口恢复。
增加纯虚对角frame不改loss恒等式；不能将旁观块删除或将光学频率留给普通多项式步进。

令原detector门为[g0,g1]、m=(g0+g1)/2。两侧各生成三枚完整曲线：

- early_forward：原local(g0)至local(m)的正向G；
- early_reverse_right：同一段的反向右作用G(m,t)，候选坐标转置；
- late_forward：原local(m)至local(g1)的正向G。

原双时间传播通过 `G(t2,t1)=G(t2,m)G(m,t1)` 进入矩形
`g0<=t1<=m<=t2<=g1`。以后由原完整port、resolved environment group及Mark target生成
两次登记积分；两臂相干项、同臂重复发射和持续Gaussian均须保留。
当前银行不假设每臂恰发一个光子，不声称已生成该积分。

## 数值提案与独立残差

每枚曲线从完整33态I生成，系数允许非Hermitian；不得投影成密度矩阵。
固定degree64、1ns片、Taylor40、最大1/16ns步、96-bit量子系数、192-bit源列与价格。
实际提案要求至少64-bit mantissa；Mac的53-bit只在合成控制中显式override。
相对有理clock与扩展算术复用RHA0032.2。物理frame保持精确；单点frame评价误差另付。

整数checker在原Chebyshev基计算完整K残差、全部拼接、原Gaussian余项、source列舍入与
数学Gamma族价格。独立有理路径直接从原H/R/raising重建作用，并核每条曲线的首／中／末片；
端点须精确同值，价格差须不超过2^-80。原有限基列审查直接复用，不转单项式量子曲线。
完整uniform及endpoint算子误差均须不超过10^-8；任一超限照实记录。
旧inlet误差不进入算子银行，后继完整CP子仪器按其来源收缩一次。

数学、source／checker／proposal／bank、测试先commit，再生成实际源handoff与曲线。
六枚source和side／role完整覆盖必须保持；default early_forward、显式coflow override、
全33复杂矩阵单位、旁观frame、非Hermitian曲线、源篡改与错误方向反控均验收。
ComputeNode复用同一任务state和锁定环境，六枚输出路径各自唯一，失败不重投同id。
首结果、超限或失败attempt均保留；不读ETH或publish，不push、发布或外联。

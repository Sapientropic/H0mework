# RHA0032.2：原完整自由流提案的相对时钟

RHA0032.1首条完整120ns曲线的严格新误差已核，预登记相对10^-8门未过。
原完整source、已付retarded factor、物理时间区间、旧入口E、Chebyshev degree64、
1ns片段、Taylor40及数学残差消费者保持；不调整物理参数或验收阈值。

此修订改变不可信数值producer。Taylor时间游标、片段边界与Lobatto目标使用有理相对时间，
只在实际数值作用时转为NumPy longdouble；不以两个绝对浮点时间相减生成局部坐标。
Gaussian数值采样、复数系数、DCT及量化同用longdouble／clongdouble。DCT的数值pi只用于
拟合，不替换原source的pi、Hamiltonian或phase。执行环境实际mantissa位数进入回执。
完整量子系数仍按96位dyadic序列化，原source列和数学phase／Gaussian价格保持。

合成高频静态源在1ns与101ns起点的完整1ns曲线应逐系数相同；原浮点producer保留为
显式对照。非零Gaussian drive与曲线篡改反控仍由原完整残差拒绝或定价。
科学提交后才重新生成声明源的完整120ns曲线。沿用同一ComputeNode负载及锁定环境，
新producer使用独立单元ID，不重投旧单元、不覆盖旧输出。回收后由未修改的RHA0032.1
closed-source检查入口恢复原owner，核同一factor／source／clock并执行整数残差。
新回执分别绑定数值producer冻结和数学checker冻结，按原门记录通过或超限。

此项是完整登记层级的自由TP项，包含全部自然recycling；不等于无光子或无click分支。
一条局部自由曲线不支付完整登记instrument、实际raw成员或唯一硬件身份。
原root／row0／whole-ledger／tick16→17保持，不读ETH或publish，不push／发布／外联。

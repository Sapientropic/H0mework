# RHA0032.1：同一Chebyshev源残差的整数实现

RHA0032科学、原handoff和节点提案保持；曲线不重新生成。首批有理片段保留为独立基准。
此修订只改变检查算术，原 source／factor／时钟／相对10^-8验收和全部物理价格保持。

量子Chebyshev系数是mode_bits dyadic，已核原source列是coefficient_bits dyadic。
复乘、导数和quiet项在共同整数分母中精确计算，原片段duration的分母另乘入。
原完整H／R／Gaussian、33坐标、Hermitian条件、phase及Gamma价格均保留。

Gaussian scalar Chebyshev系数向最近coefficient_bits dyadic量化；全部差值加入原uniform
Gaussian余项，原2^-96小系数也只进入显式余项。source列原误差分别向上舍入到
coefficient_bits+32位，再按完整输入绝对值加权。两个新增价格均来自算术，不删物理项。
原复列作用与复整数作用在注册dyadic范围严格相等；独立basis整数核验与Lean统一界不变。

默认执行integer residual；显式`--rational`使用原RHA0032有理残差。两实现的数值余项
可能因新增保守量化有微小差别，不能要求价格逐字相等；源、端点与完整区间保持相同。
合成复数作用、同曲线双算术、显式override及形似source／非Hermitian反控先核验，
修订提交冻结后才执行真实完整曲线。旧有理prefix与所有冻结输出保持。

本项核同一已发行局部自由因子，不支付完整登记instrument、实际raw成员或唯一参数。
原source/root／row0／whole-ledger／tick16→17保持；不读档案、ETH或publish，不push／发布／外联。

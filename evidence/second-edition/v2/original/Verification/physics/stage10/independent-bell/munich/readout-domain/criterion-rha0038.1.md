# RHA0038.1：带价格的Hermitian效果投影

原source／SpinPair.visit10／row0／whole-ledger／tick16→17保持。
[RHA0038](criterion-rha0038.md)的物理源、数学、60片／160节点／297基列、双整数后端、
原晚段区间、Gamma／Gaussian价格及 `10^-10` 精度门全部保持。

初冻 `f010544031cba6b5c608e75f6a1c883d77e33813` 的首节点单元失败：
连续舍入的 `P^* R P` 中心不必严格Hermitian，原断言错误地把数值中心当作精确效果。
[首失败](late-adjoint-first-rha0038.json)及[源attempt](late-adjoint-attempt-rha0038.json)原样保存。
旧程序、已发行60片、原完整source program及自由中点不改；首单位未生成认证积分。

每片加权同臂效果中心M在输出前取 `(M+M^*)/2`，再按原96-bit整数格舍入。
中心与投影中心的完整entry范数距离明确加入numeric price，不能静默删除反Hermitian部分。
仅效果使用此投影；原非Hermitian传播器及相干升降算子保持。
非交换的96-bit矩阵控制以独立Fraction乘积核实际差额被总价覆盖。

新数值代码、控制及本合同先commit，再重发计算handoff。直接复用已核原source program、
60对曲线片和自由中点，复用前核原冻结绑定与独立raw-bath路径，不重生成原物理源。
修订后的每片仍按两个完整整数后端逐项核全部81920枚复数系数。
节点ID来自新handoff，所有输出路径带rha0038_1，不重投旧失败ID或覆盖旧输出。
旧入口E、source／Gamma和实际硬件身份按原合同消费；首次receipt与响应锚由原下游生成。

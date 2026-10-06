# ia0001：独立响应锚的完整硬件逆读

固定原source、visit10、material row及current16→17；本口是校准逆读consumer。
原完整joint置信域、所有统计预算与冻结输出保持，不执行新的经验拟合。

## 已生成的恢复能力

完整law已识别四bias与X/Z产品矩阵。每个矩阵各取一枚非零乘积作锚，
允许X/Z锚在不同setting；由产品比值生成本侧各setting的相对坐标。
两枚已知归一化XZ qubit probe及其signed响应构成两行系数：

```text
a_i = probe_x_i * X(setting_i,b_x)/X(a_x,b_x)
b_i = probe_z_i * Z(setting_i,b_z)/Z(a_z,b_z)
y_i = response_i - mu_A(setting_i)
det = a_0*b_1 - b_0*a_1
U = (y_0*b_1 - y_1*b_0)/det
Z = (a_0*y_1 - a_1*y_0)/det.
```

det非零时，U/Z由响应内部生成，两个signed尺度及其四符号分支均被恢复。
本侧坐标由相对比值乘U/Z生成，另一侧由产品除以U/Z生成。
全部四effect的合法性与原law、原probe响应由最终constructor核验。
两probe可以作用于不同setting，覆盖A0在坐标极点的情形。
probe制备坐标及响应须来自独立、同run／同setting的物理责任；Bell拟合点不代付该输入。

相反或共线probe若给出det=0，不签收唯一恢复。
非零响应误差区间按同一线性逆像形成带宽：U/Z每个外包是两个输入区间的exact仿射投影，
不把区间替换成精确点。固定law的逆读不自动成为真实经验概率的精确识别。

## 不额外测量的前向锚机制

独立原始脉冲λ若自产两个合法原子电离effect J_i，且同侧共用背景d和片段率η，
完整law的两个bias可恢复`k=(1-d)η=(mu_1-mu_0)/(TrJ_0-TrJ_1)`。
由此恢复d、η和全部局部effect坐标；原子effect与器件恢复值均须在物理域内。
两trace相等的旋转协变控制不能支付该绝对锚，必须显式拒绝退化除法。
该代数机制不声称12态Lindblad已经给出两run的实际J_i。

## 来源与确切验收

[新的控制来源](hardware-anchor-access.md)支付两run的nominal setting→AOM表。
实际angle/gain、rawCSV token字典、独立已知probe响应与完整原始λ的绑定按各自来源如实登记；
不会从该名义控制表推得实际零角误差或唯一参数。

Lean独立认证覆盖完整候选声明、同源概率、一般逆读consumer、全部依赖及公理。
Leankernel的范围是source law＋两独立probe的精确恢复，不包含atomic J的前向生成或器件self-cal定理。
Python另核signed响应区间与前向锚代数，保留其准确范围。

科学合同和程序先提交，再独占生成构造控制first。
两枚旧law每枚取s/t在±0.95、±1.05的16个合法纤维点，加原点，共34个白盒控制：
独立Gauss消元重建四effect，核32格旧law和两probe响应。另核分setting坐标极点、
共线反控、有限误差外包和等trace反控。
这些probe响应由已知测试仪器生成，仅承担constructor控制；actual锚已有与实际唯一参数字段均保持false。
不读事件、计数表，不花新统计预算、不选择实际硬件代表。

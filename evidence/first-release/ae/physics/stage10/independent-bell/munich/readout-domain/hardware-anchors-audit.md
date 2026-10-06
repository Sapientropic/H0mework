# 已知 law 与独立单侧锚的逆读认证

完整 source law 给出四个偏置及 X/Z rank-one 产品。每个方向各选一个非零产品，
由产品比自产各 setting 的相对坐标；两个已知 normalized XZ probe 与对应有符号响应
组成二元线性方程。law-derived determinant 非零时，全四个合法 effect 被唯一恢复。
X/Z 产品锚和 probe 可分布在不同 setting，原坐标极点不要求补造非零坐标。

ReadoutAnchors 的 40 显式声明、119 模块声明及 40 独立 consumer 声明通过
trust0、werror、asyncoff、单线程内核检查。165 新依赖节点完整闭合，50 个已付 source
边界绑定原 source/id 证书；公理集合为 Classical.choice、Quot.sound、propext。
一般消费者覆盖全部非零 signed scales、完整 source/current/next、原 whole-ledger 与 next。
非空 split-pole 控制的 determinant=1；同轴反向 probe 的 determinant=0。

Python 主实现采用 exact inverse matrix，独立实现采用有理 Gauss 消元，不 import 主实现。
14 项 synthetic 控制和另外 72 个 signed-scale 合成恢复案例通过；后者遍历两方向各 ±0.95、
±1、±1.05 以及两种 probe 配置。均不读取原事件或重新拟合。
响应区间由同一 inverse matrix 作准确 affine 投影；它们是已知 law 条件下的 probe
输入区间，不是从当前 Bell 档案生成的新统计置信区间。

独立已知原子 ionization effect 的 trace 差还可与同一 detector 的两个偏置共同解出
background 和 detected-ionization factor：k=(mu1-mu0)/(Tr J0-Tr J1)，
d=(1-mu0-k Tr J0)/2，eta=k/(1-d)。trace 差为零、非法 effect 或非法 detector 值拒绝。
这条有理公式及控制经程序审查；原子 J 的前向生成和该公式不计入本次 Lean kernel claim。

本证书认证条件逆读机制与程序控制。实际匹配的独立 probe 输入、原子控制输入和 J 尚未
由这些程序生成；actual_independent_anchor_inputs_available 和 actual_hardware_uniquely_identified
保持 false。完整 Bell law 单独存在的连续同 law 等价类保持原判决。

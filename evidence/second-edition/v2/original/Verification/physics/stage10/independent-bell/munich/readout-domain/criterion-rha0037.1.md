# RHA0037.1：原 Gaussian 认证时段与实际传播区间分离

原 source／SpinPair.visit10／row0／whole-ledger／tick16→17保持。
本修订保留[RHA0037](criterion-rha0037.md)的六枚完整33态算子、两方向、相位、自然loss、
全部数值预算及独立残差合同，只删除把原operator认证时段误作物理field终点的额外限制。

原 `GaussianAtomicPulseSource` 的 `duration_seconds=20ns` 标记
`duration_is_certification_horizon=true`、`Gaussian_zero_at_endpoint_assumed=false`、
`hard_AOM_mask_installed=false`。原H(t)、K(t)及尾场在该时刻之后继续定义。
原RHA0033已用自身完整残差验收local `[1,121]ns` 的自由密度演化。
RHA0037的首prepare因额外的 `stop<=duration_seconds` 条件失败，尚未生成handoff或数值曲线；
[首失败](gaussian-operator-first-rha0037.json)及[attempt](gaussian-operator-attempt-rha0037.json)
按原字节保留，初冻commit为 `ff6e6a015edc180a2ed57c34f64a04e43a892174`。

新传播器接受原不截断Gaussian源上的任意有限非负 `start<stop`，保留parent及原duration，
不新建pulse、不延长原认证书、不关闭尾场。完整新传播区间由自身K残差、拼接、Gaussian余项、
source列舍入、数学Gamma与物理frame价格支付。原Gamma价格本就按给定start/stop计算。
两侧early `[1,61]ns` 与late `[61,121]ns` 的原retarded local区间直接进入六枚银行。

新代码、九项合成控制及本合同先commit，再恢复原inlet并生成六枚handoff／节点曲线。
控制同时核六枚完整计划、两个方向的非零尾场区间、独立有理残差、source身份与负时刻反例。
degree64、1ns片、Taylor40、最大1/16ns步、96-bit量子、192-bit源与价格、至少64-bit实际尾数、
10^-8绝对误差门及首／中／末独立核验均保持。所有新实际输出使用新路径且不可覆盖。
数学证书沿用已核四条Gaussian共流恒等式；旧程序和全部旧输出不改。

本修订生成后继正时间有序子仪器所需传播器。两次登记积分、响应锚及实际成员由原下游消费，
`actual_hardware_uniquely_identified=false`、`controller_advance=false`。

# 一次恢复、保留接收态与连续同源更新

[唯一active](../../../handoffs/no-island-no-magic-mathematics-active-route.md)。
源码：`Conditional/RetainedReceiver/`，namespace `SourceRetainedReceiver`。
上游：[实际key库存](source-received-key-inventory.md)、[原精确恢复](source-fibre-exact-state.md)。

## 数据与作用

`Frame Key bound stride`同时保存实际有限keys、原NativeObservers.State及每个已收到key的完整有理观察数据。
完整数据包括全部H坐标、独立mass与clock；`rawAt`对库存外行返回零。
`start`调用已付restore/decode。Key只需DecidableEq；初始化证明使用原实际outputs及其依赖样本预算。

`step`只消费一个实际新增key：keys插入该key，State调用旧NativeObservers.advance，
完整观察数据调用旧ReceivedStep.advanceData，计数取自保留State。此作用不重新读取样本、恢复支持或查询原生成器。
`run`把相同输出直接交给下一receipt。`trajectory`只沿原runtime.advance的源生维数等式重索引，不另建runtime。

## 同源方程

`start_native`消费原extended_budgets；`run_native/trajectory_native`在任意有限步认回原generate，
`run_keys/trajectory_keys`直接消费outputs_append并保全部实际库存。

原Model由保留权重生成，原观察Model由完整数据回编码得到；
`model_source`认回原条件Model，`observed_realization`认回原G值。
令`rₙ=observedₙ−realize(modelₙ)`，`Mₙ`为保留计数，实际receipt为`aₙ`：

```text
rₙ₊₁(key) = if key=aₙ then [Mₙ/(Mₙ+1)] • rₙ(key) else rₙ(key)
‖rₙ₊₁(key)‖² = if key=aₙ then [Mₙ/(Mₙ+1)]² ‖rₙ(key)‖² else ‖rₙ(key)‖²
‖rₙ(key)‖² ≤ 原初始化gain × 完整sampleEnergy
```

`residual_next`直接消费原next_value_source与decoder_next；`trajectory_residual/energy`沿同一实际runtime推广。
`continued_bound`只用初始化恢复预算。后续不要求重新阈值分类正确或新的精度保证。
`reconstruction`保留`realize(model)+r=realize(observed)`；`conditional_error`以原条件权重结算
观察误差＝精确Model误差＋完整残差平方，直接交回已付原L²链。

## 原消费者与整账

完整clock的`clock_recovers/history_next`认回原actor的nextRead与material history.next。
Field先以现存inventoryMerge/forgetClock合并保留State，随后消费原embed：
`field_source`认回原Field decoder；`field_information/field_loss/field_positive`消费原信息代价、完整两级L²损失与正损失。
因此连续精确恢复并不免费取消forgetClock造成的原损失。

StageLaw进入原NativeKeys.StageLaw、NativeModelStep.Calculation、Copy.Observation和Graph.Consumer；
原material.factorizes与normal/next均消费该链。root状态为ordinary transfer。

## 验收范围

连续6步执行核对16权重、64个H坐标、独立mass/clock以及完整误差1/16收缩。
实际源样本可达控制只在初始化支付预算，任意步认回原State。
独立阈值反例中，保留计数为1而重新分类为2；该反例不声称满足原充分精度预算。
认证范围与结果见[CP212](../../../archive/living-law-framework-checkpoints-volume-45.md)。

[完整观察合并](source-retained-coarsening.md)以保留计数混合全部Data，完整Frame交换原receipt，并把混合残差送回原Field误差及normal/next。

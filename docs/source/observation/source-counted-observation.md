# 计数观察的实际作用与原 L² 消费

[唯一 active](../../../handoffs/no-island-no-magic-mathematics-active-route.md)。
源码：`Conditional/CountedObservation/`，namespace `SourceCountedObservation`；
上游为[完整观察合并](source-retained-coarsening.md)与[保留接收态](source-retained-receiver.md)。

## 实际表示与作用

`Entry` 保存实际 key 的计数、计数加权的完整 H 数组及独立 mass/clock。
`Represents` 覆盖所有自然数坐标，不以数组长度相同替代实际内容相同。
`fromInventory` 从原有限库存及已经接收的 Frame 初始化；重复 key 不增加 occurrence。
`step/run` 只消费旧表与本次 receipt：选中项累加 born 坐标、mass 和 clock，未选中数组保持原样。
初始化之后不查询样本、不调用旧恢复器；`run` 使用 `Nat.rec`。

`ofFrame` 是使用 `Finset.toList` 的非计算性识别口；实际执行入口是 `fromInventory`。

## 由初始源支付任意步条件

`received_simulates` 消费原完整库存及初始化样本预算，生成任意步 Table 与原 Frame 的同源关系。
`source_decode` 对所有 key 成立：实际发生的非零计数由原 native/inventory 生成，缺席 key 读零。
未来计数非零不是该源合同的调用者前提。

`readValue` 只从 Table 解码并进入原 `completeValue/CurrentCoordinates.realize`；
完整 `G = H × mass × clock` 的 L² 直积、原 occurrence 与独立轴均保留。
`read_residual` 把实际读值相对原自主 Model 的偏差交回同一完整残差。

## 原条件与 Field 消费者

`conditional_error` 直接消费实际 Table 读值及原条件分布，生成原最优条件误差加完整残差能量。
`total/weight/mixedValue` 使用实际 Table keys 和计数生成合并权重及观察值。
`observationTable` 进入原 Field，`field_balance` 给出

```text
dynamicError(actual table observation)
  = original dynamicVariance
  + sum_actor originalWeight · ‖sum_key actualWeight · (readValue − originalModel)‖²
```

残差先作向量混合再取平方范数，保留交叉项。相反残差可以抵消；原压缩方差继续保留。
`field_information` 消费原信息成本定理，不另造熵或恢复定理。
自主 Model、完整条件分布与 fine occurrence 仍由同一 Frame/native 源承担。

## 本次 receipt 的真实恢复差额

`CountedRecovery.residual_mass_next` 直接消费既有逐 cell 残差收缩和完整 actor 库存。
`error_update` 将它与原 `NativeBirth.minimum_update` 合成；`field_update` 再交回实际 `Table.step` 和原 Field：

```text
(N+2) · E_next = (N+1) · E_old + sourceInnovation − c/(c+1) · ‖mixedResidual‖²
```

N 是原 inventoryBound，c 是本次 born 所在 coarse cell 的实际 Table 总计数。
新增 actor 的残差也已计入；c=0 无需另加前提。source innovation 与残差恢复共同决定总误差变化。
新方程保留全部 G、同权混合交叉项及原 occurrence；旧原 Model、posterior 和信息增量直接复用。

## 从运行表恢复完整 posterior 与原 Model

`CountedPosterior.counted_trajectory` 保留完整 G 的计数加权残差；
`initial_half_margin` 直接消费原 `start_bound/extended_budgets`，将一次初始预算变成所有 key 的固定半间隔。
这份界包含以后才进入 actor 库存的 H 坐标。

`restore` 只从实际 Entry 的 H/mass/clock 除以当前 N+1，调用原 `completeSamples → FibreExactState.restore`。
原全局阈值精确化成 counted H 坐标大于 1/2；按完整支持基数重新归一化，得到原 conditional State。
计数来自恢复的支持，目标 State、read、Frame 或未来精度都不进入值构造。

`continued_source/continued_model` 从初始样本预算与实际 receipt 生成任意步完整 posterior/原 Model。
`continued_field_balance/update` 直接用 Table 恢复 Model 替换 Field 方程的模型项；带噪 Raw 和混合残差原位保留。
公开口不要求未来 margin，联合信号与条件归一化分别由原作用链支付。

## 原自主后继

`CountedAdvance.next/nextModel` 只从当前 Table 三轴生成原恢复器的样本，直接调用原
`FibreExactState.next/nextModel`：恢复当前 State，再由本次 receipt 调用原 `NativeObservers.advance`。
`step_commutes/step_model_commutes` 证明实际表更新后恢复与这次原作用一致。

`continued_next/continued_model/continued_next_field` 只取原初始化样本预算及已生成前缀；
未来精度不进入公开口。下一 Field 实际使用旧 Table 加 receipt 生成的 Model，保留更新后完整 keys、
同权混合残差及全部 G 轴。已有 `RetainedReceiver.run` 的初始化恢复和持续 native 更新直接保留；
这里的 Table 恢复口不宣称新的求值缓存。

## 实际表粗化与后继消费

`CountedMerge.mergeTable` 只消费实际 Table 与 forget：keys 取实际像，count 复用 total，
完整 H 按原数组最大长度零填充后逐坐标累加，mass/clock 独立累加。
`merge_simulates` 覆盖全部 Nat 坐标、缺席及零计数，直接认回原 `RetainedCoarsening.merge`。
`next_simulates/next_observation` 消费已有 merge_next，将粗表实际 step 交回同一次 fine receipt 和原完整 Field。

原 fine 初始预算的共同 threshold 与实际总 count 支付粗表的固定半间隔；
`trajectory_half_margin` 直接消费旧 merge_trajectory 及计数残差守恒。
`continued_source/continued_next_model` 无新 coarse 样本或未来预算，生成粗表的完整 posterior 及下一 Model。
`continued_next_field` 的左端是原 fine 更新后的 observationTable，右端实际使用粗表 step/nextModel；
完整混合残差与原 dynamicVariance 保留，不能从粗 posterior 免费恢复 fine actor。

这是实际 counted 数据粗化与恢复执行链；原粗化数学律与 Field 方程被直接消费。
范围为任意实际 fine 前缀的粗化、粗后验恢复及当次下一拍原 Field，不宣称全局最小内存。

## 同根安装与验证

`Material.stage_law` 已进入原 `NativeKeys.StageLaw`；原 `current_consumed` 经 calculation
在 normal 与 next 都暴露该源合同、真实恢复增量、Table 完整 posterior/Model、原自主后继及实际粗化链。固定 root 和 process 保持 ordinary transfer。

[可复跑控制](../../../../../Verification/no-island/counted-observation/README.md)检查完整来源闭包、
原 normal/next、实际 `runtimeAt 3` 的预算可达性，以及 4 步、8 keys、640 坐标的执行控制。
验收数字见 [CP215–219](../../../ledgers/living-law-framework-checkpoints.md)；CP214 的签收范围为 scratch 读回链。

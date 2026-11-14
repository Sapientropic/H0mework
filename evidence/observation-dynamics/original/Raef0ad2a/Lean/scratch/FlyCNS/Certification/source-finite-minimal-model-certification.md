# 完整有限原源：可计算最小未来模型与动态精化

Verdict: **certified at the complete finite-source scope**。

冻结候选 `SourceFiniteMinimalModel.lean` SHA256
`aa2805aa54f6d53fdaf457ba3e227bd4e8c970bb8e84da750e22bbda7f80fafa`。
fresh `--trust=0 -DwarningAsError=true` 通过；**55 个独立内核控制、61 份完整 type/value 闭包**通过。
公理限于 `propext`、`Classical.choice`、`Quot.sound`；无项目公理、unsafe、`sorryAx`、
Certification／Controls 或 fixture 依赖。见[闭包摘要](finite-minimal-audit-summary.json)。
候选与冻结的 `SourceRepresentation.lean` 均未改动。

## 已签收的 producer 与消费口

`Source` 接收完整原 `Fin` 状态／操作／读者库存、独立异构读类型及其可判定相等、原初态、
自主操作、当前 read 和原一步 action。三类库存由具体字段保证非空；action 的类型保证所有原状态
上的操作完备并封闭。它没有 quotient、未来表、正确 partition、normalizer 或 every-fibre witness 字段。

`initialPairs → refine → kernel` 从当前读者相等开始，逐次检查**全部原操作**的后继 pair。
非固定步严格减少原 pair 的基数；`kernel` 自行用生成的初始 pair 数作为 fuel，
`kernel_fixed` 支付固定点。内部 `settle_fixed` 的 fuel 界与 `settle_retains_future` 的逻辑 lemma
不成为 caller 提供的目标证书。

`kernel_future_exact` 双向覆盖**全部有限操作词、每个独立读者及全部原状态**。
`code` 计算已生成类的最小原地址；`encode_kernel` 给出精确未来核，`next_commutes`、
`all_words_commute` 与 `every_future_reader_commutes` 实现同一原 action／read 的自主模型。
`minimal` 约束竞争实现自身的 action／read commuting laws，证明它不能丢失本模型的未来区分；
这些候选 laws 没有进入原源 producer。每个未来 word／reader 在 Model 上的 read 有显式可计算
见证与唯一因子化，不要求 caller 预给 factor 或 normalizer。

`adjoin` 保留原状态／操作库存、原初态与自主字母，并增加独立原读者。
`refinedKernel` 从已生成旧 kernel 与新当前 signature 出发，重新闭合全部原后继；
`incremental_matches_recomputed_minimum` 证明增量算法等于完整重算的最小核。
`refined_model_future_exact` 与 `actual_future_escape_separates` 消费新读者的**全部未来**，
并非静态 `(old code, current new read)`。

## 同源连接与精确范围

`fromProcess` 接收已固定 `SourceNativeLivingRootProcess` 的完整 raw `ConstructivePresentation`
双向库存，而不是观察历史样本或行为商。`fromProcess_decoded_word` 保持原词的执行顺序；
`computed_matches_source_future_model` 直接消费原 `WholeRepresentation.model_future_kernel`。
`computed_autonomous_next_is_actual` 的输入是原 sealed `LivingRuntimeState`，next 对齐其原 tick。
`computed_model_and_actual_root_factorizes` 与同一 runtime 的原 occurrence／whole-ledger／next
因子化相接；它不自动把未注册的 ledger 或其他读者加入 Model 的观察族。

这是完整有限源上的通用可执行最小模型 producer。实际完整52字段根目前 `root_visit : Nat`，
尚未给出该完整 raw Fin 库存，故本次不签实际 MaleCNS 的行为 partition 或 controller 推进。
原 pair 库存的构造成本与已签物理 codec 资源收益分开计账。

## 独立正反控制与编译执行

独立四状态、两原操作、Bool／Nat 异构读者控制覆盖完整 raw domain：当前 pair 库存10，
生成未来核仅4个对角 pair，最小 code 为 `[0,1,2,3]`，自主后继 code 为 `[1,2,3,3]`。
常数读者源产生16个 kernel pair 与真正的常数 code `[0,0,0,0]`。

控制拒绝当前读数相同却未来不同的 coarse code、互不兼容原读数的 Unit code、
仅一轮精化就称 fixed 的关系，以及原词 `[0,1]`／`[1,0]` 的方向混淆。
新增读者在 raw 0／1 当前和一步后都相同，两步后不同；增量算法保留全部未来区别，
产生 `[0,1,2,3]`，与完整重算精确相等。

这些 code、Model 自主 next 与增量相等也由独立 `#eval` 编译执行得到，
没有 `native_decide`、手写 extern 或 native proof；内核控制与执行输出分别记录。
见[控制与执行结果](finite-minimal-controls.json)。四状态控制不充任实际全图证据。

复核入口：`build_finite_minimal_audit.py` 生成 focused audit，`--summarize` 生成完整闭包摘要，
`--runtime` 生成独立编译执行控制。使用与 capsule 相同的 `body-full` overlay 与 trust0／werror；
全部重日志、闭包与临时 Lean 文件在 ignored `Certification/.cache/finite-minimal-audit/`。
本轮只提交这份报告、两个小 JSON 与该复核脚本。

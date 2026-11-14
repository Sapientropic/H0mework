# 完整原源：实际核逃逸与有限残差动态精化

Verdict: **certified at the checked interface and actual-consumer scope**。

冻结 `BodyFullDynamicRefinement.lean`／`full_dynamic_refinement.py` 的 SHA 与构造交接一致。
fresh `--trust=0 -DwarningAsError=true` 通过；**34 个独立内核控制、48 份完整 type/value 闭包**通过。
逐项检查 `ConstantInfo.isUnsafe`；无项目公理、`sorryAx`、Certification／Controls 或 fixture 依赖，
公理限于 `propext`、`Classical.choice`、`Quot.sound`。
详细摘要见[内核与完整闭包](dynamic-refinement-audit-summary.json)。冻结构造及原根没有改动。

## 直接签收的机器口

- `findOrigin`／`separationCoordinates` 是原状态坐标 producer：从预先固定的全部 literal word／解释
  加 `visit` 搜索未表达的差异，没有 endpoint、decoder、factorization 或未来方向作 premise。
- `detectEscape` 消费同一 `root.fixedSource` 下已出生的两个 `GeneratedAt`，运行时检查旧 view 相等、
  实际后继 view 不等，再搜索更新前的来源方向。`actual_future_cannot_factor` 是该 view 的精确
  non-factorization diagnostic，不把局部结果推广为完整 Packet 或其他表示的失败。
- `escape_nextPlan_separates`／`escape_preserves_old_view` 证明精化分离实际 pair 并保留旧投影；
  `adjoined_source_coordinate_exact` 直接消费既有 `IndependentConsumerSystem.adjoin_refinedFace`。
  `viewConsumers` 的 exactness 范围是这个已声明的 view；完整自主闭包另由残差执行支付。
- `Representation` 仅保存坐标 inventory 和完整有限 Packet 残差。`execute` 通过固定 parser 消费
  同一个 `root.emit`；`continuation_current`／`continuation_every_reader` 保持完整 Current 和任意读者。
  `step_whole_ledger_next` 消费该 actual occurrence 的全部六行 ledger 与 generated next；
  `finite_autonomous_words_exact` 把任意成功有限 trace 精确消去到原 packed trace。
  source operation 的下一字母仍由原 `visit` 选择。

## 实际同源核逃逸

根为 `body-full-source-154440967171458`，instance／birth／installation 与已签收的完整首装根相同。
固定源的 before-visit 55 操作产生 after-visit **56 damage**，神经／物理时钟不推进；
after-visit 55 与 56 的 **51 个 nongate 原 word 全字节相同**。
其原源后继分别为 56 和 57，已有 **26 个 nongate word** 不同，包含 `body.integration`。

原状态差异恰为 `body.controller_enabled` 和 `root_visit`。消费者由更新前原件计算这两个附加坐标；
后继值只暴露旧核逃逸，未选择或填入新状态。gate 与 visit 同时缺失，且两支由原 F 选择不同
macro operation；本结果没有把这个实际自主状态差异改称为 isolated pure-gate effect。
相同实际分支不生成 escape；已经分离的 view 也不再被报告为这对分支的核逃逸。

## 完整残差继续

第56次完整 Current 的 **57 份原件**从压缩包重开全等。
随后只从 packet 和固定 source binding 实际执行 **56→57→58**：每拍 **58 份原件／事件**，
以及两份逐微学习／物理 trace，均与原存活根生成的结果全字节相同。
神经时钟分别为 5600／5700，物理时钟为 56000／57000；来源身份保持。

独立 checker 重读全部三份原表 **1,109,008,094 bytes**、六份 admitted graph arrays 与 source guards。
64 份源码／模型／原源 binding 在执行前后保持。descriptor alias、lost visit、missing gate 三类坏包
在 source event 前拒绝，部分解码未暴露为完整状态。源执行参数只有捕获的 primitive、固定根目录、
完整 decoded Current 和新 output；observed／independent snapshots 仅在返回后用于比较。

这份动态表示包实际由 **27,538,174 bytes 降至 17,170,139 bytes（37.6497%）**，包含完整 framing、
全部解释及旧／新坐标 inventory。该数字签收空间收益；不由它宣称整体 CPU 加速。
见[独立实际控制](dynamic-refinement-actual-controls.json)。

## 范围与复核

这次签收实际来源方向精化与完整残差的自主后继；没有宣称已计算 minimum behavioral partition。
新 Lean refinement runner 未在已经出生的 cap 内晚装：Lean 成功执行口与 actual captured-fixed-foreign
消费者分别签收，原 cap 的自身历史保持。没有制造或安装新的 U8 world row。
Python／NumPy／Numba、原 CPG 与 MuJoCo 保持原 foreign execution trust 范围。

```sh
python3 Lean/scratch/FlyCNS/Certification/build_dynamic_refinement_audit.py
cd Lean
lake env sh -c 'LEAN_PATH="$PWD/scratch/FlyCNS/.cache/body-full:$LEAN_PATH" lean -DwarningAsError=true --trust=0 scratch/FlyCNS/Certification/.cache/dynamic-refinement-audit/DynamicRefinementAudit.lean > scratch/FlyCNS/Certification/.cache/dynamic-refinement-audit/audit.log 2>&1'
```

摘要生成入口：`build_dynamic_refinement_audit.py --summarize`。
实际复核：`check_dynamic_refinement_actual.py <root> <fresh-output> --evidence <report>`，
消费冻结 `activation-58.json`。完整日志／闭包／原件保存在 ignored `Certification/.cache/`。
本认证只拥有 Certification 小文件；提交与 active route 由 parent 合并协调。

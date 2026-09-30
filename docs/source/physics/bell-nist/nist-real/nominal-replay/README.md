# nominal-replay — NIST 2015 名义装置最优独立重放

按 Christensen 博士论文 Appendix A 的公开装置模型 + 2015 论文 p.4 的**全局**信道值，独立重放
「校准以最大化 CH 违反」的最优 (r, θ0, θ1)，在**预先声明**的容差带内比对论文公布的态与角。

- 判定：`REPLAY_DEVIATION_EXCEEDS_PREDECLARED_BAND`（独立复核 `CERTIFIED_…`，逐盒点 Δθ ≤ 5×10⁻⁷°）。
  重放最优 (r\*, θ0\*, θ1\*) = (0.315464, 4.9547°, −27.2329°)；文档值 (0.287201, 4.2°, −25.9°) 在带外
  （带 r [0.31396, 0.31697]、θ0 [4.887, 5.023]、θ1 [−27.311, −27.155]）。
- 模型本身的验证（与目标值无关）：复现论文 p.4 的 2/3 无背景阈值（模型 0.6685）与 72.5% 含背景
  阈值（模型 0.7264）；偏差的输入空间归因见 `replay.json` 的 D7（相当于效率低约 1 个百分点）。
- 重跑：`python3 replay.py && python3 independent_replay.py`（各 ~2 分钟，纯标准库、离线、无随机数；
  输出逐字节可复现）。`python3 tests.py` 跑模型对称性、两条概率路径与阈值/局域极大检查。
- 文件：`criterion.md`（唯一冻结输入：机读 FROZEN-INSTRUMENT 块 + 全部自由选择与页码引证 + 修订史）、
  `christensen-appendix-a.txt`、`shalm2015-channel-inputs.txt`（逐页原文提取 + 来源 sha256）、
  `replay.json`、`independent_replay.json`、`replay-r0001-superseded.json`（被判错的第一版输出，保留）、`tests.py`。

纪律不变式：① 所有数值只来自 `criterion.md` 的 FROZEN-INSTRUMENT 块，代码内无旋钮；
② 判据先于任何优化输出写成，唯一的实质修订（r0001→r0002 的背景归一化）由**与目标值无关**的公开阈值
数字判定且不改变结论；③ 带 = 输入不确定度盒（中心 + 16 角点）上最优的逐分量 [min,max]，再加宽公布
舍入分辨率（±0.05°、±0.0005）；④ 本目录不接触任何试次事件数据、不改动仓库既有文件、不签收门禁——
输出只是后续 gate review 的候选输入。

版本标注说明：机读版本字段为 `nominal-replay-r0002`；`criterion.md` §10 把同一文件内的第二处小修订
（D3b 的退化参数化）标为 r0002.1。两处修订都在当前 `criterion.md` 内，其 sha256 与 `replay.json`
的绑定一致；D3b 修订不触及任何模型选择、输入、目标函数、带或判定。

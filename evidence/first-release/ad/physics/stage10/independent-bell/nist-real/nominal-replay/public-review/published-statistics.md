# 已发表局域统计声明与公开充分统计量

[NIST 主文 Table I](https://arxiv.org/pdf/1511.03189v2#page=8)及
[SI I.A–C、Table S-I](https://journals.aps.org/prl/supplemental/10.1103/PhysRevLett.115.250402/LHFSupplementary.pdf)
已经给出重算原印刷 p-value 所需的充分统计量。
数值核对消费 `(Nχ, NS, ε)`；实际停止前缀的执行身份与数值算术分别验收。
本口不要求新的校准、隐藏数据或新实验，不改变原 root、名义最优性与已冻统计 CI。

## 原统计合同

正事件为 `++ab`，负事件为 `+0ab′`、`0+a′b`、`++a′b′`。
只保留这四类事件形成 T 序列，`Nχ` 是预声明的 T 长度，`NS` 是其前 Nχ 个元素中的正事件数。
完整 trial 中的其他十二 outcome 不计入 Nχ，但仍计入完整曝光。
主文的 `Nstop` 与 SI 的 `Nχ` 是同一 relevant-event 口。

SI I.B 的切点规则先移除一小段 training 数据，分别估计每个 run、每组 pulse 的 T 频率 f，
再取 `Nχ≈0.9 r f`，r 为剩余 trial 数。只消费前 Nχ 个 T 事件，之后 discard。
这项规则避免一个有记忆的局域系统在有利波动后停止发出 T 事件而锁定结果。
单纯固定物理运行时间、再把整个 T 长度送入 fixed-N 二项尾，并没有支付相同的停止口。

SI I.A–C 的局域统计不要求 trial 独立或 source 平稳；允许 hidden variables 记忆此前 trial。
每侧 setting predictability 至多 `(1+ε)/2`，并按原文承担给定 predictability 时双方选择独立的条件。
相对 setting 质量须逐条件事件满足；聚合频率接近1/2不自动产生这项界。
原调整成功概率为

`q0 = 1/2 + ε/(1+ε²) = (1+ε)²/[2(1+ε²)]`，

对应印刷尾概率

`p_bin = Σ[k=NS..Nχ] binom(Nχ,k) q0^k (1−q0)^(Nχ−k)`。

SI III.A/D 给 PDRNG 的 model/metrology 估计与 synchronization-board 后验测试，
并以 `εp=.003` 调整主文 Table I；该值是十五倍约 `.0002` 的公开 conservative allowance。
原文同时允许 PSRNG 与 cultural source 对 hypothetical hidden variables 完全可预测。
这些是已发表 RNG/setting 合同的来源，不能由 diagnostics 的 i.i.d. 偏差检验替换。

## 公开的切点与成功数

下表每格为 `Nχ / NS`，各个 run 的完整 `NTotal` 由 Table S-I 单列。

| run | 1 pulse | 3 pulses | 5 pulses | 7 pulses | 完整 NTotal |
| --- | --- | --- | --- | --- | --- |
| 02-54 | 2528 / 1263 | 7659 / 3842 | 12753 / 6460 | 17854 / 9057 | 203629242 |
| 03-43 | 1213 / 618 | 3678 / 1893 | 6192 / 3190 | 8668 / 4471 | 107032197 |
| 19-45 | 2455 / 1246 | 7304 / 3692 | 11891 / 6016 | 16648 / 8465 | 182560876 |
| XOR1 | 2332 / 1179 | 7108 / 3617 | 11917 / 6034 | 16684 / 8503 | 178781131 |
| XOR2 | 2384 / 1215 | 7120 / 3616 | 11921 / 6087 | 16690 / 8546 | 177785896 |
| XOR3 | 2376 / 1257 | 7211 / 3800 | 12127 / 6378 | 16979 / 8820 | 182137032 |

主文 XOR3 四窗在各自切点的完整 trial 曝光依次为
175654992、175744824、177358351、177797650；均不等于 full run 的182137032。
SI 给 ε=0、.0001、.001、.01 的印刷尾概率；主文另给 ε=.003 的四项 adjusted p-value。
这些原数字可由公开 sufficient statistics 直接验算，不需从 full-run aggregate 推断前缀。

## 官方小程序的角色

公开 `p_calculator_for_krister.py` 的四项 `cutpoints`、`Npp` 与主文完全对应，
其尾口是 `1−binom.cdf(NS−1,Nχ,q0)`。它足以确认包含 NS 的上尾与 ε 的定义，
不独立生成前缀计数或提供 Nχ 的预声明执行日志。

`pvaluehack.py` 的16列分支累计相同四类 T outcome，并寻找 T 达到切点的 trial；
它说明逐 trial 顺序负责哪项身份。`peter_to_p.py` 还保留用整个样本的 T 数乘.9的探索路径。
后者没有消费 SI 所述独立 training 切点，不能据一个脚本文件名认定为最终发表协议。
这些代码只作为静态算法来源；独立尾概率算法不调用 SciPy、正态近似或作者缓存 p-value。

## 由完整公开 summary 产生的新局域口

[mw0001](multi-window/criterion.md)的全终点 e-value 直接消费完整 aggregate 的
W=`++ab` 和 L=`+0ab′ + 0+a′b + ++a′b′`，不把它们冒充旧切点 `(Nχ,NS)`。
局域确定赋值中，若 `A(a)=B(b)=1`，则以下三种情况穷尽：
`B(b′)=0`；或 `B(b′)=1,A(a′)=0`；或 `B(b′)=A(a′)=1`。
分别产生三个负事件，所以 unweighted win indicator 不大于 loss indicator 之和。

逐条件 setting 界 `πmin=(1−ε)²/4`、`πmax=(1+ε)²/4` 给
`P(win)≤r P(loss)`，`r=πmax/πmin`，且 `r/(1+r)=q0` 正好是 SI S4 的口。
固定 `p_k≥q0` 时，win 乘 `p_k/q0`、loss 乘 `(1−p_k)/(1−q0)`、其余乘1，
单步条件期望至多1。乘积及20项等权混合都保持非负 supermartingale。
因此终点只需 W、L；允许 memory、漂移和任意停止，计算不依 trial 排列。
光学 identical-pulse 表示的成败不改写这项局域统计界。

固定单检验给 `min(1,1/E)`；从六run、32767 mask 家族选择则给
`min(1,6·32767/E)`。窗口间的重叠不会妨碍 union bound，也不允许相乘独立似然。
20 bet 已混合进 E，不再另乘20。四个固定 XOR3 窗口给 `min(1,4/E)` 的具名范围；
它不支付在六个 run 中选择 XOR3 的成本，也不追认为事先盲选。
mask 库存只是统计家族大小，不给全部 mask 时空分离资格；九脉冲身份由来源卡单列。
固定算法的分布上界、事先的算法选择和真实执行 lineage 是三项分别验收的责任。

原文逐窗给出的 p-value 与新 familywise 上界分列。旧数字的四舍五入算术可通过或被拒绝；
新全终点统计裁决可以从已有公开 summary 原生生成。
聚合材料不能恢复某次 trial 的真实时间和前缀排列，这不阻断这两项公开审查口。

[统计来源库存](published-statistics-sources.json)只绑定原文、旧公开程序和统计合同。
独立算术合同与首回执由 `published-statistics/` 保存；该目录的数值结果不得倒写来源或原印刷值。

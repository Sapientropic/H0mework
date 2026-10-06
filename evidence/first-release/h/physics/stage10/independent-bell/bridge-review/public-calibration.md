# Storz 2023：本次公开校准证据审查

**Fig. 5 横轴已经校正仪器相位偏移；官方设置/输出编码没有授权两格反号。**
本次是旧 first100k 已揭盲之后的 bridge/calibration evidence review，不追认旧 lock。
角色记录在首次证据释放前建立，访问范围、出处和判断见
[calibration-evidence.json](calibration-evidence.json)。旧 34 个锁输入未由本角色修改。

本角色未打开 main event member，未拟合、评分或用结局选 sign。读取获准公开校准段落时，
邻接文字曾显示论文结果概要；这些数值未向父 agent 转述，未写入交付物。fig2/fig5 数值数组也未复制到本目录。

## 已观察的控制与编码

| 事实 | 精确官方位置 |
|---|---|
| `S = E00 − E01 + E10 + E11`。 | [SI](https://media.springernature.com/original/springer-static/esm/art:10.1038%2Fs41586-023-05885-0/MediaObjects/41586_2023_5885_MOESM1_ESM.pdf) §I Eq.7，印刷 p2 / PDF p3；§IX Eq.15 前，印刷 p16 / PDF p17。 |
| `b_in(t)=β_in(t)e^{-i(ω_ge t+φ)}`；`φ=0` 指 x 轴，`φ=π/2` 指 y 轴。 | SI §IX，印刷 p16 / PDF p17；已核对渲染原页。 |
| 固定脉冲为 A `(π/2)_x`、B `(π/2)_(x+θ)`，随后才随机选基；可选脉冲标为 A `a(π/2)_y`、B `b(π/2)_(y_θ)`。 | [Methods](https://www.nature.com/articles/s41586-023-05885-0) “Optimizing the measurement basis”；[Fig.4](https://www.nature.com/articles/s41586-023-05885-0/figures/4) 原图。图上 x/y 箭头指输出信号，不提供 Bloch 旋转方向。 |
| bit `0` 阻断可选脉冲，bit `1` 放行。读出 `g→+1`、`e→−1`；FPGA packed code `0,1,2,3` 分别为 `(0,g),(0,e),(1,g),(1,e)`。 | SI §II，印刷 p6 / PDF p7；Table SIV，印刷 p17 / PDF p18。旧 metadata 说明事件文件已解包；本次未重开该文件。 |

SI §IX Eq.14–16 的逐字公式责任是：

```text
γ = φ_ef^A − φ_f0g1^A + φ_f0g1^B − φ_ef^B
|ψ⟩ = (|eg⟩ + e^(−iγ)|ge⟩)/√2
S = 2√2 cos θ_SI
θ_SI = φ_ef^A + φ_ge^A − φ_f0g1^A − (φ_ef^B + φ_ge^B − φ_f0g1^B)
```

这里 `φ_ge` 是两个测量脉冲合成的有效相位。官方没有给出它逐 setting 对应的带符号 unitary。
同段同时写 `θ=θ_control+θ0`，并说展示 Fig.5 时从 `θ_control` 扣除 `θ0=160°`，且讨论约每小时重校。
**这是已校正横轴的证据，不是已发布原始控制相位或独立拟合记录的证据。** 原文未给 offset 估计器或误差；
不得仅因共用 θ 符号就令 Eq.16 相位、单个脉冲轴角及图横轴相等。

## 校准资产能承担什么

| 资产与已观察内容 | 本轮判断／未验证项 |
|---|---|
| `fig5.txt` L4 给完整扫描角轴，L6–10 给四相关函数，L13–21 给图中扫描汇总；[Fig.5 caption](https://www.nature.com/articles/s41586-023-05885-0/figures/5) 把各扫描点称为各自的 Bell test，虚线来自主方程模拟。 | 扫描产品及各点实验有官方出处；[⚠️] 与 fixed main 严格逐试次不交叉仍无 run/时间/行号 manifest。没有 raw `θ_control`、offset 记录、逐点误差或 setting 样本数。逆算原始相位还需要选定原文校正方向的解释，无法恢复精确命令及不确定度；不补零误差或自制 error bar。 |
| `fig2.txt` L4–8 是测量矩阵，L11–15 是主方程矩阵；[Fig.2b caption](https://www.nature.com/articles/s41586-023-05885-0/figures/2) 明示前者为经过读出纠正的态层析。 | 层析含源态信息。直接把矩阵作为 source，会把源态预测改成经验态输入；可服务另行声明的条件性测量模型检验，不能签收原 source 预测。主方程矩阵也是模型输出，不是原始仪器参数。 |
| SI §VII、Fig.S7，印刷 p12–13 / PDF p13–14：已知 g/e 制备训练积分权重与 Gaussian threshold，Bell tests 前固定。 | 这是独立仪器训练方法的公开证据；获准 ZIP 没有两站各自 asymmetric readout errors、误差传播或逐运行校准记录。 |

旧 metadata 的 `sealed_non_evaluation_reference` 与省略 calibrated model 是旧协议事实；本审查保持其原义。
本次三个获准 ZIP member 的 hash 均与旧 metadata 一致。[ETH 数据记录](https://www.research-collection.ethz.ch/entities/researchdata/100f0077-511e-4765-b6c8-08ff50a0962a)
中 `readme.txt` L22 只说明按图命名，L24 指向按需索取更多数据；未提供不交叉证明或控制代码。
公开代码补查（2026-09-06）：article 的 Data availability 指向按需索取，未列独立 Code availability；
SI 参考文献 [20]（印刷 p22 / PDF p23）链接作者的
[BellAtHome](https://github.com/jdbancal/BellAtHome/tree/02ac8dc4ecbe7e7d9d39171d9220e5cf561a5e23)，其 README 说明这是测量依赖性演示。
另核对 [QudevETH](https://github.com/QudevETH) 的
[PycQED 公开版本](https://github.com/QudevETH/PycQED_py3/tree/e3aa99352a0cd3978c071aa1762624406556a4e5) 文件树、公开分支名和定向序列源码；
结合论文标题、DOI、作者与 GitHub 搜索，**[⚠️] 所审范围未恢复实际逐 setting 相位映射或 phase log**。
通用控制库与概念演示未替代本次运行配置；此次补查未重开任何实验数据，具体检索范围记在 JSON。

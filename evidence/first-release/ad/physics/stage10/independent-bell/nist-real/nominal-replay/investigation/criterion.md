# r0004：双基可见度与完整四角的装置研究判据

版本 `nominal-investigation-r0004`，2026-10-01。
本文件必须先提交，再执行本版任何数值重放；旧 r0001/r0002/r0002.1/r0003 判据、
输出和实现均保持原字节。本版输出进入本目录，不能覆盖旧回执。

> No model choice or parameter in this file is adjusted after observing replay output; any change
> requires rewriting this criterion first.

已见信息：旧重放、P23、r0003 全部结果及其诊断；没有看过下述新模型的优化输出。
本版检验来源支持的光学机制及已命名映射缺额。它不通过选择碰巧靠近文档值的模型
签收原2015仿真身份；数值通过与装置来源充分分别记录。

## 控制与直接消费者

分类是 `bounded subordinate producer / conditional apparatus readout`。
同一归一实幅制备，经源模式偏迹或局域 Pauli 混合，进入原 Born effect 的线性读出。
原 `SpinPair.visit 10`、material row、whole-ledger、tick16→17 后继不变。
直接消费者是本目录 `replay.py`、`independent_replay.py` 与 `verify.py`；readiness
读取研究回执及其来源缺额，同时保留 r0003 的有效负向判决。研究相容不替代生产准入。

## 已核来源与固定责任

- Shalm 主文 p.3 Fig.1：PPKTP 内两条下转换路径形成 HH/VV 叠加，源相位固定0。
  p.4：最大纠缠态的 H/V=0.999±0.001、D/A=0.996±0.001；两侧 Klyshko 系统效率
  74.7±0.3%、75.6±0.3%；仿真消费效率、发对率、可见度和背景。来源及PDF哈希见
  [design-sources.json](design-sources.json)。
- 官方 SI p.1 §I.A / Eq.(S1)：设计校准最大化 CH 违反。保留 LHS−RHS 原目标；
  不改换比例、信噪比或 p 值目标。
- Christensen thesis p.52脚注4：D/A 高可见度表明 beam-displacer 源的相干性与稳定性。
  App.A p.76–78 给出纯态、偏迹、三类噪声与 CH 优化方法；其镜像归约使用对称模型。
  r0003 延拓不等效率后，该对称归约需要独立验证，故本版开放四角。
- 这些来源没有给出最大纠缠校准到非最大态的完整通道放置或设计输入表。
  `source_mapping_identified=false` 是本轮待支付的实际责任，不是数值输出决定的标签。

## 同一制备生成的四个固定模型

所有模型从同一 `|ψ_r⟩=(|HH⟩+r|VV⟩)/sqrt(1+r²)` 出发，V,H 为计算基。
记 `Δ=(r²−1)/(r²+1)`、`χ=2r/(r²+1)`。
XZ轴为 `(sin2θ,cos2θ)`，θ 相对垂直偏振片。

**pure_reference** 保留 r0003 的 δ=0 纯态，作为镜像与完整四角的直接基准。

**mode_overlap**：双路径源 `|HH⟩|f_H⟩+r|VV⟩|f_V⟩` 对未读模式偏迹，
生成 `ρ_r` 的 HH/VV 对角与非对角 `rγ/(1+r²)`；实 `γ=V_DA`。
概率保留原边缘，相关为 `Tzz=1,Txx=γχ`。H/V=1 位于公开区间[0.998,1]。
固定模式重叠对 r 不变是本次明确的光学假设，不能声称已恢复原仿真。

为精确检验最大态校准是否唯一指定非最大态映射，另固定两种合法过程：

`Γ_{x,z}(ρ)=D_Z^x(B_X^z(ρ))`，其中
`D_Z^x(ρ)=((1+x)/2)ρ+((1−x)/2)ZρZ`，
`B_X^z(ρ)=((1+z)/2)ρ+((1−z)/2)XρX`。

**pauli_left**：`Γ_{V_DA,V_HV} ⊗ Id`；
**pauli_balanced**：`Γ_{sqrt(V_DA),sqrt(V_HV)} ⊗ Γ_{sqrt(V_DA),sqrt(V_HV)}`。

两者在 r=1 的完整密度矩阵相同，均兑现两个中心可见度。
r≠1 时相关仍相同，单边均值分别是
`(V_HV Δ, Δ)` 和 `(sqrt(V_HV) Δ,sqrt(V_HV) Δ)`。
它们是校准不能唯一决定映射的具名见证，均没有原2015通道放置来源；不能择优升格。
矩阵路径必须分别取 Alice/Bob 偏迹，不复用 Alice 约化矩阵充当 Bob。

所有四模型的计算可用共同矩表达：

`P++ = (1 + m_A Δ az + m_B Δ bz + z az bz + x χ ax bx)/4`，
`P_A+ = (1 + m_A Δ az)/2`，`P_B+ = (1 + m_B Δ bz)/2`。

`(m_A,m_B,x,z)` 分别为
`(1,1,1,1)`、`(1,1,V_DA,1)`、`(V_HV,1,V_DA,V_HV)`、
`(sqrt(V_HV),sqrt(V_HV),V_DA,V_HV)`。
该表达须与生成的密度矩阵独立核对，不把目标概率放进 primitive。

## 信道与目标

主文输入保留 r0003 的真实概率单位：ηA=0.747±0.003，ηB=0.756±0.003。
背景 `bA=8.9e−7,bB=3.2e−7`；每脉冲 `q=5e−4`，盒[4e−4,6e−4]。
一试次一个固定 pulse slot 与本地窗，不读事件或按输出选窗口。

沿用 App.A 的逐试次 M3：
`s_A=qηA P_A+ + bA`，`s_B=qηB P_B+ + bB`，
`j=qηAηB P++ + s_A s_B`。
该 accidental 上界保持其原具名近似身份，不等同于全事件仪器运输器。

`S_CH = j00+j01+j10−j11−s_A(a0)−s_B(b0)`。
完整优化变量 `(r,a0,a1,b0,b1)`；同时保留镜像限制
`(r,t0,t1,−t0,−t1)` 作为对照。

## 确定性搜索与机器验收

- 域 `r∈[1e−6,1]`，四角均∈[−90°,90°]；同时翻转所有角为同值表示。
  规范化取角序列中首个非零值为正；不交换实际 Alice/Bob 或设置身份。
- 主实现：两偏移镜像粗网格生成固定多起点；镜像用26邻居细化，完整四角用逐轴
  全域最大化。固定其它轴时每个角是一阶 sin/cos(2θ)，可以直接求全域最优；
  r目标为 `C+BΔ+Xχ+DΔ²`，求其四次导数多项式的所有区间实根及端点，再比较。
- 独立实现：独立矩阵生成／双侧偏迹；另一偏移粗网格，多起点 Nelder–Mead，
  随后独立坐标黄金分割细化。不得从主输出取得输入、起点、带或容差。
- 输出是具名确定性数值搜索；双实现一致不冒充连续全域最优证明。
- 两程序必须检查新判据字节已进入冻结 commit。所有输入/实现/来源有 sha256 绑定。
- 四模型均重放中心的镜像与完整四角；只对来源有机制依据的 mode_overlap 扫描
  ηA、ηB、q、γ 四维中心＋16角点，共17点。两个 Pauli 见证只声明中心数值，
  校准非识别的量词由通道恒等式承担。
- mode_overlap 带为17点完整四角数值的分量[min,max]，保留原舍入加宽：r±0.0005，
  四角±0.05°；五文档值全部带内才 `CONSISTENT`，否则 `DEVIATION`。不改验收口。
- 独立一致性容差保持 `|Δr|≤1e−5,|Δangle|≤0.001°,|ΔS|≤1e−10`。
- 记录完整四角与镜像的目标差；核对不等效率横向导数及 Werner 盲区的代数恒等式。
  旧 tilt 诊断 Bob 偏迹错误另外做固定反例，不改旧主结果。
- `source_mapping_identified=false` 与 `production_admitted=false` 必须随输出保留；
  来源字段只有新证据能修订，不能由数值相容自动变为 true。

## 唯一机读输入

<!-- FROZEN-STUDY-BEGIN -->
```json
{
  "criterion_version": "nominal-investigation-r0004",
  "scope": "conditional_visibility_mapping_and_full_control_replay",
  "source_mapping_identified": false,
  "production_admitted": false,
  "models": ["pure_reference", "mode_overlap", "pauli_left", "pauli_balanced"],
  "channel": {
    "eta_A": {"center": 0.747, "half_width": 0.003},
    "eta_B": {"center": 0.756, "half_width": 0.003},
    "background_A_per_trial": 8.9e-7,
    "background_B_per_trial": 3.2e-7,
    "pair_probability": {"center": 0.0005, "box_low": 0.0004, "box_high": 0.0006},
    "visibility_HV": {"center": 0.999, "box_low": 0.998, "box_high": 1.0},
    "visibility_DA": {"center": 0.996, "box_low": 0.995, "box_high": 0.997}
  },
  "domains": {"r": [0.000001, 1.0], "angle_deg": [-90.0, 90.0]},
  "primary_optimizer": {
    "grid_r_step": 0.05,
    "grid_r_start": 0.05,
    "grid_angle_step_deg": 3.0,
    "offsets": [0.0, 0.5],
    "keep": 6,
    "mirror_iterations": 700,
    "mirror_step_stop": 1e-10,
    "coordinate_cycles": 250,
    "coordinate_stop": 1e-10,
    "polynomial_root_stop": 1e-12
  },
  "independent_optimizer": {
    "grid_r_step": 0.04,
    "grid_r_start": 0.02,
    "grid_angle_step_deg": 4.0,
    "keep": 6,
    "simplex_step_r": 0.04,
    "simplex_step_angle_deg": 4.0,
    "simplex_iterations": 3500,
    "simplex_coordinate_stop": 1e-10,
    "golden_iterations": 140,
    "golden_stop": 1e-10,
    "coordinate_cycles": 180,
    "line_scan_cells": 16
  },
  "band": {"r_widen": 0.0005, "angle_widen_deg": 0.05},
  "tolerance": {"r": 0.00001, "angle_deg": 0.001, "S_abs": 1e-10},
  "forensic_tilt_controls": {"r": [0.25, 0.5], "delta_deg": [1.5, 3.0], "angles_deg": [0.0, 22.5, 45.0]},
  "input_sources": ["../../instrument.json", "../criterion-r0003.md", "../christensen-appendix-a.txt", "../shalm2015-channel-inputs.txt", "design-sources.json"],
  "outputs": {"primary": "replay.json", "independent": "independent_replay.json", "verification": "verification.json"}
}
```
<!-- FROZEN-STUDY-END -->

## 本轮完成条件与下一来源责任

具名 mode-overlap producer、双基 Pauli producer 和独立矩阵消费者实现；
完整四角双重放、17点带与五比较、单位/来源/独立性检查全部执行并保存真实判决；
最大态校准相同但非最大态边缘不同的证明及 direct consumer 核对；
readiness 如实读取研究结论及仍缺的来源，不覆盖旧事实。

若原装置映射仍无法识别，需要提供同一设计实例的 `r→ρ_r` 或两路径模式重叠/噪声
放置、两侧/设置效率的输入身份，以及实际优化自由度／目标。模型本身和输入绑定应
来自原设计或独立装置 characterization；文档态、角和 Bell 结果不能充当这些参数的拟合输入。

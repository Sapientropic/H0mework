# P23 同源收集族：执行前冻结合同 cs-r0001

2026-10-01。此文件必须先进入独立分支的 Git commit，再运行任何本版数值模型或测试。
已读 r0003/r0004/r0005 的历史结果、公布控制与原 NIST 四模代码；不以它们的距离选择
模型、参数、样例或判决。本版不优化公布态/角，不给历史重放换输入。

## 任务与 authority

从同一 HH/VV 双路径源和本地光学收集等距映射，生成四个 CC/CL/LC/LL 分支，
再生成非归一 Ω_AB、Ω_A、Ω_B。单侧对象包含伙伴失模，最后消费 analyzer effects。
这是 bounded subordinate optical producer，直接消费者是独立全模振幅收缩与 Lean
代数 consumer；不安装原 root face，不改 `positiveSmoothUnifiedSource`、`SpinPair.visit10`、
原 material row、whole-ledger、tick16→17 或主线程公共状态卡。

本任务只拥有 `investigation/collected-source/` 新目录。旧源码/判据/回执保持。
禁止读取 Bell 试次档案、外联、修改 publish、推送；不写生产 readiness。

## 具名模型假设

- **S1 单对层**：全源每脉冲以 Q 发一对，否则真空；以下 Ω 按发出一对条件归一。
  多对不能靠 q_eff 自动补齐。另给原 N=4 Hamiltonian 的低增益接口及标量纯损失归约。
- **S2 固定双路径**：归一源为 `( |HH>F_H + r exp(i phi)|VV>F_V )/sqrt(1+r²)`；
  两个 F 各为归一有限联合空间/频谱模振幅，r≥0。H/V 是本研究坐标；与原代码的
  V-first 次序必须显式同时重命名。跨 r 固定 F 与光学元件，不预设实装已满足。
- **S3 本地保偏振收集**：每侧每偏振每输入模施加
  `|p,i> -> exp(i phase_p_i) cos(beta_p_i)|C,p,i> + sin(beta_p_i)|L,p,i>`。
  C/L 正交，模标记和失模偏振仍存在；此单输入列可扩成二端口 unitary。
  它是明确光学元件，不接受任意完整待证 channel 或 Ω/目标概率作为输入。
- **S4 未读模**：不分辨的空间/频谱标签与失模的全部自由度做偏迹；不相干相加的
  是正交标签。同标签 HH/VV 在 CC 保留干涉；trace 伙伴的偏振消去单侧 H/V 非对角。
- **S5 探测平面**：入模后常数 uA/uB∈[0,1]，无背景、无死时间、无设置依赖，
  rank-one 偏振 effects 可含相位。Klyshko 校准是未筛偏振或校正筛选后的率。
  背景、window、bucket/multipair 与设置映射列为外部接口，不能混进 Klyshko 恒等式。

## 固定交付与验收

1. 主路径按 CC/CL/LC/LL 模振幅生成 Gram/三个 Ω；独立路径从全源态、本地映射和
   analyzer 振幅直接求和，不调用主模型、统计量、Ω 或概率函数，不读取主结果后再生成自身结果。
2. 每个冻结样例对全部 r、源相位、analyzer 组合比较三个 Ω、singles、joint、四种 click/no-click；
   绝对容差 2e-12。核源归一、分支守恒、非负、无信号、Ω_A−tr_B Ω_AB 的正性。
3. 正控：统一收集归约、全收集、全失模、源端点、复相位的 Y-sensitive 读出。
   显式 override：强制统一收集；反控：用 joint 偏迹冒充 singles 必须被检出。
4. 两份源的 CC 完全相同且 r=1 未筛偏振 Klyshko/总率相同，而非最大制备 singles 分叉；
   每份的原始模振幅固定于下列 recipes。不得用目标输出倒算新的样例。
5. 解析推导 r_col、环境相干、Klyshko/Q/QPp/q_eff，以及全 effects 标量归约条件。
   Lean 核验实际有限收集分支的 singles 分解、生成的率和归约恒等式及精确反控。
   只声称具体 Lean mouth 已证明的范围，Python 复振幅模型另做独立差分。
6. 列明最小可识别校准量、必要退化情形、未取得的外部字段；相同平衡校准不作实装身份。
7. 原四模接口：从原 pair-sector 系数读单对 r_src；在共同单模、偏振无关独立纯损失下，
   用二项损失求和核 `D_eff(n)=1-(1-uT)^n+d`，n=0..3。完整四模的 gain 与 q_eff 不混同。
8. 所有控制是合成研究样例；不比较公布控制、不运行优化、不授予 publication/production 身份。

## 冻結样例输入

下列 `power_H/V` 是源端联合模强度，phase 是源端模相位（单位 pi）；程序先取平方根生成 F。
未指定源端 phase 时为0。`beta_A/B` 每行对应 H/V，各列对应本侧模，单位 pi；
未指定传输 phase 时为0。每条源 power 总和为1；只有这些源/光学原始输入允许进入 producer。

<!-- CS-FROZEN-BEGIN -->
```json
{
  "version": "p23-collected-source-cs-r0001",
  "tolerance": 2e-12,
  "r_values": [0.0, 0.25, 0.5, 1.0, 2.0],
  "source_phase_pi": [0.0, 0.5],
  "analyzers": [[0.0,0.0],[0.5,0.0],[0.25,0.0],[0.25,0.5],[0.137,0.31]],
  "rates": {"Q": 0.001, "uA": 0.8, "uB": 0.7},
  "fixtures": [
    {"name":"uniform", "power_H":[[1]], "power_V":[[1]], "beta_A":[[0.17],[0.17]], "beta_B":[[0.23],[0.23]]},
    {"name":"all_collected", "power_H":[[1]], "power_V":[[1]], "beta_A":[[0],[0]], "beta_B":[[0],[0]]},
    {"name":"all_lost", "power_H":[[1]], "power_V":[[1]], "beta_A":[[0.5],[0.5]], "beta_B":[[0.5],[0.5]]},
    {"name":"path_filter", "power_H":[[1]], "power_V":[[1]], "beta_A":[[0.1],[0.3]], "beta_B":[[0.2],[0.13]], "phase_A":[[0.1],[0.4]]},
    {"name":"unread_tag", "power_H":[[0.5,0],[0,0.5]], "power_V":[[0.5,0],[0,0.5]], "source_mode_phase_V":[[0,0],[0,0.5]], "beta_A":[[0.1,0.3],[0.1,0.3]], "beta_B":[[0.2,0.1],[0.2,0.1]]},
    {"name":"calibration_I", "power_H":[[0.25,0.25],[0.25,0.25]], "power_V":[[0.25,0.25],[0.25,0.25]], "beta_A":[[0,0.5],[0,0.5]], "beta_B":[[0,0.5],[0,0.5]]},
    {"name":"calibration_II", "power_H":[[0.25,0.4],[0.1,0.25]], "power_V":[[0.25,0.1],[0.4,0.25]], "beta_A":[[0,0.5],[0,0.5]], "beta_B":[[0,0.5],[0,0.5]]}
  ],
  "four_mode_control": {"n":[0,1,2,3], "T":[0.0,0.3,1.0], "u":[0.0,0.7,1.0], "d":[0.0,0.000001]},
  "identity": {"synthetic":true,"publication_configuration_identified":false,"production_admitted":false}
}
```
<!-- CS-FROZEN-END -->

完成条件：冻结 commit 可核；两条前向路径及关键正反控制通过；Lean focused trust0/werror
及公理审查通过；机制说明与外部字段齐全；只提交本新目录。本次不合并主线程。

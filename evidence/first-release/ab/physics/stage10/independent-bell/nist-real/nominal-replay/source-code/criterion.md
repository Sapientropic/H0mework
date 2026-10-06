# r0005：原 NIST 四模设计代码恢复与配置身份重放

版本 `nominal-source-code-r0005`，2026-10-01。先提交本文件与来源绑定，再执行本版任何
数值测试或重放。原 r0001/r0002/r0002.1/r0003/r0004 的判据、实现及输出保持原字节。
已见旧结果、论文公布态/角、原作者打印代码及历史默认参数；尚未执行本版模型。
本版固定全部分支，不按数值是否靠近公布控制选择来源、输入或判据。

## 同项目来源与消费者

Meyer-Scott 2016 Waterloo thesis p24–25/§2.5 p38/Appendix A p159–163，分别绑定
2014–2015 NIST 项目、作者的优化贡献、用于文献[37]的仿真以及 NIST2015 `CH_B.m`。
完整来源与页/字节哈希见 [sources.json](sources.json)，代码提取见 [author-code.txt](author-code.txt)。
原定制 MATLAB 函数没有取得原文件；Jennewein arXiv1012.1868 Eq.(2),(3),(6)及Appendix B
给出同名 bucket detector 的数学规格，Tan QO 的真空/梯算子/tensor 原语有独立源码。
这已识别原同项目模型；历史默认值没有被宣称为最终发表的校准配置。

分类为既有制备/effect 责任的 bounded subordinate optical producer/readout。
原 `positiveSmoothUnifiedSource`、`SpinPair.visit10`、material row、whole-ledger、tick16→17保持。
直接消费者是本目录两个重实现和 verifier，再由 readiness 读取来源恢复及各分支真实判决。
本版 `model_source_identified=true`，`publication_configuration_identified=false`，
`production_admitted=false`；数值吻合不能自动补齐最终配置身份。

## 原量子生成器

每光学模式 N=4，基为 n=0,1,2,3；四模顺序 `(H_A,V_A,H_B,V_B)`。
`a[n−1,n]=sqrt(n)`，从四模真空生成

```text
H = sqrt(2) epsilon [sin(gamma)(a_HA† a_HB† + a_HA a_HB)
                  + cos(gamma)(a_VA† a_VB† + a_VA a_VB)]
psi = exp(-i H) |0,0,0,0>
```

相对相位固定0，gamma是泵浦平衡角，不是 r0004 的模式重叠参数。
原实际 Hamiltonian 的 sin/cos 次序与注释的态文字相反；按实际算子执行。
双方同时交换脚本 H/V 标记，第一被测端口对应仓库 V-first；测量旋转也同时转换。
零相位模型对全部角同时反号不变，规范化取第一非零角为正。
用于和论文振幅比比较的是生成态单对扇区的实际系数比
`r_one_pair=|psi[1,0,1,0]/psi[0,1,0,1]|`，另记录弱增益的 `tan(gamma)`。
不得把单对条件态当作整个脉冲状态。

本地 HWP 为 `U(t)=exp[t(a_H a_V†−a_H† a_V)]`，角 t 用弧度。
bucket click effect为 `D(n)=1−(1−eta)^n+d`，其余偏振模式取单位算子。
按 N=4 有限域验证全部 effects∈[0,1]，不切换 OR 暗计数、不饱和裁切。
真空、多对、HWP 及探测器均在同一个四模态上读出；不另加 `sA*sB` accidental。
代码里的 visibility 只有注释中的计算读出，没有外加 visibility/去相干输入。

## 输入身份分支（全部执行）

**author_defaults**：复制 Appendix A 中全部影响 CH 优化的默认配置。Alice eta=.747，Bob eta=.732，
每侧 darks=2000/s，coincidence window=.2e−9 s，laser=79.3e6/s，平衡泵浦单个 HH 设置
coincidences=33e3/s。`epsilon²=coinc/(etaA etaB rep_rate)`，`d=darks*window`。
只计算这个明确历史中心，不代造它未公布的不确定度。

其余两分支均用论文最终公开输入：74.7±0.3%／75.6±0.3%，故概率半宽为 **0.003**；
背景概率 bA=8.9e−7、bB=3.2e−7，q=.0005，保留既有 nominal box [.0004,.0006]。
该 q 盒不是统计置信区域。代码的 HH 校准强度与论文每脉冲对概率尚未同实例绑定：

- **published_gain_half**：按弱增益总对概率的 leading term `2epsilon²≈q`，固定 `epsilon²=q/2`；
- **published_native_strength**：按原代码 HH 校准强度解释 q，固定 `epsilon²=q`。

二者是明确的输入身份判别，不把其中的吻合分支自动升格为发表配置。
两公开分支各自行生成 etaA/etaB/q 的中心加8角点，合计9点；加历史中心，总计19点。
公开可见度只记录原模型计算读出及是否消费，没有添加拟合参数。

## 目标、域与搜索

保留原 `opt_CH=1`：CH=j00+j01+j10−j11−sA0−sB0；最小化1/(1+CH)等价于最大化CH。
不采用另一个 normalized-B 分支。保留原三变量镜像约束，在本版预声明有界域重放：
gamma∈[1e−6°,45°]；两个Alice角均∈[−90°,90°]。原 fminsearch 没有显式 bounds，
这些界是本版计算口径，不伪称原作者已给出的搜索界。
固定半空间表示与镜像域，不把四角自由度扩展的结果混进源代码验收。

主实现用 commuting HH/VV 源的因子分解、有限 photon-number block 的 HWP/effect 收缩；
独立实现用完整 tensor 基底、复矩阵 Hermitian 谱演化和直接振幅探测求和。
两程序分别解析本判据、生成盒点和参数；独立路径不得从主输出取输入或起点。
主26邻居模式细化；独立 Nelder–Mead，不共享概率或优化函数。
各分支中心自行做冻结粗网格，选4点并加入原代码起点[45,5,-28]；
角点分别由各实现自己的中心解及冻结固定起点细化。
数值搜索和双实现一致不声称连续全域极值的形式证明。

## 机器验收

- 先核 criterion 已进入冻结 Git commit；核来源/实现/input/output 全部哈希。
- 验证源归一、有限探测 effects、所有概率与 no-click 守恒；与单对低增益 Born 读出对齐。
- 一手 detector 正控制 `[.001,.601,.841,.937]` 必须一致；OR 形似反控制不得冒充原 detector。
- 两实现完成19点，逐点 `|Δr|≤1e−5,|Δangle|≤.001°,|ΔCH|≤1e−10`。
- 各分支各自形成分量最优包络；加原舍入 r±.0005、角±.05°。历史分支只含一个中心。
- 各自比较同一 instrument 的五个文档值；全部带内才 CONSISTENT，否则 DEVIATION。
- 不将互异配置的带并成一个通过带；三个分支均保存真实判决和身份。
- readiness 读取有效研究回执及来源恢复；原 r0003 生产回执保持，最终配置准入仍需独立绑定。
- 测试只使用原设计代码输入及合成参数，不读试次事件或 Bell 计数档案，不执行外联。

<!-- FROZEN-SOURCE-STUDY-BEGIN -->
```json
{
  "criterion_version": "nominal-source-code-r0005",
  "model_source_identified": true,
  "publication_configuration_identified": false,
  "production_admitted": false,
  "source": {"N": 4, "relative_phase_rad": 0.0, "detector_noise": "additive"},
  "author_defaults": {
    "eta_A": 0.747, "eta_B": 0.732,
    "darks_A_per_second": 2000.0, "darks_B_per_second": 2000.0,
    "coincidence_window_seconds": 2e-10, "rep_rate_per_second": 79300000.0,
    "balanced_HH_coincidences_per_second": 33000.0
  },
  "published": {
    "eta_A": {"center": 0.747, "half_width": 0.003},
    "eta_B": {"center": 0.756, "half_width": 0.003},
    "background_A_per_trial": 8.9e-7, "background_B_per_trial": 3.2e-7,
    "pair_scale": {"center": 0.0005, "box_low": 0.0004, "box_high": 0.0006}
  },
  "cases": ["author_defaults", "published_gain_half", "published_native_strength"],
  "domains": {"gamma_deg": [0.000001, 45.0], "angle_deg": [-90.0, 90.0]},
  "primary_optimizer": {
    "grid_gamma_deg": [5,10,15,20,25,30,35,40,45],
    "grid_angle0_deg": [0,4,8,12,16,20],
    "grid_angle1_deg": [-45,-40,-35,-30,-25,-20,-15,-10,-5,0],
    "keep": 4, "step_deg": 3.0, "iterations": 800, "step_stop": 1e-8
  },
  "independent_optimizer": {
    "grid_gamma_deg": [6,12,18,24,30,36,42],
    "grid_angle0_deg": [0,5,10,15,20],
    "grid_angle1_deg": [-44,-38,-32,-26,-20,-14,-8,-2],
    "keep": 4, "simplex_step_deg": 3.0, "iterations": 2500,
    "coordinate_stop": 1e-8, "scaled_objective_stop": 1e-9, "objective_scale": 1e8
  },
  "author_start_deg": [45.0,5.0,-28.0],
  "corner_starts_deg": [[15.0,4.0,-25.0],[30.0,8.0,-35.0]],
  "band": {"r_widen": 0.0005, "angle_widen_deg": 0.05},
  "tolerance": {"r": 1e-5, "angle_deg": 0.001, "CH_abs": 1e-10},
  "operator_controls_deg": [[17.0,6.0,-31.0],[33.0,-12.0,24.0]],
  "input_sources": ["author-code.txt","sources.json","../shalm2015-channel-inputs.txt","../../instrument.json"],
  "outputs": {"primary":"replay.json","independent":"independent_replay.json","verification":"verification.json"}
}
```
<!-- FROZEN-SOURCE-STUDY-END -->

本 checkpoint：恢复真实源 Hamiltonian/测量器，独立19点重放与三份不可择优判决，
签收实际改变的模型身份责任。最终 eta/q/dark 配置身份由后续来源支付，不用吻合反推。

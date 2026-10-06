# sc0001：对齐标量效率源的同次single结构检验

2026-10-02。合同、来源和每份新程序/Lean候选先提交，再执行。
公开SI计数及此前结果已暴露，本版为回顾性具名模型检验，不登记blind p-value。
旧criterion、程序、回执及统计域保持。

## 被检验的源映射

原paired HH/VV源、相位噪声、镜像角及每方两偏振共同标量损失，生成相同的局域
pre-loss photon-number law；在ηA≤ηB时，源生click满足
ηB P_A(signal)≥ηA P_B(signal)。任意合法共同源强与光子数不能消去该不等式。
Alice整窗口OR背景不少于Bob时，observed singles保持相同dominance。
该模型包含原具名qubit/phase-only以及aligned single-mode full-Fock读出。
它不包含任意Jones reference-plane map、pol/setting-dependent损失或任意多模局域读出。

kernel须从原RawKernel和实际Γ生成局域律、镜像及损失比较，不能把目标singles关系
放入SourcePrim。热bucket闭式与fullBorn等价尚无kernel证书；若先证明热读出比较，
必须明确登记这个口径，不能改称已证明fullBorn闭式。一步统计因子是null的readout。

三个具名效率映射同时保留：

1. nominal_center：原公开中心作为raw scalar transmission，c=(.747/.756)=83/84。
2. printed_probability_box：raw scalar transmission取正确±.003盒，c=.744/.759=248/253。
3. matched_calibration_box：校准为cal0001指定matched、单pulse、signal-only，t_cal=1/10000；
   K−T∈[0,2n_cal]、n_cal=1/9999，故c=(.744−2/9999)/.759。

第3支是具名校准身份下的外包域，不赋予公开实验这个校准身份。
公开k=1误差区间作为模型输入域，不宣称其本身具有95%覆盖。

## 完整trial因子与覆盖预算

固定两个mirror cells 00、11。每个完整trial置
X=1_setting [A−cB]，H0为每次conditional E[X|past]≥0。
λ=2^-k，k=1..20全部计算；因子F=1−λX非负且null下条件期望≤1。
M_n=∏F形成非负supermartingale，Ville运输到任意停止时刻，不要求iid。
相同trial的++同时计入A/B，不能把两个singles当独立样本。

对所选setting的四outcomes，因子分别为
`++:1−λ(1−c), +0:1−λ, 0+:1+cλ, 00:1`；其他setting为1。
公开完整四outcome整数直接生成log M，不需要事件顺序或读取trial档案。
采用α=.05、family=6runs×32767个15-slot非空子集×3c×2cells×20λ。
log M下界>log(family/α)上界才reject；全120项与每支结果保留，最大值只作摘要。
选择概率ε不额外加入已声明的gated null；该null的实际源/设置身份须由模型承担。

## 双实现及结论口

主实现用Decimal80的正确舍入log与上下相邻值生成有理包络；输入有理数先向外舍入。
独立实现用精确有理atanh级数、2次幂range reduction及J=100项显式余项，
输出向外60位小数，不调用主代码/数值。两方首科学回执生成后才读另一实现。
拒绝与未拒绝按每个效率域分别登记；不修改λ网格、数据、α、source或threshold找结论。

本检验的α独立于原po0003同时域，不合并宣称两个合同的整体覆盖率。
拒绝只作用于已命名的aligned scalar source bridge；不表示Born定理或NIST实验被否定。
若单分量CI相容而source contrast拒绝，两项各自的数学事实同时保留。

正控使用原null内的源/效率/背景；反控覆盖++双侧因子、wrong单位、遗漏family budget、
只选最有利λ、零期望边界、数字冒proof bool及错误实际源身份。
readiness消费具名结构研究字段，旧nominal optimum与production admission保持。
不读取trial/count archives、推送、修改publish或发送外联；root/whole-ledger/tick保持。

<!-- SC-FROZEN-BEGIN -->
```json
{
  "version": "p23-structured-contrast-sc0001",
  "public_counts": "../observable-prediction/public-observables.json",
  "efficiency_ratios": {
    "nominal_center": "83/84",
    "printed_probability_box": "248/253",
    "matched_calibration_box": "2477824/2529747"
  },
  "eta_probability_half_width": "0.003",
  "mirror_cells": [0, 3],
  "lambda_exponents": [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
  "alpha": "1/20",
  "run_count": 6,
  "slot_subset_count": 32767,
  "efficiency_model_count": 3,
  "mirror_cell_count": 2,
  "lambda_count": 20,
  "primary_decimal_digits": 80,
  "independent_series_terms": 100,
  "independent_output_digits": 60,
  "source_mapping_identified": false,
  "publication_configuration_identified": false,
  "production_admitted": false,
  "calibration_protocol_identified": false,
  "actual_source_failure_claimed": false,
  "bell_event_files_read": 0,
  "retrospective": true
}
```
<!-- SC-FROZEN-END -->

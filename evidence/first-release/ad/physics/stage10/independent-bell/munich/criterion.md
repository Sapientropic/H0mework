# mu0001：Munich 全几何、全编码互补平衡裁决

原 `positiveSmoothUnifiedSource / SpinPair.visit 10 / tick16→17` 的 source、effect、
whole-ledger 与生成后继固定。本接口是它的从属经验 producer／consumer；
直接消费者为 NIST readiness 中单独登记的 Munich 实际仪器裁决。
[方法与投影桥](source-methods.md)和[官方字节绑定](sources.json)承担来源。

## 受裁决合同

原 `Bell.probability` 与 `Bell.runtime_probability` 对全部合法单位
XZ 轴、两个原 herald 生成 `p00=p11`、`p01=p10`。名义仪器合同将这些恒等式运输为
每个事件在全部过去、当前 herald／setting 给定后的条件概率：

```text
p(x,y | past,h,a,b) = m_(x xor y)(past,h,a,b) / 2,
m_0 >= 0, m_1 >= 0, m_0 + m_1 = 1.
```

允许控制角未知、随过去适应以及 herald／setting 不均匀；herald 和两侧 setting 在测量
outcome 前生成。单时点 Lean 恒等式支付理想概率口；逐 trial 条件 null 另外包含合格
event-ready selection／readout、原排除／配对／顺序运输及该理想概率到实际仪器的运输责任。
条件分布是在官方 valid pairs 选择之后，按其原始顺序定义。
程序的 `additional_outcome_selection=false` 记录本程序完整消费 pairs，官方选择的
outcome-independent 责任由维护、激光及 CEM 的公开预声明方法合同承担。
这里不使用论文名义最优角作为逐 run 硬件命令，不拟合相位、visibility、效率、背景或容差。

## 固定输入与准入

同时消费官方 April 15 与 June 14, 2016 两份完整 ZIP；缺少一份即准入失败。
archive 字节数、MD5、SHA256、成员名与六个 header 必须和 `sources.json` 及程序固定值
一致。只接受 ZIP 中声明的四个成员，不替换运行、成员或事件段。

原 README 明确 local 行号从 header 后起算；本版对其整数索引语法保留每侧全文件固定
`offset in {0,1}`：原物理行号 `1,2,...` 等于 raw reference 加 offset。
四个两侧 offset 候选各自核完整运行；保留全部成功候选，无成功候选则准入失败。
不逐行选 offset，也不根据 E 值选候选。lab1 为分号七列；lab2 为分号六列加末尾空列；pairs 为 TAB
八列。header 字节逐字核验，所有记录必须恰为一个物理行；空行、错列、CSV 错误或
非 UTF-8 记录失败，不跳过记录。

`*_pairs.csv` 的全部 valid atom–atom 记录是分母。每行原顺序保留，必须：

- 对成功的全文件 offset 候选，引用两侧存在且从未重复使用的原 local 行；
- pair timestamp 等于 lab1 timestamp，两侧 Unix ms 时间差不超过 `100`；
- setting、result 及 lab1 herald 的 raw token 与原 local 行逐字一致；
- 每侧全部被引用 local 的 `excluded from evaluation` 共享一个 raw token。

README 的权威分母是 valid pairs，exclusion flag 没有公开 token 字典。
被引用行共享的 raw token 可为空，原值保留为 `valid_pair_flags`，不从频数推定其它值的
排除语义。未配对 local 按 raw flag 分组审计；flag、comment 与原行字节摘要保真保存。
维护、激光故障及 CEM 故障的 outcome-independent 选择由公开方法固定，不增加结果裁剪。

全部 pair 及其被引用 local 的 modeled setting、result、herald 字段为非空 ASCII、无首尾
空白。每个 run 的每个角色至多两个 raw token；空结果或第三个 token 失败。
仅出现一类标签及空 context 合法。未配对 local 的 modeled 字段允许为空或任意值，
时间也按原字段保存；pair 和引用行的 Unix ms 接受有限非负十进制／科学记数字串，
以 `Fraction` 精确比较相等与 ±100ms，不浮点或取整；row reference 仍为严格整数。
所有未配对原行号 RLE、raw flag／comment
分组和完整原字节摘要保留审计，不进入评分分母。
空 pairs 运行的统计状态为 `inconclusive`。
本地全部 state-measurement attempts 不改名为全部原子激发尝试。

## 编码与精确评分

herald、Alice setting、Bob setting、Alice result、Bob result 分别将已出现的一或两个 raw token
按 ASCII 字节字典序编码为 `0,1`。字典只给有限编码，不赋予 `Psi±`、角度或 `up/down` 身份；
不使用频数、相关符号或检验结果选字典。全部 `2^5=32` 个 global 二元重命名产生相同
逐 prefix E 值：context 仅被置换，outcome 翻转仅交换同一 context 的两个计数。因此该
确定性字典消费完整有限编码歧义，没有结果后择模。

每个 run 独立初始化三个 wealth 为 `1`。joint wealth `EJ` 对每个 `(h,a,b,c)` 保存过去的 `n_0,n_1`。
在评分当前 `(x,y)` 前，为当前 `(h,a,b)` 的两个 `c=0,1` 都固定

```text
q_c(x) = (2 n_x + 1) / [2(n_0+n_1)+2].
e_t(x,y) = 2 q_(x xor y)(x) = (2 n_x + 1) / (n_0+n_1+1).
EJ_t = EJ_(t-1) e_t.
```

随后只更新实际 `(h,a,b,x xor y,x)` 的计数。全部 pair 都评分；当前 parity 参与整个
joint factor，不能当作事后筛选条件。给定过去，两个 parity 的 `q_c(0)+q_c(1)=1`，故
条件期望为 `sum_c m_c [q_c(0)+q_c(1)] = 1`。

原合同还给出两侧每 trial 的条件 marginal `1/2`。另以全部过去的 Alice／Bob 各自两个
pooled 计数，使用相同 Bernoulli Jeffreys `2q` 更新 `EA`／`EB`；两个 factor 的条件期望
分别为 `1`。固定主 e-process 为 `E_t=(EJ_t+EA_t+EB_t)/3`，权重在事件解码前固定。
这是三个同起点 e-process 的等权混合，不将相关的 wealth 相乘。不要求 trial 独立同分布。
回执同时保三个 component 的终值与两侧 pooled 计数；全部主摘要和阈值针对该固定 mixture。

每个 run 的 anytime alpha 为 `1/40`，阈值为精确 `40`；两 run 联合预算为 `1/20`。
任一 run 的全部原序 prefix 中 `E_t >= 40`，共同合同为 `rejected`；否则为
`not_rejected`；没有有效 pair 的运行返回 `inconclusive`。
跨阈值后继续评分全部记录，不据结果停止、删行或变更 alpha。
乘积与全部阈值比较使用标准库 `Fraction`，不以 float／log 作科学决定。
大有理数以 canonical numerator／denominator 的 bit 长度、SHA256 和 48-bit 精确 dyadic
包络保存。逐 prefix 摘要只包含 `E_1..E_n`：每个正的 reduced Fraction 依次编码为
`uint64BE(length(numerator_bytes)) || minimal unsignedBE numerator ||
uint64BE(length(denominator_bytes)) || minimal unsignedBE denominator`，连接后取 SHA256。

## 首次执行与 claim

科学合同、来源和程序的实际路径必须已提交且 clean，才允许解码事件。
`primary-attempt.json` 在事件解码前独占创建，`primary-first.json` 在成功或失败后独占
创建；已有任一文件即拒绝再次启动。首份回执不覆盖。准入失败产生明确失败回执，
不形成统计 verdict。源码修复与后续版本保持不同版本／回执身份。

`rejected` 拒绝上述共同 balanced-complement 名义仪器合同；`not_rejected` 表示预声明
裁决未拒绝它，不认证完整 joint 分布、底层理论或实际硬件 identity。原理论构造的
数据独立性保持。公开结果邻接曝光已记录，不声明人类认知未暴露。

<!-- MUNICH-MU0001-FROZEN-BEGIN -->
```json
{
  "version": "stage10-munich-mu0001",
  "source": "positiveSmoothUnifiedSource",
  "root_visit": 10,
  "current_tick": 16,
  "next_tick": 17,
  "controller_advance": false,
  "runs": ["2016-04-15", "2016-06-14"],
  "null": "conditional_balanced_complement_all_unit_XZ_axes_both_heralds",
  "encoding": "per_run_per_role_ascii_byte_sorted_at_most_two_raw_tokens",
  "finite_global_label_maps": 32,
  "selection": "all_official_pairs_strict_original_local_row_join",
  "per_lab_global_row_offsets": [0, 1],
  "pair_window_ms": 100,
  "valid_pair_flag": "per_lab_constant_raw_token_including_empty",
  "predictor": "context_herald_settingA_settingB_parity_Jeffreys_past_only",
  "per_run_alpha": "1/40",
  "familywise_alpha": "1/20",
  "per_run_threshold": "40",
  "e_process": "equal_mixture_joint_Alice_marginal_Bob_marginal",
  "component_weights": ["1/3", "1/3", "1/3"],
  "anytime": true,
  "exact_prefix_arithmetic": "fractions.Fraction",
  "score_all_records_after_crossing": true,
  "empirical_fit_parameters": 0,
  "actual_angles_required": false,
  "physical_label_dictionary_required": false,
  "hardware_identity_validated": false,
  "full_joint_validated": false,
  "theory_validated": false,
  "human_outcome_unexposed_claimed": false
}
```
<!-- MUNICH-MU0001-FROZEN-END -->

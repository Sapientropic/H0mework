# cp0003 独立源与联合响应数学审查

`joint_response.py` 的完整 gain-cap profile通过独立审查：原 source 的乘积强口把四个局部响应共同约束到八个 context；八 context 共用一个全局 likelihood 分子，生成原整个 parent 置信域的同时必要资格。实际端点由冻结后的独立数值程序验收。

真实 `SettingFamily` 只存 `alice : Bool → CompactReadoutEffect` 与 `bob : Bool → CompactReadoutEffect`。local effect 只依赖本侧 setting，两个 herald 共享。旧 `ReadoutResponseBounds.centered_correlation_product_bound` 及独立消费者 `actualMomentResponse` 对任意 family、herald、双方 setting 已证明 `|C−mu_A*mu_B|≤g_A*g_B`，其中 C 是原四 outcome 的 signed moment。旧 source/current/next moment 等式和完整原 source image 保持。控制状态为 `positiveSmoothUnifiedSource`、`SpinPair.livingRoot / visit10`、`materialEntry / generatedRows row0`、tick16→17；该口属于从属逆读，`controller_advance=false`。

对有序 cap `c=(A0,A1,B0,B1)∈[0,1]^4`，null `g_i≤c_i` 给出 `g_Aa*g_Bb≤c_Aa*c_Bb`。id0001 同一个 parent 置信域的 bias 四角积围住真实 `mu_Aa*mu_Bb`，所以每个 context 的 `p_even=(1+C)/2` 必在代码给出的 radius=`c_Aa*c_Bb` 裁切 band 内。四个 cap 同时成立的全部 source 点均被该 relaxation 覆盖，包括 cap 为零的情况。

固定 parity 质量 p 后，组内两个 cell 的经验频率最大化 conditional likelihood。parity likelihood `p^n_even*(1−p)^n_odd` 在 band 上的 exact maximizer 是经验 parity MLE 的 clamp。八个 context 各自最大化只放宽了 source 的联合约束，所得分母不小于任意 null source 点的真实分母。因此同一个 Dirichlet(1/2×4) 全局分子给出 `joint_profile(c)≤E_full(q)`。实现将一次 `FullProfile.mle_log` 加上八项 parity 损失；clamp 等于 MLE 时跳过精确零损失。

增大任一 cap，涉及的四 context band 扩张，其余 band 保持，最大分母非减，profile 非增。原 `E=E_full/2+E_A/6+E_B/6+E_complement/6<40` 蕴含 `E_full<80`，故 `joint_profile(c)≥80` 排除整个闭 lower orthant `0≤g_i≤c_i`。这是一枚原置信域的确定性必要检查，四维 cap、三 ray 和两 run 共用原预算 `1/20`。

三条预声明 ray 逐分量非减；uniform 的 radius 为 t²，Alice/Bob ray 的 radius 为 t。下端排除分别意味着四个 gain 的最大值、本侧两个 gain 的最大值严格大于 t。它不把本侧两项各自都读成大于 t。36-bit bracket 定位 relaxation 阈值，不宣称真实 source 极值锐性；profile 通过保留为必要资格，完整 joint 相容性仍由原消费者支付。

每个 context 显式要求两 parity 观测计数均正；缺一个或两个 parity 时拒绝本计算资格。若 cap/bias band 强制 p=0 或 p=1，已观测的另一 parity likelihood 为零，profile 记为无穷，没有 epsilon 替代。Directed 两端分别核 `logprofile≥log80` 与严格 `<log80`，只有真正分居阈值两侧且 gap≤2^-36 才输出 bracket。

`witness_caps` 的整数平方根向上外包满足 `g≤cap`，含 g=0、g=1 与负 u/z 坐标。形似控制的四 cap 取 cp0002 下界最大值并向上取整至 10^-6，逐项仍需落在旧 gain 区间；其联合通过或拒绝由实际 profile 如实登记。这些必要资格保持原 regular 双尺度纤维、canonical 代表及 actual-label 身份的语义，硬件唯一性字段保持 false。

验证：`python3 -m unittest -v test_joint_response.py` 的 7 个合成控制通过；独立 Fraction 四 cell 公式核验48个泛型 source lower-orthant 分母覆盖、3次完整八 context likelihood、31次嵌套、4个零 support 边界、16个平方根外包和1次 box 向上取整。旧 `response_bounds_certify.consume()` 成功，全部源口复用标准三公理。该数学审查使用合成输入；实际计数及端点另由冻结后的双实现支付。

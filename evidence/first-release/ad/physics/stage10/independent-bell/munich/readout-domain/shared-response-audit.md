# cp0002 独立源与统计逻辑审查

`shared_response.py` 的四 context 联合响应 profile 通过源与统计逻辑审查：它消费原整个 parent 置信域，生成同一局部响应的同时必要下界，没有增加检验预算。审查覆盖源码中的数学机制；实际端点由冻结后的独立数值程序验收。

真实 `SettingFamily` 类型只有 `alice : Bool → CompactReadoutEffect` 和 `bob : Bool → CompactReadoutEffect`。effect 只依赖本侧 setting。同一 run 内固定 Alice setting 时，两个 herald 与两个 Bob setting 确实共享同一 gain；Bob 同理。已冻结的 `centered_correlation_response_bounds` 对任意 family、herald、双方 setting 给出 `|C−mu_A*mu_B|≤g_A,g_B`。原 source、current、next 的 correlation moment 等式已由旧 `ResponseBoundsCertification` 支付，沿 `positiveSmoothUnifiedSource`、visit10、ledger row0、tick16→17 消费，`controller_advance=false`。

令该共享响应的 null 为 `g≤G`，四个相关 context 均满足 `C∈[productLower−G,productUpper+G]`。bias 四角积来自 id0001 对同一个 parent 置信域的区间；因此 `p_even=(1+C)/2` 位于代码给出的裁切 band。把各 context 的 bias 产品与 parity 质量独立放宽，仍覆盖每个合法低响应 source 点。

四 cell likelihood 按 parity 质量和组内 conditional likelihood 分解。固定 parity 质量时，组内经验频率给出 exact MLE；band 内的 parity MLE 是 `clamp(n_even/N,lo,hi)`。其余四 context 取无约束四 cell MLE。八个 context 的同一 Dirichlet(1/2,1/2,1/2,1/2) 分子除以此最大分母，所以 `profile(G)≤E_full(q)` 对每个 source null 点成立。

代码先放入一次全部八 context 的 `FullProfile.mle_log`，再加四项 parity MLE 损失。没有重复使用全局分子。`G` 增大时四个 band 同时嵌套扩张，最大分母非减，profile 非增。parent 的 `E=E_full/2+E_A/6+E_B/6+E_complement/6<40` 蕴含 `E_full<80`；因此签收下端 `profile(Glo)≥80` 排除整个 `0≤g≤Glo`，四角色及两 run 仍共用原预算 `1/20`。

两 parity 计数为正是此实现显式检查的输入资格。裁切最大值为 0 或 1 时，已观测 parity 的 likelihood 为零，profile 为无穷；实现没有 epsilon 替代。Directed 运算按下端 `logprofile≥log80`、上端 `logprofile<log80` 签收。36 次有理二分的 gap≤2^-36 定位这个 relaxation 的阈值；没有声称完整 source 置信域的真实 gain 极值达到此处。

最终 `G=max(Glo,legacyGainLower)` 合并两枚已支付的必要界，保证逐项不弱于 cp0001。对 `mu∈[ML,MU]`，canonical 范围为 `g∈[G,1−min|mu|]`、`e0∈[max(0,−MU),(1−G−ML)/2]`、`e1∈[max(0,ML),(1−G+MU)/2]`，均由旧合法 source cone 与 canonical channel 公式推出。严格改进应由冻结后的八个角色逐项比较登记；actual ideal-label 身份与硬件唯一性不由这些范围选择。

验证：`python3 -m unittest -v test_shared_response.py` 的 7 个合成控制通过；另以独立 Fraction 公式核了四个非对称／含零 cell 合成 profile 的 source-null 分母覆盖、24 次 band 嵌套、363 组带符号 bias 的误率输运。旧 `response_bounds_certify.consume()` 已成功，公理集仍为 `propext`、`Classical.choice`、`Quot.sound`。本审查没有打开实际计数、试次事件或运行科学 first。

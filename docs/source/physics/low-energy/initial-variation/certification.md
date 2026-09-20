# 原共同解族的真实初值变分认证

**Verdict: certified。** 2026-09-19，独立核验正式候选
`Evolution/{Variation,VariationEstimate,VariationDerivative}.lean`。
候选未修改；未发现余项假设未消去、正负时间漏项或源 Jacobian 替换。

这是原共同非线性解族的 **initial-derivative producer / variational readout**。
原 source/action、visit 10 / tick 16 / materialEntry 及 visit 11 / tick 17 后继保持；
本组不新增 runtime authority。

## 精确公开口与源对象

令 `x₀ = Evolution.seed 0`、`J = fderiv ℝ generator x₀`。
对任意已生成的 `UniformDevelopment x₀` family，以及其共同正时间区间内每个 t，
`initial_derivative` 证明

`HasFDerivAt (fun initial => family.curve initial t) (exp (t • J)) x₀`。

导数是对全部七维 State 初值增量的 Fréchet 导数。
`initial_fderiv` 读回 Lean 的实际 fderiv；`initial_variation_evolves` 再证明
这个实际初值导数应用任意 direction 后，对真实时间满足 `V′(t)=J(V(t))`。
其生成输入是已签收的共同解族与原光滑 generator，没有外供变分解或导数证书。

Audit 从 `uniformDevelopment_exists (seed 0) (seed_admissible 0)` 实际生成同一个 family，
共同消费所有球内初值的原九场解及上述初值导数。family 的正初值球使该
`HasFDerivAt` 成为通常的邻域导数；family 在球外的任意定义不影响这一 mouth。

## 原相位漂移与同一个 J

`background t = x₀ + t • Pi.single 6 frequency` 使用原已证漂移。
私有 backgroundSolution 由原 `Spectrum.background_orbit`、真实 Admissible 相位不变性
和时间光滑性构造；`uniform_background` 用已签收的重叠唯一性将 family 的中心轨道与它识别。

实际位移 `d(t)=family.curve initial t−background t` 经原
`generator_phase_translation` 得到精确自主方程
`d′(t)=centeredGenerator(d(t))`。
`centeredGenerator z=generator(x₀+z)−phaseDrift`，其原点值为零且真实导数仍为 J。
没有冻结错误的静态背景或改变原时间。`linearFlow` 是同一个连续线性算子的 Banach 代数指数，
其时间导数次序经原 Mathlib 指数定理核验为 `J(exp(tJ)v)`。

## 完整小 o 与双向时间估计

`centered_remainder` 由源生成器的真实 HasFDerivAt 得到
`centeredGenerator(z)−Jz = o(‖z‖)`。
证明初值可微性时，对任意 ε>0，先取
`Q = dependenceConstant + 1 > 0` 与正放大因子

`A(t) = Q/(‖J‖+1) · (exp((‖J‖+1)|t|)−1) + 1`。

以 `η=ε/A(t)` 选择源 Taylor 余项邻域 δ，再把初值增量限制在
`‖h‖ < min(initialRadius, δ/Q)`。
共同 Lipschitz 界保证整个积分时间段的真实位移满足 `‖d(s)‖≤Q‖h‖<δ`，
故每个中间时刻的非线性余项都由 `η Q ‖h‖` 控制。

`linearError` 是实际位移与 `exp(tJ)h` 的差，初值为零，真实导数分解为
`J(linearError) + centered remainder`。
`norm_linearError_le` 实际消费 Grönwall 定理，取 `K=‖J‖+1`，
得到最终误差不超过 `η(A(t)−1)‖h‖≤ε‖h‖`。
这完成整个 State 邻域的 Fréchet 小 o 条件；Lipschitz 界承担轨道管控制，
可微性由后续余项极限产生。

负时间使用 `sign · s`、`s∈[0,|t|]`。
链式导数中的 sign 保留到范数，再由 `|sign|=1` 消去；
`|t|<timeRadius` 支付整个正/负时间段的定义域。
时间零也包含在同一估计中。条件性 Grönwall helper 的 remainder premise 在最终
`initial_derivative` 中由上述源小 o 与整段位移控制构造，没有留给调用者。

`initial_variation_evolves` 使用共同开时间区间上的 eventual equality，
把 `fderiv(initial ↦ family.curve initial t)` 的真实时间导数与指数流导数识别。

## 直接消费者与严格结果

[Audit.lean](Audit.lean) 有六个公开消费者：

- 由原 seed 实际生成同一个九场 family，并消费其全部时间的真实初值导数；
- 显式消费 `±timeRadius/2` 两个时间；
- 消费原 family 的完整 Taylor 小 o，及实际初值导数的源 Jacobi 时间方程；
- 核验 t=0 的导数为恒等，并将原两个非零 gauge/radial 谱方向接到实际初值导数的初始变化率。

三候选及 Audit fresh 执行 `lake env lean --trust=0 -DwarningAsError=true`，
全部 **EXIT 0**；三源 `.olean` 同次生成，无宽构建。
26 个候选公开声明加六个消费者，共 **32 项**传递公理检查，
全部属于 `{propext, Classical.choice, Quot.sound}`。
无 `sorry`、`admit`、`native_decide`、自定义 axiom 或新增信任绕过。
mouth lint 只提示仓库惯用的 `autoImplicit false`。
真实命令、退出值及公理见 [lean-audit.log](lean-audit.log)。

签收范围是共同原解族在固定 `seed 0` 的全方向初值 Fréchet 导数及其时间演化，
不是整个初值球上已证明的 C¹ 依赖，也没有延伸旧逐初值选择轨道在各自条带外的语义。
未改候选，未 stage 或 commit。

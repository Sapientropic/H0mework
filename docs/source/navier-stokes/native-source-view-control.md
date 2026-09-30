# 同一发生的窗口热物理实现

本卡记录源生成的正热物理合同与同源零热极限；[原生全阶 active card](../../handoffs/navier-stokes-native-regularity-active-route.md)管理其签收状态。
从属表示由原 root 授权，直接承担最终物理消费者。控制对象、初态和时钟如下定义。

## 原输入与完整表示

输入是既有 `NativeUnifiedCompleteSource.source initial t : FullSpace`，同时保留物理 L²
速度与完整 H⁻² 应力。原 history 的全部整数波、九分量、零频及原 R 点值仍在原载体上。

`SourceView.Window.Source` 从固定归一化光滑 bump 生成 g；其支撑在 `[-2,-1]`，
`g≥0`、`∫g=1`。令 S 为原完整输入，Hₕ 为同一 νλ 热乘子对 U／σ 的作用：

```text
W(t) = ∫ g(s) S(t−s) ds，Vₕ(t) = Hₕ W(t)，h>0。
```

原 S 的可测性与原预算直接生成 W 的全部强时间 jets。第 n 阶范数界是
`(∫‖g⁽ⁿ⁾‖) · budget(initial)`，没有 caller Smooth、矩预算或目标可积性。
这是原 source 的进一步生成；没有将尚未发生的整条未来表称为当前 occurrence 的已有字段。

## 实际作用与物理消费

`Window.Write` 消费原完整 writer 与有限窗口 Fubini，得到每对 `a,b≥−1` 的实际
Bochner 写入；每个 `t>−1` 的实际导数由同一完整动量给出。
`Window.Evolution` 对全部有限阶生成未加权物理速度字 vₙ，并证明
`embed(vₙ₊₁)=momentumCLM(Wₙ)`。`Heat.Carrier` 逐全频证明

```text
momentumCLM(Hₕ S) = Hₕ(momentumCLM S)，
R(Hₕ S) = Hₕ R(S) + Hₕ Q(U) − Q(Hₕ U)。
```

原三通道 native RHS 与同一热乘子交换；第二式的二次交换子属于生成的完整修正。
`Heat.Evolution` 将全部实际作用字、完整 writer 和原宏 next 一起送到 Vₕ。
`Window.Physical` 的有限 F 口验证真实物理 curl、统一方向微分、原 native RHS 和端点
积分；保留 `F∪(F+F)` 出频。有限 F 在这里是方程的观察口。

`Heat.Multiplier` 对原热乘子生成全频任意阶 lp 算子，其预算为
`n! exp(4a)/aⁿ`，`a=ν(2π)²h>0`。`Spacetime.Fourier` 用可和频率主控和真实时间
字递归合成普通四维 C∞。`Spacetime.Velocity` 认回既有完整 `spatialField`；
`Stress` 控制完整复／实应力张量；`Residual` 从原 `R(Vₕ)` 的全部系数合成受控场。
其 `torusField_fourier` 逐整数波、九分量及零频读回同一个 R，完整 Cauchy 乘积保留。
U／σ／R 的任意有限阶导数均获得紧时空域上的全 p 控制，包括 ∞。

## 原 canonical 配对

`Window.PairingMoments` 将任意完整 Finsupp 测试写成
`covariance_test = stressTest − ‖meanTest‖²`。原 Data 的正性与 Jensen 方差共同进入
`PairingAverage`，生成 W 自身的 canonical Data；四 current 精确等于同一 g 对原
canonical current 的平均，baseline 由 `∫g=1` 保持。

`Heat.GaussianPhase` 从真实空间平移的 Gaussian 特征函数认回原 heat。
`TranslationData` 消费原物理 L² 平移及原 GNS 相位 Gram；`PairingAverage.sourceData`
再自动生成 Vₕ 的 reality／完整正协方差。primal／dual 仍由原 canonical 构造产生，
完整修正与同一四 current 同时读回。

## 原 root 的接收

`Root.Carrier` 的 `CarrierAt` 保存 exact occurrence 的完整 compiler ledger，以及
由同一 initial 进一步生成的完整 history。有限 current 使用原 elapsed clock；cofinal
与 Galerkin 使用原 accumulation clock。view 是这个 history 的固定窗口及原热作用。

具体 `component` 经 `withProjectionCoface` 进入原 authority inventory。
`Root.Control.authorityCarrier` 从实际 `projectionOutcome` 消元取得载体；
`Root.CompleteControl.authority_all_order_Lp` 直接消费其完整视图 U／σ／R。
原 whole-ledger 不变，living 的 generated-next current 与原 current 保持 HEq。
有限 next 按原 contact 时间运输整个 view；cofinal／Galerkin 的这份坐标保持不变。
`Root.Pairing` 将相同 next 等式送到完整 canonical Data。

`Root.Runtime` 将固定 `stackedShortCurrent`、正热分辨率 h=1 与该 projection 安装为具名
`NativeViewRuntime.facade`。`carrier` 从实际 runtime readout 消元；`activated_readout`
同时消费 `readoutAt_factorizes`、原 whole-ledger 和原 generated next。通用生成定理仍对任意
原 initial、任意 h>0 有效，具名消费者无需外部提交 Smooth、目标预算或实现证书。

## 物理初态、实验室时钟与预测

在原 current 的累计物理时刻 o，令本地时间为 t≥0，实验室时钟为 `ℓ=o+2+t`。
`Root.Preparation` 证明 dℓ/dt=1；测量 Vₕ(o+t) 只取原历史在 `[ℓ−1,ℓ]` 的值，
并证明该区间上的样本相同就产生相同完整测量。新初态为这台仪器在 t=0 的完整输出，
即 `Hₕ∫g(s)S(o−s)ds`，同时生成 U／σ／R 及 canonical Data。
两单位是一次制备偏移；下一拍沿原 contact／macro 步长推进，不重复添加偏移，窗口可以重叠。
h 是空间热分辨率参数，不替代实际物理时钟。

`Prediction.Rows/Whole` 从完整 σ 的投影散度和原 ν 热作用生成独立 Duhamel 写入：

```text
embed Uₕ(t) = Hₜ(embed Uₕ(0)) + ∫₀ᵗ H₍ₜ₋ₛ₎ P div σₕ(s) ds。
```

源口生成右侧；`Root.Prediction` 证明其物理 L² 解码唯一，且在原下一拍时刻恰写入下一
preparedInitial 的速度。预测输入是新初态与同源生成的完整应力历史；forcing 不含未来
平均速度。原 source 提供数学上的生成，不把未来测量称为已经观察到的数据。

## 实际能量、作用与最终消费者

`Energy.Content` 将同一 measured pair 的零频 trace 写成
`Etotal=‖Uₕ‖²physical/2 + Efluctuation`。canonical GNS Gram 保证涨落能非负；
总能量由原 source budget 统一控制。这里的速度能量经 Parseval 认回完整实物理场。

`Energy.Evolution/Work` 用真实强时间率证明

```text
dEresolved/dt = WR − νD，D = Σₖ λₖ‖Uₕ,k‖² ≥ 0，
WR = Σₖ ⟪P div Rₕ,k, Uₕ,k⟫ℝ。
```

全频做功级数由原 H¹／H⁻¹ 配对证明可和；R 是同一完整 σ 减去 Q(Uₕ) 的 canonical
修正。能量积分由实际动量作用、非线性消去及 FTC 支付。

`Spacetime.Time/Curl/Equation` 合成全部物理时间字及真实 curl：实际 ∂tUₕ 等于完整
momentumField，普通方向微分和空间 curl 进入原 Fluid 算子；任意有限 F 的三个 native
通道恰是该涡量行的实际导数。无限频率、完整九分量应力及零频始终保留。

`Consumer.Physical.read` 直接消费具名 runtime payload，输出 U／σ／R／curl U／∂tU。
`all_order_control` 给这些实际输出在任意紧时空域上的任意有限阶 ordinary 导数和全部
Lp（含 ∞）；`forecast` 消费上述 Duhamel 预测。`controller_write_back` 在同一 tick
交付整账、完整下一态、实验室时钟、预测的下一初态及实际做功能量写入。
`Consumer.Next.pairing_next` 将整个 canonical Data 一起运输。
具名 Nat runtime 表示全部有限 visits；cofinal／Galerkin 与宏 next 的完整表示等式由
`Root.Carrier/Pairing/Preparation` 及 `Spacetime.Equation.physical_next` 单独给出。

合同固定这份正分辨率物理实现，不取 h→0 的统一界，也不要求新旧速度逐点相等。
标准 NS 固定源分支保持其独立合同。

## 同一个完整源的零热极限

`Heat.Zero.fullHeat_zero` 精确给出 `fullHeatCLM ν 0=id`；原全频 lp 支配与乘子的连续性
生成强收敛。相同收缩作用经紧集等度连续性给完整载体上的紧集一致恢复。

`Heat.WindowZero.jet_uniform_on_compact` 将每个固定时间阶 n 的 `HₕW_n` 在任意紧时间集上
一致送回 W_n。这里 U 使用真实物理 L²，完整 σ／R 使用 H⁻²；零频和全部九分量保持。
连续二次 mixedCLM 使 R 同时恢复，原 momentumCLM 给 H⁻⁴ 的一致作用恢复，原完整 native
RHS 在每个固定有限观察口一并恢复。原 jet 预算对全部 h≥0 一致。

这份极限保留同一未加热 W 和真实时间字，不依靠另一个固定正尺度。普通空间全阶的
零尺度消费是更强的命题，其当前生成责任只见唯一 active card。

## 未热源的物理空间控制

`Unheated.PrefixPayment` 将原第一张 receipt 的耗散与其后全部 kinetic-dissipation payments
拼成与 micro prefix 长度无关的预算。`MacroGradient` 对实际有限波段的时间积分穿过
原 accumulation，再消费 recovery core 的黏性账户；`GlobalGradient` 沿原 NativeReachable
有限宏历史与同一 terminal trajectory 拼出任意有限原时间区间的梯度账户。

`WindowJensen` 在原 `[-2,-1]` 概率窗逐行消费 Jensen；`WindowGradient` 将每个有限波段的
界交给完整频率求和。对任意时间阶 n 和 t≥−1，原 W_n 满足

```text
Σₖ |k|² |Uₙ,k(t)|² ≤ kernelCeiling(n) · globalGradientBudget(initial,t+2)。
```

预算来自原发生；没有输入 H¹、正热尺度或预设可积性。结论是每个时间 jet 的物理 H¹。

`StressProduct` 用完整卷积的加权 Cauchy 与可和频率核，生成 H¹×H¹ 的无权张量 ℓ²
乘积。`WindowStress` 对原 U 的有限投影先作完整二次乘积，原梯度时间账统一控制其窗口
积分，再由原 `stress_ae` 和完整行极限得到同一 σ_n。该步骤保留所有九分量与零频。

`WindowResidual` 从这些 σ_n 减去同一 W 的 binomial 混合时间字，逐行认回实际 R 的
普通第 n 阶时间导数。σ／R 的无权 ℓ² 系数都经 Fourier 读回真实 T³ L² 张量场，并有
显式源预算。原 H⁻² 强时间 jets 因而得到忠实的物理 L² 实现；这里未将新 L² 曲线自身的
强求导作为附带结论。

`Unheated.Energy` 直接将 W 的 H¹ 与其实际 L² 时间率代入原完整动量和 R：
R 的投影散度在 H⁻¹ 中可读，与原梯度的配对使全部做功级数可和。真实物理动能满足
`dE/dt=WR−νD`，区间积分恰为两个原 W 物理 L² 动能的差。
这条能量链不借用正热 H¹ 界；初态、窗口、原时间区间保持。

## 未热源的完整作用与净矩支付

原全历史 H⁻¹ writer、完整逆对分解、实际二次／三次原材料逼近，以及原 standing 的
有符号谱与真实付款边统一预算，统一见[未热原源机制](native-unheated-source-action.md)。

## 窄验收与源码

最初五份表示候选按各自 scope 验收；以下是分批计数，不合称全目录 aggregate。

| 批次 | 手写根／原始模块条目 | 完整 type/value 闭包 | 可读 opaque |
| --- | ---: | ---: | ---: |
| 窗口作用四模块 | 50／81 | 60,258 | 45 |
| 热空间矩两模块 | 22／31 | 37,702 | 27 |
| 窗口配对与时空场九模块 | 124／202 | 60,705 | 45 |
| 原 root 与作用七模块 | 90／154 | 64,804 | 47 |
| 热 canonical 配对三模块 | 48／63 | 63,174 | 47 |

候选与生产分别通过默认 heartbeat 的 `--trust=0 -DwarningAsError=true`。
全部 type／value、原始模块条目多重集、完整依赖边及数学闭包对应；仅标准三公理，
无 unsafe／partial／缺失实现。四个模块自动命名的局部 measure 实例及其证明子项按
实际模块归属一一对应，不使用通配豁免。

- [Window/Write.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Window/Write.lean)
- [Heat/PairingAverage.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Heat/PairingAverage.lean)
- [Spacetime/Residual.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Spacetime/Residual.lean)
- [Root/CompleteControl.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Root/CompleteControl.lean)

物理交接另有五份独立证书，使用同一严格验证与生产对应流程：

| 批次 | 手写根／原始模块条目 | 完整 type/value 闭包 | 可读 opaque |
| --- | ---: | ---: | ---: |
| 初态与运行时两模块 | 39／58 | 63,862 | 47 |
| Duhamel 预测三模块 | 28／40 | 60,009 | 45 |
| 物理时间／curl／方程三模块 | 44／65 | 64,464 | 47 |
| 能量三模块 | 46／70 | 64,045 | 47 |
| 最终消费者五模块 | 57／72 | 65,500 | 47 |

候选输入生成、实际作用和下一状态对应全部独立签收；完整 moduleData 保留本模块触发的
惰性生成方程，不以 namespace 过滤。最终消费者的全部手写声明均能从公开消费口到达。

- [Root/Preparation.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Root/Preparation.lean)
- [Root/Runtime.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Root/Runtime.lean)
- [Root/Prediction.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Root/Prediction.lean)
- [Spacetime/Equation.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Spacetime/Equation.lean)
- [Energy/Work.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Energy/Work.lean)
- [Consumer/Physical.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Consumer/Physical.lean)

零热两模块独立认证及生产 type/value、原始 moduleData 多重集与完整依赖对应通过：
23 个声明、59,889 项完整闭包、45 个可读 opaque，仅标准三公理，无异常信任项。

- [Heat/Zero.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Heat/Zero.lean)
- [Heat/WindowZero.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Heat/WindowZero.lean)

未热物理控制按三份独立证书验收，生产晋升逐原始发生多重集、type/value 和完整依赖对应：

| 批次 | 手写根／原始模块条目 | 完整 type/value 闭包 | 可读 opaque |
| --- | ---: | ---: | ---: |
| 原梯度账户与窗口 H¹ 六模块 | 61／85 | 59,651 | 45 |
| 未热实际能量一模块 | 15／18 | 67,533 | 47 |
| 完整 σ／R 物理 L² 三模块 | 65／98 | 59,922 | 45 |

默认 heartbeat、strict trust 0 与 warningAsError 通过；数学证明闭包仅标准三公理，
无 unsafe、partial 或缺失值。H¹ 原始模块登记另含精确孤立的编译器递归替代
`NativeUnheatedGlobalGradient.pathBudget._unsafe_rec`：仅自身入边，不可达任何手写数学根；
其 kernel 定义使用 `NativeReachable.brecOn`，生产对应保留这一隔离事实。
H¹ 的 `band.eq_1` 两次原始发生均保留；σ／R 的局部 Haar 实例及其证明子项按模块归属
逐符号对应。十模块共 1,499 行，每个文件不超过 209 行。

- [Unheated/GlobalGradient.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/GlobalGradient.lean)
- [Unheated/WindowGradient.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/WindowGradient.lean)
- [Unheated/WindowStress.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/WindowStress.lean)
- [Unheated/WindowResidual.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/WindowResidual.lean)
- [Unheated/Energy.lean](../../../SaturationMonoid/NavierStokes/SourceAction/FullOrder/SourceView/Unheated/Energy.lean)

完整原应力分解及净矩账户的分批独立验收见[未热原源机制](native-unheated-source-action.md#独立验收与源码)。

# Archive: Navier–Stokes Source-Native Turbulence Total Evolution

> **冻结 checkpoint，非当前实时 route。**
>
> 本责任于 2026-08-10 首次签收。当前 `main` 已把当时的公开 resolver 强化为 sealed、
> zero-information 接口；NS 的实时责任见
> [native clock active route](../handoffs/navier-stokes-native-clock-active-route.md)，框架责任见
> [framework active route](../handoffs/living-law-framework-active-route.md)。

## 当前主线保留的最终机器合同

```text
arbitrary GeneratedWholeRestartCurrent ν
→ source-owned next / run over every finite stage
→ fixed-root boundary inquiry and exhaustive old/revised disposition
→ old global physical evolution
  ⊕ rooted failure + minimal-coface T_native evolution
→ exact Fourier / physical / flux / Duhamel law
→ native write + recovery next
→ re-enter the same GeneratedWholeRestartCurrent grammar.
```

当前公开总入口是：

```lean
sourceGeneratedNativeBoundaryReachabilityAnswer
  (initial : GeneratedWholeRestartCurrent ν) :
  SourceGeneratedNativeBoundaryReachabilityAnswerAt initial
```

它只接收 `initial`。elapsed disposition、root inquiry、old/revised branch、global trajectory、
revised occurrence、native law 与 recovery 均由同一 source 生成。answer 的 branch coordinate和
constructors保持 private；下游只能经 `fold` 消费：

- old branch生成 `GeneratedWholeGlobalPhysicalTrajectory initial`；
- revised branch生成 exact conditional occurrence与
  `SourceGeneratedNativeTurbulenceLawAt initial generated`。

2026-08-10 checkpoint中的历史入口名是 `sourceGeneratedNativeBoundaryResolution`；当前接口不是
它的缺失，而是后续 provenance hardening后的替代与加强。

## 已闭合的权威证明链

### 任意 source 与逐拍 native evolution

- `GeneratedWholeRestartCurrent.next`把本拍 actual contact写成下一枚同型 current；receipt、duration
  与positive contact由source生成。
- `GeneratedWholeRestartCurrent.run`对任意 `Nat`递归执行该 update。
- finite effect grammar在每拍生成 dependent `.next`；exact target effect不能再生时，同一row生成
  causal `.cut`并进入fixed-root U7。

### Total old/revised disposition

- `sourceGeneratedBoundaryInquiryOutcome initial`穷尽生成 old或revised inquiry，不接收caller提供的
  boundedness proof、branch、target、failure或revision。
- old inquiry生成完整global physical trajectory。
- revised inquiry保留original-root failure、U8 minimal coface与answer-and-next；其sealed native law
  在actual receipt path上生成Fourier、physical、enstrophy-flux与Duhamel evolution。
- recovery next重新进入 `GeneratedWholeRestartCurrent`，并由原authoritative NS ledger识别。

### 非零 revised 分支与独立消费

- concrete closed-triad source在 `wholeRestartModes 1` 外生成精确非零 nonlinear row与非零canonical
  `T_native` correction。
- 同一fixed initial occurrence写出literal `.nativeWrite`，其next physical state由root compiler生成。
- correction-free old projected realization被排除；next source上的独立nonlinear observer严格为正。
- concrete public producer的唯一输入是 `Viscosity`；state、occurrence、effect、write与next都在结论侧生成。

## Claim scope

本 checkpoint签收的是：对任意既有 `GeneratedWholeRestartCurrent`，old/revised 两种边界现实都由
同一source原生给出完整可继续演化的typed answer。它不把 `∀ current` 偷换成“每枚current都落入
old classical branch”，也不把 revised `T_native` evolution冒充caller-supplied classical解。

同初值、同时间跨度的 whole mild/Serrin 解唯一性由
`wholeContinuousMildSerrin_sameInitial_unique`独立闭合；它与这里的total old/revised resolver是两枚
互补机器事实。

## 当前源码入口

- [`NativeRecursion.lean`](../../SaturationMonoid/NavierStokes/ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.lean)
- [`BoundaryDisposition.lean`](../../SaturationMonoid/NavierStokes/NativeAccumulation/BoundaryDisposition.lean)
- [`NativeTurbulenceLaw.lean`](../../SaturationMonoid/NavierStokes/NativeAccumulation/NativeTurbulenceLaw.lean)
- [`ConcreteEffectRecurrence.lean`](../../SaturationMonoid/NavierStokes/NativeAccumulation/ConcreteEffectRecurrence.lean)
- [`LocalNativeTurbulenceLaw.lean`](../../SaturationMonoid/NavierStokes/NativeAccumulation/LocalNativeTurbulenceLaw.lean)
- [`BoundaryInquiryAuthorityRegression.lean`](../../SaturationMonoid/NavierStokes/NativeAccumulation/BoundaryInquiryAuthorityRegression.lean)
- [`LivingLawNavierStokesRootInstance.lean`](../../SaturationMonoid/Tracks/LivingLawNavierStokesRootInstance.lean)

import H0mework.Versions.Ra4744604.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceOpenFieldKernelRha0299.SourceR0006.SourceExactDensityFlow299
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-! The terminal operator flow is generated in an abstract complex Banach space.
Reflection is proved before any concrete iterated operator space is substituted.
The coefficient and its continuity are the inputs; no completed curve, Hilbert
structure, topology equality or normalization certificate is supplied.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
open Set

namespace SourceTerminalBanachFlow303

private def reflectClock (left right time : ℝ) : ℝ := left + right - time

private theorem reflectClock_twice (left right time : ℝ) :
    reflectClock left right (reflectClock left right time) = time := by
  unfold reflectClock
  ring

private theorem reflectClock_terminal (left right : ℝ) :
    reflectClock left right right = left := by
  unfold reflectClock
  ring

private theorem reflectClock_continuous (left right : ℝ) :
    Continuous (reflectClock left right) := by
  change Continuous (fun time : ℝ => left + right - time)
  exact continuous_const.sub continuous_id

private theorem reflectClock_mem (left right time : ℝ)
    (inside : time ∈ Icc left right) :
    reflectClock left right time ∈ Icc left right := by
  change left ≤ left + right - time ∧ left + right - time ≤ right
  constructor <;> linarith [inside.1, inside.2]

private theorem reflectClock_derivative (left right time : ℝ) :
    HasDerivWithinAt (reflectClock left right) (-1 : ℝ) (Icc left right) time := by
  change HasDerivWithinAt (fun r : ℝ => left + right - r) (-1 : ℝ) (Icc left right) time
  exact HasDerivWithinAt.const_sub (left + right)
    (hasDerivWithinAt_id time (Icc left right))

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]

/-- The same forward Banach producer, read at the reflected physical time. -/
def terminalOperatorFlow (action : ℝ → B →L[ℂ] B) (continuous : Continuous action)
    (left right : ℝ) (ordered : left ≤ right) (time : ℝ) : B →L[ℂ] B :=
  SourceOpenFieldKernel299.BanachOperatorFlow.operatorFlow
    (fun r => action (reflectClock left right r))
    (continuous.comp (reflectClock_continuous left right))
    left right ordered (reflectClock left right time)

theorem terminalOperatorFlow_terminal (action : ℝ → B →L[ℂ] B) (continuous : Continuous action)
    (left right : ℝ) (ordered : left ≤ right) :
    terminalOperatorFlow action continuous left right ordered right = 1 := by
  simpa only [terminalOperatorFlow, reflectClock_terminal] using
    SourceOpenFieldKernel299.BanachOperatorFlow.operatorFlow_initial
      (fun r => action (reflectClock left right r))
      (continuous.comp (reflectClock_continuous left right)) left right ordered

theorem terminalOperatorFlow_derivative (action : ℝ → B →L[ℂ] B)
    (continuous : Continuous action) (left right : ℝ) (ordered : left ≤ right)
    (time : ℝ) (inside : time ∈ Icc left right) :
    HasDerivWithinAt (terminalOperatorFlow action continuous left right ordered)
      (-((action time).comp (terminalOperatorFlow action continuous left right ordered time)))
      (Icc left right) time := by
  have forward := SourceOpenFieldKernel299.BanachOperatorFlow.operatorFlow_derivative
    (fun r => action (reflectClock left right r))
    (continuous.comp (reflectClock_continuous left right)) left right ordered
    (reflectClock left right time) (reflectClock_mem left right time inside)
  -- Pull back the TVS remainder itself; the normed scomp interface would
  -- reselect the operator space's additive, module and topological data.
  have forward_error := HasFDerivWithinAt.isLittleOTVS forward.hasFDerivWithinAt
  have clock_continuous := (reflectClock_derivative left right time).continuousWithinAt
  have pulled := forward_error.comp_tendsto (clock_continuous.tendsto_nhdsWithin
    (fun r hr => reflectClock_mem left right r hr))
  have difference (r : ℝ) :
      reflectClock left right r - reflectClock left right time = -(r-time) := by
    unfold reflectClock
    ring
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  apply HasFDerivWithinAt.of_isLittleOTVS
  refine pulled.neg_right.congr (fun r => ?_) (fun r => ?_)
  · simp only [Function.comp_def, terminalOperatorFlow,
      ContinuousLinearMap.toSpanSingleton_apply, reflectClock_twice, difference,
      neg_smul, smul_neg]
  · simp only [Pi.neg_apply, Function.comp_def, difference, neg_neg]

theorem terminalOperatorFlow_continuousOn (action : ℝ → B →L[ℂ] B)
    (continuous : Continuous action) (left right : ℝ) (ordered : left ≤ right) :
    ContinuousOn (terminalOperatorFlow action continuous left right ordered) (Icc left right) :=
  (SourceOpenFieldKernel299.BanachOperatorFlow.operatorFlow_continuous
    (fun r => action (reflectClock left right r))
    (continuous.comp (reflectClock_continuous left right)) left right ordered).comp
      (reflectClock_continuous left right).continuousOn
      (fun r hr => reflectClock_mem left right r hr)

theorem applied_terminal_flow_derivative (action : ℝ → B →L[ℂ] B)
    (continuous : Continuous action) (left right : ℝ) (ordered : left ≤ right)
    (value : B) (time : ℝ) (inside : time ∈ Icc left right) :
    HasDerivWithinAt
      (fun r => terminalOperatorFlow action continuous left right ordered r value)
      (-(action time (terminalOperatorFlow action continuous left right ordered time value)))
      (Icc left right) time := by
  let evaluation : (B →L[ℂ] B) →L[ℝ] B :=
    (ContinuousLinearMap.apply ℂ B value).restrictScalars ℝ
  have derivative :=
    (evaluation.hasFDerivAt
      (x := terminalOperatorFlow action continuous left right ordered time)).comp_hasDerivWithinAt
        time (terminalOperatorFlow_derivative action continuous left right ordered time inside)
  exact derivative

end SourceTerminalBanachFlow303

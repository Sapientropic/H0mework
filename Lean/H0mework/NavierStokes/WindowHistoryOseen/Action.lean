import H0mework.NavierStokes.WindowHistoryOseen.Fiber
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryOseen
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def application : (wholePhysical →L[ℝ] wholePhysical) →L[ℝ] wholePhysical →L[ℝ] wholePhysical :=
  ContinuousLinearMap.id ℝ (wholePhysical →L[ℝ] wholePhysical)

private def multiplication (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Lp (E →L[ℝ] E) ∞ averageMeasure →L[ℝ] Lp E 2 averageMeasure →L[ℝ] Lp E 2 averageMeasure :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] E)).holderL averageMeasure ∞ 2 2

private theorem multiplication_continuous (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Continuous (multiplication E) := (multiplication E).continuous

def action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  multiplication wholePhysical (forwardProfile seed M time)

def adjoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  multiplication wholePhysical (dualProfile seed M time)

theorem action_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (action seed M) := by
  have control : Continuous (multiplication wholePhysical) := multiplication_continuous wholePhysical
  have prof : Continuous (forwardProfile seed M) :=
    profile_continuous (E := wholePhysical →L[ℝ] wholePhysical) (forwardFiber seed M) (forwardFiber_continuous seed M)
  simpa only [action] using! control.comp prof

theorem adjoint_continuous (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : Continuous (adjoint seed M) := by
  have control : Continuous (multiplication wholePhysical) := multiplication_continuous wholePhysical
  have prof : Continuous (dualProfile seed M) :=
    profile_continuous (E := wholePhysical →L[ℝ] wholePhysical) (dualFiber seed M) (dualFiber_continuous seed M)
  simpa only [adjoint] using! control.comp prof

theorem action_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    action seed M time v =ᵐ[averageMeasure] fun shift => forwardFiber seed M (time-shift) (v shift) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical →L[ℝ] wholePhysical) (F := wholePhysical) (G := wholePhysical) (r := 2) application (forwardProfile seed M time) v,
    forwardProfile_ae seed M time] with shift read original
  change action seed M time v shift=application (forwardProfile seed M time shift) (v shift) at read
  rw [read,original]
  rfl

theorem adjoint_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    adjoint seed M time v =ᵐ[averageMeasure] fun shift => dualFiber seed M (time-shift) (v shift) := by
  filter_upwards [ContinuousLinearMap.coeFn_holder (𝕜 := ℝ) (E := wholePhysical →L[ℝ] wholePhysical) (F := wholePhysical) (G := wholePhysical) (r := 2) application (dualProfile seed M time) v,
    dualProfile_ae seed M time] with shift read original
  change adjoint seed M time v shift=application (dualProfile seed M time shift) (v shift) at read
  rw [read,original]
  rfl

theorem action_adjoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (u v : H) :
    inner ℝ (action seed M time u) v=inner ℝ u (adjoint seed M time v) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [action_ae seed M time u,adjoint_ae seed M time v] with shift first second
  rw [first,second,fiber_adjoint]

theorem action_dissipative (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    inner ℝ v (action seed M time v) ≤ 0 := by
  rw [L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [action_ae seed M time v] with shift actual
  rw [actual]
  exact fiber_dissipative seed M (time-shift) (v shift)

theorem exists_evolution (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (initial : H)
    (start finish : ℝ) (ordered : start ≤ finish) :
    ∃ path : ℝ → H,path start=initial ∧ ∀ time∈Icc start finish,
      HasDerivWithinAt path (action seed M time (path time)) (Icc start finish) time := by
  exact PhysicsCore.StageNineDiracMatterGalerkinEvolution.exists_galerkinLinearCoefficientCurve_on_Icc
    (action seed M) (action_continuous seed M) initial start finish ordered

theorem exists_backward (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (terminal : H)
    (start finish : ℝ) (ordered : start ≤ finish) :
    ∃ path : ℝ → H,path finish=terminal ∧ ∀ time∈Icc start finish,
      HasDerivWithinAt path (-adjoint seed M time (path time)) (Icc start finish) time := by
  obtain ⟨path,initial,evolution⟩ :=
    PhysicsCore.StageNineDiracMatterGalerkinEvolution.exists_galerkinLinearCoefficientCurve_on_Icc
      (fun time => adjoint seed M (-time)) ((adjoint_continuous seed M).comp continuous_neg)
      terminal (-finish) (-start) (neg_le_neg ordered)
  refine ⟨fun time => path (-time),initial,?_⟩
  intro time inside
  have into : MapsTo (fun t : ℝ => -t) (Icc start finish) (Icc (-finish) (-start)) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have differentiated := (evolution (-time) (by constructor <;> linarith [inside.1,inside.2])).scomp time
    ((hasDerivAt_neg time).hasDerivWithinAt) into
  simpa only [neg_neg,neg_smul,one_smul,PhysicsCore.StageNineDiracMatterGalerkinEvolution.galerkinLinearVelocity]
    using! differentiated

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem whole_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    (action seed M (step.2.clockAdvance+time),adjoint seed M (step.2.clockAdvance+time))=
      (action step.1 M time,adjoint step.1 M time) := by
  have fields : ∀ᵐ shift ∂averageMeasure,
      (forwardField seed M (step.2.clockAdvance+time) shift,dualField seed M (step.2.clockAdvance+time) shift)=
        (forwardField step.1 M time shift,dualField step.1 M time shift) := by
    filter_upwards [NativeWindowTraceEndpointWindow.average_interval] with shift support
    have same := NativeWindowTraceAdjoint.source_next seed M step generated (time-shift) (by linarith [support.2])
    change (lift M _,lift M _)=(lift M _,lift M _)
    rw [add_sub_assoc]
    simp only [Prod.mk.injEq] at same
    rw [same.2.1,same.2.2]
  have profiles : (forwardProfile seed M (step.2.clockAdvance+time),dualProfile seed M (step.2.clockAdvance+time))=
      (forwardProfile step.1 M time,dualProfile step.1 M time) := by
    apply Prod.ext
    · apply Lp.ext
      filter_upwards [forwardProfile_ae seed M (step.2.clockAdvance+time),forwardProfile_ae step.1 M time,fields]
        with shift first second same
      rw [first,second]
      exact congrArg Prod.fst same
    · apply Lp.ext
      filter_upwards [dualProfile_ae seed M (step.2.clockAdvance+time),dualProfile_ae step.1 M time,fields]
        with shift first second same
      rw [first,second]
      exact congrArg Prod.snd same
  simp only [Prod.mk.injEq] at profiles
  simp only [action,adjoint,profiles.1,profiles.2]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryOseen

import H0mework.NavierStokes.WindowSchurFrozen.EffectiveTime
import H0mework.NavierStokes.WindowSchurMean.PhysicalJet

set_option autoImplicit false
open scoped BigOperators Topology ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCommonForceTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryEffectiveInverse (generator)
open NativeWindowHistoryMeanPhysicalJet (physicalJet)
open NativeWindowHistorySchurCompletion (commonForce completion)
open NativeWindowHistoryMeanProjection (embed mean)
open NativeWindowHistoryOseen (H action)
open NativeWindowTraceWholeHistory (projected projection)
noncomputable section
variable {nu : Viscosity}

def value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  NativeWindowHistoryHeatWindow.sourceInput seed M time

theorem value_product (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    value seed M time=generator seed M time (physicalJet seed M 0 time) := by
  rw [NativeWindowHistoryMeanPhysicalJet.physicalJet_zero]
  exact (NativeWindowHistoryEffectiveInverse.source_mean seed M time).symm

theorem commonForce_projected (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    projection M (commonForce seed M time)=commonForce seed M time := by
  have equation := NativeWindowHistorySchurCompletion.completion_equation seed M time
  have acted := congrArg ((projection M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure) equation
  have fixed : projected M (completion seed M time-action seed M time (completion seed M time))=
      completion seed M time-action seed M time (completion seed M time) := by
    have distribute := ((projection M).compLpL 2 NativeForwardWindowPairingReadout.averageMeasure).map_sub
      (completion seed M time) (action seed M time (completion seed M time))
    exact distribute.trans (congrArg₂ (fun x y : H => x-y)
      (NativeWindowHistorySchurCompletion.completion_projected seed M time)
      (NativeWindowHistoryOseenGap.projected_action seed M time (completion seed M time)))
  have point := NativeWindowHistoryMeanProjection.comp_embed (projection M) (commonForce seed M time)
  have result : embed (projection M (commonForce seed M time))=embed (commonForce seed M time) :=
    point.symm.trans (acted.symm.trans (fixed.trans equation))
  simpa only [NativeWindowHistoryMeanProjection.mean_embed] using congrArg mean result

theorem value_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    includeCLM (modes M) (modes_closed M) (value seed M time)=commonForce seed M time :=
  commonForce_projected seed M time

theorem mean_contDiff (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    ContDiff ℝ ∞ (physicalJet seed M 0) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro order _
  rw [NativeWindowHistoryMeanPhysicalJet.physicalJet_iterated]
  exact fun time => (NativeWindowHistoryMeanPhysicalJet.physicalJet_hasDerivAt seed M order time).differentiableAt

private theorem apply_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] E) (v : ℝ → E) (ha : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (fun t => A t (v t)) := ha.clm_apply hv

theorem value_contDiff (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : ContDiff ℝ ∞ (value seed M) := by
  have same : value seed M=fun t => generator seed M t (physicalJet seed M 0 t) := funext (value_product seed M)
  rw [same]
  exact apply_smooth _ _ (NativeWindowHistoryEffectiveTime.generator_contDiff seed M) (mean_contDiff seed M)

private theorem apply_leibniz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] E) (v : ℝ → E) (ha : ContDiff ℝ ∞ A) (hv : ContDiff ℝ ∞ v) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun t => A t (v t)) time=
      ∑ i∈Finset.range (order+1),order.choose i • (iteratedDeriv i A time) (iteratedDeriv (order-i) v time) := by
  let bounded : IsBoundedSMul (E →L[ℝ] E) E := .of_norm_smul_le (fun A v => A.le_opNorm v)
  let tower : IsScalarTower ℝ (E →L[ℝ] E) E := ⟨fun _ _ _ => rfl⟩
  have smoothA : ContDiff ℝ (order : ℕ) A := ha.of_le (by exact_mod_cast (ENat.natCast_lt_top order).le)
  have smoothV : ContDiff ℝ (order : ℕ) v := hv.of_le (by exact_mod_cast (ENat.natCast_lt_top order).le)
  have source := iteratedDerivWithin_smul (𝕜 := ℝ) (𝔸 := E →L[ℝ] E) (Set.mem_univ time) uniqueDiffOn_univ
    smoothA.contDiffAt.contDiffWithinAt smoothV.contDiffAt.contDiffWithinAt
  simpa only [iteratedDerivWithin_univ,Pi.smul_def,ContinuousLinearMap.smul_def] using! source

def jet (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) : ℝ → physicalSpace (modes M) :=
  iteratedDeriv order (value seed M)

theorem jet_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : jet seed M 0=value seed M := iteratedDeriv_zero

theorem jet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (jet seed M order) (jet seed M (order+1) time) time := by
  have source := ((value_contDiff seed M).differentiable_iteratedDeriv order (by exact_mod_cast (ENat.natCast_lt_top order))) time
  simpa only [jet,iteratedDeriv_succ] using source.hasDerivAt

theorem jet_product (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    jet seed M order time=∑ i∈Finset.range (order+1),order.choose i •
      NativeWindowHistoryEffectiveTime.jet seed M i time (physicalJet seed M (order-i) time) := by
  have same : value seed M=fun t => generator seed M t (physicalJet seed M 0 t) := funext (value_product seed M)
  have source := apply_leibniz _ _ (NativeWindowHistoryEffectiveTime.generator_contDiff seed M) (mean_contDiff seed M) order time
  simpa only [jet,same,NativeWindowHistoryEffectiveTime.jet,NativeWindowHistoryMeanPhysicalJet.physicalJet_iterated] using! source

theorem whole_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (commonForce seed M) (includeCLM (modes M) (modes_closed M) (jet seed M 1 time)) time := by
  have source := (includeCLM (modes M) (modes_closed M)).hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed M 0 time)
  simpa only [Function.comp_def,jet_zero,value_original] using! source

theorem whole_iterated (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    includeCLM (modes M) (modes_closed M) (jet seed M order time)=iteratedDeriv order (commonForce seed M) time := by
  induction order generalizing time with
  | zero => exact value_original seed M time
  | succ order ih =>
    have lifted := (includeCLM (modes M) (modes_closed M)).hasFDerivAt.comp_hasDerivAt time (jet_hasDerivAt seed M order time)
    have source : HasDerivAt (iteratedDeriv order (commonForce seed M))
        (includeCLM (modes M) (modes_closed M) (jet seed M (order+1) time)) time :=
      lifted.congr_of_eventuallyEq (Eventually.of_forall fun t => (ih t).symm)
    simpa only [iteratedDeriv_succ] using source.deriv.symm

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem jet_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0 ≤ time) :
    jet seed M order (step.2.clockAdvance+time)=jet step.1 M order time := by
  rw [jet_product,jet_product]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun v : physicalSpace (modes M) => order.choose i • v)
    (congrArg₂ (fun A v => A v) (NativeWindowHistoryEffectiveTime.jet_next seed M i step generated time time0)
      (NativeWindowHistoryMeanPhysicalJet.physicalJet_next seed M (order-i) step generated time time0))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCommonForceTime

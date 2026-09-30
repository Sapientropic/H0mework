import H0mework.Versions.X.NavierStokes.WindowSchurMean.Time
import H0mework.Versions.X.NavierStokes.WindowSchurMean.Gradient
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanPhysicalJet
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeResolventCompactness (State)
noncomputable section
variable {nu : Viscosity}

def includeState (M : ℕ) : physicalSpace (modes M) →L[ℝ] State :=
  wholePhysical.subtypeL.comp (includeCLM (modes M) (modes_closed M))

def physicalRead (M : ℕ) : State →L[ℝ] physicalSpace (modes M) :=
  (restrictCLM (modes M) (modes_zero M) (modes_closed M)).comp wholePhysical.orthogonalProjectionOnto

theorem physicalRead_include (M : ℕ) (v : physicalSpace (modes M)) : physicalRead M (includeState M v)=v := by
  change restrictCLM (modes M) (modes_zero M) (modes_closed M)
    (wholePhysical.orthogonalProjectionOnto ((includeCLM (modes M) (modes_closed M) v).1))=v
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,restrict_include]

def physicalJet (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : physicalSpace (modes M) :=
  physicalRead M (NativeWindowHistoryMeanTime.jet seed M order time)

theorem physicalJet_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    physicalJet seed M 0 time=NativeWindowHistoryMeanGradient.meanValue M (finiteHistory seed time M) := by
  unfold physicalJet
  rw [← NativeWindowHistoryMeanTime.source_mean seed M time]
  change restrictCLM (modes M) (modes_zero M) (modes_closed M)
    (wholePhysical.orthogonalProjectionOnto ((mean (finiteHistory seed time M)).1))=_
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

theorem include_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    includeCLM (modes M) (modes_closed M) (NativeWindowHistoryMeanGradient.meanValue M (finiteHistory seed time M))=
      mean (finiteHistory seed time M) := by
  have read:=congrArg mean (NativeWindowHistoryMeanGradient.source_projection seed M time)
  change mean (embed (mean (finiteHistory seed time M)))=mean (embed
    (includeCLM (modes M) (modes_closed M) (NativeWindowHistoryMeanGradient.meanValue M (finiteHistory seed time M)))) at read
  rw [NativeWindowHistoryMeanProjection.mean_embed,NativeWindowHistoryMeanProjection.mean_embed] at read
  exact read.symm

theorem physicalJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (physicalJet seed M order) (physicalJet seed M (order+1) time) time :=
  (physicalRead M).hasFDerivAt.comp_hasDerivAt time (NativeWindowHistoryMeanTime.jet_hasDerivAt seed M order time)

theorem includeState_jet (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    includeState M (physicalJet seed M order time)=NativeWindowHistoryMeanTime.jet seed M order time := by
  induction order generalizing time with
  | zero =>
      rw [physicalJet_zero]
      exact (congrArg (fun v : wholePhysical => v.1) (include_mean seed M time)).trans (NativeWindowHistoryMeanTime.source_mean seed M time)
  | succ order previous =>
      have lifted:HasDerivAt (fun t => includeState M (physicalJet seed M order t))
          (includeState M (physicalJet seed M (order+1) time)) time :=
        (includeState M).hasFDerivAt.comp_hasDerivAt time (physicalJet_hasDerivAt seed M order time)
      have original:HasDerivAt (NativeWindowHistoryMeanTime.jet seed M order)
          (includeState M (physicalJet seed M (order+1) time)) time :=
        lifted.congr_of_eventuallyEq (Eventually.of_forall fun t => (previous t).symm)
      exact original.unique (NativeWindowHistoryMeanTime.jet_hasDerivAt seed M order time)

theorem physicalJet_iterated (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) :
    iteratedDeriv order (physicalJet seed M 0)=physicalJet seed M order := by
  induction order with
  | zero => exact iteratedDeriv_zero
  | succ order previous =>
      rw [iteratedDeriv_succ,previous]
      funext time
      exact (physicalJet_hasDerivAt seed M order time).deriv

theorem physicalJet_norm (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    ‖coefficients (modes M) (physicalJet seed M order time)‖ ≤ NativeForwardWindowJets.budget seed order := by
  have read:‖coefficients (modes M) (physicalJet seed M order time)‖=
      ‖NativeWindowHistoryMeanTime.jet seed M order time‖ :=
    (include_norm (modes M) (modes_zero M) (modes_closed M) (physicalJet seed M order time)).symm.trans
      (congrArg (fun v : State => ‖v‖) (includeState_jet seed M order time))
  exact read.trans_le (NativeWindowHistoryMeanTime.jet_bound seed M order time)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem physicalJet_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    physicalJet seed M order (step.2.clockAdvance+time)=physicalJet step.1 M order time :=
  congrArg (physicalRead M) (NativeWindowHistoryMeanTime.jet_next seed M order step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanPhysicalJet

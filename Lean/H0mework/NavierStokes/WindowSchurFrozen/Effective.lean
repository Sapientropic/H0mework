import H0mework.NavierStokes.WindowSchurFrozen.HeatWindow
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

set_option autoImplicit false
open scoped BigOperators Topology ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryEffectiveInverse
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistorySchurAction (effective)
noncomputable section
variable {nu : Viscosity}

abbrev Operator (M : ℕ) := physicalSpace (modes M) →L[ℝ] physicalSpace (modes M)

def average (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) : Operator M :=
  (restrictCLM (modes M) (modes_zero M) (modes_closed M)).comp
    ((NativeWindowHistoryInverseWindow.average seed M order time).comp (includeCLM (modes M) (modes_closed M)))

def generator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : Operator M :=
  ContinuousLinearMap.id ℝ _-(restrictCLM (modes M) (modes_zero M) (modes_closed M)).comp
    ((effective seed M time).comp (includeCLM (modes M) (modes_closed M)))

theorem generator_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    generator seed M time v=v-restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (effective seed M time (includeCLM (modes M) (modes_closed M) v)) := rfl

theorem average_original (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    average seed M order time v=NativeWindowHistoryHeatWindow.value seed M order time v := by
  have read := congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M))
    (NativeWindowHistoryHeatWindow.physical_read seed M order time v)
  simpa only [average,ContinuousLinearMap.comp_apply,restrict_include] using! read.symm

theorem right_inverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    average seed M 0 time (generator seed M time v)=v := by
  have original := NativeWindowHistoryInverseWindow.schur_inverse seed M time v
  have read := NativeWindowHistoryHeatWindow.whole_read seed M 0 time
    (includeCLM (modes M) (modes_closed M) v-effective seed M time (includeCLM (modes M) (modes_closed M) v))
  have finite := congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M)) (read.trans original)
  simpa only [restrict_include,map_sub,← average_original,generator_original] using finite

theorem average_bijective (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Function.Bijective (average seed M 0 time) := by
  have onto : Function.Surjective (average seed M 0 time) := fun v => ⟨generator seed M time v,right_inverse seed M time v⟩
  exact ⟨LinearMap.injective_iff_surjective.mpr onto,onto⟩

theorem left_inverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    generator seed M time (average seed M 0 time v)=v :=
  (average_bijective seed M time).1 (right_inverse seed M time (average seed M 0 time v))

def unit (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : (Operator M)ˣ where
  val := average seed M 0 time
  inv := generator seed M time
  val_inv := ContinuousLinearMap.ext (right_inverse seed M time)
  inv_val := ContinuousLinearMap.ext (left_inverse seed M time)

theorem inverse_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    Ring.inverse (average seed M 0 time)=generator seed M time :=
  Ring.inverse_unit (unit seed M time)

theorem generator_invertible (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    IsUnit (generator seed M time) := ⟨(unit seed M time)⁻¹,rfl⟩

theorem source_mean (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    generator seed M time (restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)))=
      NativeWindowHistoryHeatWindow.sourceInput seed M time := by
  have source := congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M))
    (NativeWindowHistoryHeatWindow.source_read seed M time)
  have input : average seed M 0 time (NativeWindowHistoryHeatWindow.sourceInput seed M time)=
      restrictCLM (modes M) (modes_zero M) (modes_closed M)
        (NativeWindowHistoryMeanProjection.mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)) := by
    simpa only [restrict_include,← average_original] using source
  exact (congrArg (generator seed M time) input).symm.trans (left_inverse seed M time _)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem average_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    average seed M order (step.2.clockAdvance+time)=average step.1 M order time := by
  exact congrArg (fun A : wholePhysical →L[ℝ] wholePhysical =>
    (restrictCLM (modes M) (modes_zero M) (modes_closed M)).comp (A.comp (includeCLM (modes M) (modes_closed M))))
      (NativeWindowHistoryInverseWindow.average_next seed M order step generated time time0)

theorem generator_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    generator seed M (step.2.clockAdvance+time)=generator step.1 M time := by
  rw [← inverse_original,← inverse_original,average_next seed M 0 step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryEffectiveInverse

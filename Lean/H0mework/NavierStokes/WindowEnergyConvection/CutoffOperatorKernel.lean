import H0mework.NavierStokes.WindowEnergyConvection.CutoffPayment
import H0mework.NavierStokes.WindowEnergyTraceOperator.Action

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCutOperator
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowStressOseenTest NativeResolventAdjoint
open NativeWindowConvectionCutoffAction (primitiveField)
open NativeWindowStressHeatSource (physical)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def differenceField (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : ScalarField :=
  ∑ i : Coordinate,primitiveField seed F 0 time i i

def differenceRead (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) : C(Torus,ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (differenceField seed time F)).comp physical

def differenceForm (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) :
    physicalSpace M →ₗ[ℝ] physicalSpace M →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ i : Coordinate,differenceRead seed time F (evaluate M F i x*evaluate M F i y))
    (fun _ _ _ => by simp only [map_add,add_mul,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,smul_mul_assoc,Finset.smul_sum])
    (fun _ _ _ => by simp only [map_add,mul_add,Finset.sum_add_distrib])
    (fun _ _ _ => by simp only [map_smul,mul_smul_comm,Finset.smul_sum])

def difference (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) :
    Module.End ℝ (physicalSpace M) := (duality M).symm.toLinearMap.comp (differenceForm seed time M F).flip

theorem difference_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector)
    (x y : physicalSpace M) : pairing M x (difference seed time M F y)=differenceForm seed time M F x y := by
  have generated := congrArg (fun f : Module.Dual ℝ (physicalSpace M) => f x)
    ((duality M).apply_symm_apply ((differenceForm seed time M F).flip y))
  change pairing M (difference seed time M F y) x=_ at generated
  rw [pairing_symmetric] at generated
  exact generated

def test (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M L F : Finset IntegerWavevector) (radius : ℕ) :
    Module.End ℝ (physicalSpace M) := NativeWindowTraceOperator.test seed time M L F radius-difference seed time M F

def jointTest (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ) :
    Module.End ℝ (physicalSpace M) := LinearMap.id-test seed time M M F radius

theorem test_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M L F : Finset IntegerWavevector) (radius : ℕ)
    (x y : physicalSpace M) : pairing M x (test seed time M L F radius y)=
      NativeWindowAugmentedFixedOperator.spectral nu M L x y-
        ∑ i : Coordinate,inner ℝ (NativeWindowConvectionCutoffTrace.relative seed F radius time)
          (physical (evaluate M F i x*evaluate M F i y)) := by
  simp only [test,LinearMap.sub_apply,map_sub,NativeWindowTraceOperator.test_pairing,difference_pairing,
    NativeWindowTraceOperator.form,LinearMap.add_apply,NativeWindowTraceOperator.matrixForm,LinearMap.mk₂_apply,
    NativeWindowTraceOperator.read,differenceForm,differenceRead,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    NativeWindowTraceOperator.field_original,inner_neg_left,Finset.sum_neg_distrib,
    NativeWindowConvectionCutoffTrace.old_trace_difference,inner_add_left,Finset.sum_add_distrib,differenceField]
  ring

theorem actual_diagonal (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ)
    (v : physicalSpace M) (zero : 0∉M) : pairing M v (test seed time M M F radius v)=
      pairing M v v+nu.coeff*curlPair M v.1 v.1+NativeWindowTraceOperator.positiveForm seed time M F v+
        NativeWindowConvectionCutoffPayment.testForm seed time M F radius v := by
  rw [test,LinearMap.sub_apply,map_sub,NativeWindowTraceOperator.actual_diagonal seed time M F radius v zero,difference_pairing]
  simp only [NativeWindowTraceCorrection.testForm,NativeWindowConvectionCutoffPayment.testForm,
    NativeWindowConvectionCutoffTrace.correction,NativeWindowConvectionCutoffNormalForm.correction,
    Finset.sum_sub_distrib,inner_sub_left,NativeWindowTraceEnergy.correction,differenceForm,LinearMap.mk₂_apply,
    differenceRead,ContinuousLinearMap.comp_apply,innerSL_apply_apply,differenceField]
  ring

theorem source_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ cutoff≥low,∀ M : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →
      ∀ time∈Icc 0 horizon,∀ v : physicalSpace M,
        pairing M v v+(nu.coeff/2)*curlPair M v.1 v.1≤
          pairing M v (test seed time M M (integerWaveFrequencyCube cutoff) radius v) := by
  obtain ⟨low,paid⟩ := NativeWindowConvectionCutoffPayment.source_test_bound seed horizon nonnegative
  refine ⟨low,fun radius above cutoff covered M zero closed time inside v => ?_⟩
  have small := (neg_abs_le _).trans' (neg_le_neg (paid radius above cutoff covered M zero closed time inside v))
  have positive := NativeWindowTraceOperator.positiveForm_nonnegative seed time M (integerWaveFrequencyCube cutoff) v
  rw [actual_diagonal seed time M (integerWaveFrequencyCube cutoff) radius v zero]
  linarith only [small,positive]

theorem jointTest_difference (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ) :
    jointTest seed time M F radius=NativeWindowTraceOperator.jointTest seed time M F radius+difference seed time M F := by
  unfold jointTest test NativeWindowTraceOperator.jointTest
  abel

theorem jointTest_physical (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector) (radius : ℕ)
    (zero : 0∉M) (closed : FiniteModeNegClosed M) (x y : physicalSpace M) :
    pairing M x (jointTest seed time M F radius y)=
      ∑ i : Coordinate,inner ℝ (NativeWindowConvectionCutoffTrace.relative seed F radius time)
        (physical (evaluate M F i x*evaluate M F i y))-
          nu.coeff*pairing M x (NativeWindowOperatorGreen.laplacian M zero closed nu y) := by
  rw [jointTest,LinearMap.sub_apply,LinearMap.id_apply,map_sub,test_pairing,
    NativeWindowTraceOperatorAction.spectral_laplacian M zero closed]
  ring

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem difference_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (M F : Finset IntegerWavevector) :
    difference seed (step.2.clockAdvance+time) M F=difference step.1 time M F := by
  simp only [difference,differenceForm,differenceRead,differenceField,primitiveField,
    NativeWindowConvectionCutoffWindow.primitive_next seed F 0 step generated time nonnegative]

theorem test_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (M L F : Finset IntegerWavevector) (radius : ℕ) :
    test seed (step.2.clockAdvance+time) M L F radius=test step.1 time M L F radius := by
  rw [test,test,NativeWindowTraceOperatorAction.test_next seed step generated time nonnegative,
    difference_next seed step generated time nonnegative]

theorem jointTest_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time)
    (M F : Finset IntegerWavevector) (radius : ℕ) :
    jointTest seed (step.2.clockAdvance+time) M F radius=jointTest step.1 time M F radius := by
  simp only [jointTest,test_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCutOperator

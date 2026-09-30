import H0mework.NavierStokes.WindowEnergyConvection.CutoffOperatorKernel
import H0mework.NavierStokes.WindowEnergyTraceOperator.Time

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCutTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowStressOseenTest
open NativeUnheatedStressProduct NativeWindowAugmentedTestProduct
open NativeWindowAugmentedCoercivity (productCap)
open NativeWindowConvectionCutoffAction (primitiveField)
open NativeWindowStressHeatSource (physical)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def fieldJet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) : ScalarField :=
  NativeWindowTraceOperatorTime.traceJet seed F radius order time-
    ∑ i : Coordinate,primitiveField seed F order time i i

theorem fieldJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) : HasDerivAt (fun t => fieldJet seed F radius order t) (fieldJet seed F radius (order+1) time) time :=
  (NativeWindowTraceOperatorTime.traceJet_hasDerivAt seed F radius order time).sub
    (HasDerivAt.sum (u := Finset.univ) fun i _ => NativeWindowConvectionCutoffAction.primitiveField_hasDerivAt seed F order time i i)

theorem fieldJet_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) : fieldJet seed F radius 0 time= -NativeWindowConvectionCutoffTrace.relative seed F radius time := by
  rw [fieldJet,NativeWindowTraceOperatorTime.traceJet_zero,NativeWindowTraceOperator.field_original,
    NativeWindowConvectionCutoffTrace.old_trace_difference]
  abel

def quadraticJet (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (value : physicalSpace M) : ℝ :=
  ∑ i : Coordinate,inner ℝ (fieldJet seed F radius order time) (physical (evaluate M F i value*evaluate M F i value))

theorem actual_pairing (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (value : physicalSpace M) :
    pairing M value (NativeWindowTraceCutOperator.test seed time M M F radius value)=
      NativeWindowAugmentedFixedOperator.spectral nu M M value value+quadraticJet seed M F radius 0 time value := by
  rw [NativeWindowTraceCutOperator.test_pairing]
  simp only [quadraticJet,fieldJet_zero,inner_neg_left,Finset.sum_neg_distrib]
  ring

theorem quadraticJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (value : physicalSpace M) : HasDerivAt (fun t => quadraticJet seed M F radius order t value)
      (quadraticJet seed M F radius (order+1) time value) time := by
  have row (i : Coordinate) :=
    (innerSL ℝ (physical (evaluate M F i value*evaluate M F i value))).hasFDerivAt.comp_hasDerivAt time
      (fieldJet_hasDerivAt seed F radius order time)
  simpa only [quadraticJet,Finset.sum_fn,Function.comp_def,innerSL_apply_apply,real_inner_comm] using!
    (HasDerivAt.sum (u := Finset.univ) fun i _ => row i)

theorem actual_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (value : physicalSpace M) :
    HasDerivAt (fun t => pairing M value (NativeWindowTraceCutOperator.test seed t M M F radius value))
      (quadraticJet seed M F radius 1 time value) time := by
  simpa only [actual_pairing] using
    (quadraticJet_hasDerivAt seed M F radius 0 time value).const_add
      (NativeWindowAugmentedFixedOperator.spectral nu M M value value)

theorem fieldJet_split (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ) (time : ℝ) :
    fieldJet seed F radius order time=∑ i : Coordinate,
      (physical (NativeWindowStressHeatTime.jet seed F i i order time)+
        NativeWindowConvectionCutoffNormalForm.correctionJet seed F radius order time i i) := by
  simp only [fieldJet,NativeWindowTraceOperatorTime.traceJet,NativeWindowAugmentedTimeForm.matrixJet,
    NativeWindowConvectionCutoffNormalForm.correctionJet,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  abel

theorem source_field_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) (order : ℕ) :
    ∃ low : ℕ,∃ B : ℝ,0 ≤ B ∧∀ radius ≥ low,∀ cutoff ≥ low,∀ time ∈ Icc 0 horizon,
      ‖fieldJet seed (integerWaveFrequencyCube cutoff) radius order time‖ ≤ B := by
  let B := NativeWindowAugmentedPayment.stressBudget seed order horizon+1
  have B0 : 0 ≤ B := by
    have paid := (norm_nonneg _).trans (NativeWindowAugmentedPayment.stressJet_bound seed 0 order 0 horizon ⟨le_rfl,nonnegative⟩ 0 0)
    dsimp only [B]
    linarith
  obtain ⟨low,small⟩ := NativeWindowConvectionCutoffNormalForm.correctionJet_small seed order horizon nonnegative 1 (by norm_num)
  refine ⟨low,3*B,mul_nonneg (by norm_num) B0,fun radius above cutoff covered time inside => ?_⟩
  rw [fieldJet_split]
  apply (norm_sum_le _ _).trans
  have row (i : Coordinate) : ‖physical (NativeWindowStressHeatTime.jet seed (integerWaveFrequencyCube cutoff) i i order time)+
      NativeWindowConvectionCutoffNormalForm.correctionJet seed (integerWaveFrequencyCube cutoff) radius order time i i‖ ≤ B := by
    rw [← NativeWindowAugmentedPayment.stressJet_original seed cutoff order time inside.1]
    exact (norm_add_le _ _).trans (add_le_add
      (NativeWindowAugmentedPayment.stressJet_bound seed cutoff order time horizon inside i i)
      (small radius above cutoff covered time inside i i).le)
  exact (Finset.sum_le_sum fun i _ => row i).trans_eq (by simp)

theorem quadratic_bound (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (value : physicalSpace M) (zero : 0 ∉ M) (closedM : FiniteModeNegClosed M) (closedF : FiniteModeNegClosed F) :
    |quadraticJet seed M F radius order time value| ≤
      3*‖fieldJet seed F radius order time‖*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
  have row (i : Coordinate) : |inner ℝ (fieldJet seed F radius order time) (physical (evaluate M F i value*evaluate M F i value))| ≤
      ‖fieldJet seed F radius order time‖*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    apply (abs_real_inner_le_norm _ _).trans
    have tested := (product_bound M F value zero closedM closedF i i).trans
      (mul_le_mul_of_nonneg_left (projected_gradient_le M F value) (by positivity))
    exact (mul_le_mul_of_nonneg_left tested (norm_nonneg _)).trans_eq (by unfold productCap; ring)
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => row i).trans_eq (by simp; ring))

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem fieldJet_next (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    fieldJet seed F radius order (step.2.clockAdvance+time)=fieldJet step.1 F radius order time := by
  unfold fieldJet
  apply congrArg₂ (fun x y : ScalarField => x-y)
  · unfold NativeWindowTraceOperatorTime.traceJet
    apply Finset.sum_congr rfl
    intro i _
    simp only [NativeWindowAugmentedTimeForm.matrixJet,
      NativeWindowStressHeatTime.jet_next seed F i i order step generated time nonnegative,
      NativeWindowJointNormalForm.correctionJet_next seed F radius order step generated time nonnegative]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [primitiveField,NativeWindowConvectionCutoffWindow.primitive_next seed F order step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCutTime

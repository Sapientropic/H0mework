import H0mework.Versions.X.NavierStokes.WindowEnergyTraceOperator.Kernel
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.Payment

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceOperatorTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowStressOseenTest
open NativeUnheatedStressProduct NativeWindowAugmentedTestProduct
open NativeWindowAugmentedFixedOperator (spectral)
open NativeWindowTraceOperator (test test_pairing form matrixForm field read)
open NativeWindowAugmentedCoercivity (productCap)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def traceJet (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) : ScalarField := ∑ i : Coordinate,NativeWindowAugmentedTimeForm.matrixJet seed F radius order time i i

theorem traceJet_zero (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) : traceJet seed F radius 0 time=field seed time F radius := by
  simp only [traceJet,NativeWindowAugmentedTimeForm.matrixJet_zero,field]

theorem traceJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) : HasDerivAt (fun t => traceJet seed F radius order t) (traceJet seed F radius (order+1) time) time :=
  HasDerivAt.sum (u := Finset.univ) fun i _ => NativeWindowAugmentedTimeForm.matrixJet_hasDerivAt seed F radius order time i i

def quadraticJet (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (value : physicalSpace M) : ℝ := ∑ i : Coordinate,
  inner ℝ (traceJet seed F radius order time)
    (NativeWindowStressHeatSource.physical (evaluate M F i value*evaluate M F i value))

theorem quadraticJet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius order : ℕ)
    (time : ℝ) (value : physicalSpace M) : HasDerivAt (fun t => quadraticJet seed M F radius order t value)
      (quadraticJet seed M F radius (order+1) time value) time := by
  have row (i : Coordinate) :=
    (innerSL ℝ (NativeWindowStressHeatSource.physical (evaluate M F i value*evaluate M F i value))).hasFDerivAt.comp_hasDerivAt
      time (traceJet_hasDerivAt seed F radius order time)
  have sum := HasDerivAt.sum (u := Finset.univ) fun i _ => row i
  simpa only [quadraticJet,Finset.sum_fn,Function.comp_def,innerSL_apply_apply,real_inner_comm] using! sum

theorem actual_pairing (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (value : physicalSpace M) : pairing M value (test seed time M M F radius value)=
      spectral nu M M value value+quadraticJet seed M F radius 0 time value := by
  rw [test_pairing,NativeWindowTraceOperator.form,LinearMap.add_apply,LinearMap.add_apply]
  simp only [quadraticJet,traceJet_zero,matrixForm,LinearMap.mk₂_apply,
    NativeWindowTraceOperator.read,ContinuousLinearMap.comp_apply,innerSL_apply_apply]

theorem actual_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (value : physicalSpace M) : HasDerivAt (fun t => pairing M value (test seed t M M F radius value))
      (quadraticJet seed M F radius 1 time value) time := by
  simpa only [actual_pairing] using (quadraticJet_hasDerivAt seed M F radius 0 time value).const_add (spectral nu M M value value)

theorem source_time_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) (order : ℕ) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius,∀ M : Finset IntegerWavevector,
      0∉M →FiniteModeNegClosed M →∀ time∈Icc 0 horizon,∀ value : physicalSpace M,
        |quadraticJet seed M (integerWaveFrequencyCube outerRadius) radius order time value|≤
          C*pairing M value (test seed time M M (integerWaveFrequencyCube outerRadius) radius value) := by
  let B := NativeWindowAugmentedPayment.stressBudget seed order horizon+1
  have B0 : 0≤B := by
    have paid := (norm_nonneg _).trans (NativeWindowAugmentedPayment.stressJet_bound seed 0 order 0 horizon ⟨le_rfl,nonnegative⟩ 0 0)
    dsimp only [B]
    linarith
  let C := 18*B*productCap/(nu.coeff*(2*Real.pi)^2)
  have C0 : 0≤C := by dsimp only [C,productCap]; positivity [nu.coeff_pos]
  obtain ⟨first,coercive⟩ := NativeWindowTraceOperator.source_coercivity seed horizon nonnegative
  obtain ⟨last,small⟩ := NativeWindowJointNormalForm.correctionJet_small seed order horizon nonnegative 1 (by norm_num)
  refine ⟨max first last,C,C0,fun radius above outerRadius M zero closed time inside value => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  have componentBound (i : Coordinate) : ‖NativeWindowAugmentedTimeForm.matrixJet seed F radius order time i i‖≤B := by
    rw [NativeWindowAugmentedTimeForm.matrixJet,← NativeWindowAugmentedPayment.stressJet_original seed outerRadius order time inside.1]
    exact (norm_add_le _ _).trans (add_le_add
      (NativeWindowAugmentedPayment.stressJet_bound seed outerRadius order time horizon inside i i)
      (small radius ((le_max_right first last).trans above) F time inside i i).le)
  have fieldBound : ‖traceJet seed F radius order time‖≤3*B :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => componentBound i).trans_eq (by simp))
  have row (i : Coordinate) : |inner ℝ (traceJet seed F radius order time)
      (NativeWindowStressHeatSource.physical (evaluate M F i value*evaluate M F i value))|≤
        3*B*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    apply (abs_real_inner_le_norm _ _).trans
    have tested := (product_bound M F value zero closed (NativeWindowFiniteGramFourier.cube_closed outerRadius) i i).trans
      (mul_le_mul_of_nonneg_left (projected_gradient_le M F value) (by positivity))
    exact (mul_le_mul fieldBound tested (norm_nonneg _) (by positivity)).trans_eq (by unfold productCap; ring)
  have budget : |quadraticJet seed M F radius order time value|≤9*B*productCap*gradientMass (complexSharpSupportProjection M value.1) :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => row i).trans_eq (by simp; ring))
  have mass0 : 0≤pairing M value value := by
    change (0 : ℝ) ≤ inner ℝ (coefficients M value) (coefficients M value)
    rw [real_inner_self_eq_norm_sq]
    positivity
  have control := coercive radius ((le_max_left first last).trans above) M F zero closed
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) time inside value
  have relative := mul_le_mul_of_nonneg_left control C0
  have cancel : C*((nu.coeff/2)*curlPair M value.1 value.1)=
      9*B*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    rw [curl_original M value zero]
    dsimp only [C]
    field_simp [nu.coeff_pos.ne',Real.pi_ne_zero]
    ring
  rw [mul_add,cancel] at relative
  exact budget.trans (by linarith only [relative,mul_nonneg C0 mass0])

theorem source_energy_time_control (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius,∀ M : Finset IntegerWavevector,
      0∉M →FiniteModeNegClosed M →∀ time∈Icc 0 horizon,∀ value : physicalSpace M,
        |deriv (fun t => pairing M value (test seed t M M (integerWaveFrequencyCube outerRadius) radius value)) time|≤
          C*pairing M value (test seed time M M (integerWaveFrequencyCube outerRadius) radius value) := by
  obtain ⟨low,C,C0,paid⟩ := source_time_bound seed horizon nonnegative 1
  refine ⟨low,C,C0,fun radius above outerRadius M zero closed time inside value => ?_⟩
  rw [(actual_hasDerivAt seed M (integerWaveFrequencyCube outerRadius) radius time value).deriv]
  exact paid radius above outerRadius M zero closed time inside value

end
end SaturationMonoid.NavierStokes.NativeWindowTraceOperatorTime

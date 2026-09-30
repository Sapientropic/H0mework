import H0mework.NavierStokes.WindowEnergyAugmented.TestProduct
import H0mework.NavierStokes.WindowEnergyAugmented.FixedOperator

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedCoercivity
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowStressOseenTest
open NativeUnheatedStressProduct NativeWindowAugmentedTestProduct NativeWindowAugmentedFixedOperator
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def correctionForm (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (value : physicalSpace M) : ℝ :=
  ∑ output : Coordinate,∑ input : Coordinate,inner ℝ
    (NativeWindowPressureStrainHistory.correction seed F radius observation output input)
    (NativeWindowStressHeatSource.physical (evaluate M F output value*evaluate M F input value))

theorem matrix_split (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (value : physicalSpace M) :
    matrixPhysicalForm seed observation M F radius value value=
      form seed observation M F value value+correctionForm seed observation M F radius value := by
  simp only [matrixPhysicalForm,LinearMap.mk₂_apply,NativeWindowAugmentedSourceForm.matrixRead,
    ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowAugmentedSourceForm.matrixField,
    inner_add_left,Finset.sum_add_distrib,correctionForm,form_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro output _
  apply Finset.sum_congr rfl
  intro input _
  rw [mean_apply,NativeWindowStressHeatSource.physical_inner]
  apply integral_congr_ae
  filter_upwards with point
  simp only [ContinuousMap.mul_apply]
  ring

theorem spectral_diagonal (M : Finset IntegerWavevector) (value : physicalSpace M) (zero : 0∉M) :
    spectral nu M M value value=pairing M value value+nu.coeff*curlPair M value.1 value.1 := by
  rw [pairing_eq,curlPair]
  change (∑ wave ∈ M,∑ coordinate : Coordinate,(1+nu.coeff*integerWaveViscousMultiplier wave)*
    inner ℝ (value.1 wave coordinate) (value.1 wave coordinate))=_
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro wave inside
  rw [← curl_pair_row wave (fun same => zero (same ▸ inside)) _ _
    (physical_transverse value wave inside) (physical_transverse value wave inside),← Finset.mul_sum]
  have row : (∑ coordinate : Coordinate,inner ℝ (value.1 wave coordinate) (value.1 wave coordinate))=
      complexCoordinateRealInner (value.1 wave) (value.1 wave) := by
    simp only [real_inner_self_eq_norm_sq,complexCoordinateRealInner_self,complexCoordinateVectorNormSq,Complex.normSq_eq_norm_sq]
  rw [row]
  ring

theorem actual_diagonal (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (value : physicalSpace M) (zero : 0∉M) :
    pairing M value (test seed observation M M F radius value)=pairing M value value+
      nu.coeff*curlPair M value.1 value.1+form seed observation M F value value+
        correctionForm seed observation M F radius value := by
  rw [test_pairing,physicalForm,LinearMap.add_apply,LinearMap.add_apply,spectral_diagonal M value zero,
    matrix_split]
  ring

def productCap : ℝ := 12*Real.sqrt NativeUnheatedRieszKernel.constant

theorem correction_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (value : physicalSpace M) (zero : 0∉M) (closedM : FiniteModeNegClosed M)
    (closedF : FiniteModeNegClosed F) (delta : ℝ) (nonnegative : 0≤delta)
    (small : ∀ output input,‖NativeWindowPressureStrainHistory.correction seed F radius observation output input‖≤delta) :
    |correctionForm seed observation M F radius value|≤
      9*delta*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
  have row (output input : Coordinate) : |inner ℝ
      (NativeWindowPressureStrainHistory.correction seed F radius observation output input)
      (NativeWindowStressHeatSource.physical (evaluate M F output value*evaluate M F input value))|≤
        delta*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    apply (abs_real_inner_le_norm _ _).trans
    have tested := (product_bound M F value zero closedM closedF output input).trans
      (mul_le_mul_of_nonneg_left (projected_gradient_le M F value) (by positivity))
    exact (mul_le_mul (small output input) tested (norm_nonneg _) nonnegative).trans_eq (by unfold productCap; ring)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have paid := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ => row output input)
  exact paid.trans_eq (by simp; ring)

theorem source_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →
      FiniteModeNegClosed F →∀ time∈Icc 0 horizon,∀ value : physicalSpace M,
        pairing M value value+(nu.coeff/2)*curlPair M value.1 value.1≤
          pairing M value (test seed time M M F radius value) := by
  let delta := nu.coeff*(2*Real.pi)^2/(18*(productCap+1))
  have deltaPos : 0<delta := by dsimp only [delta,productCap]; positivity [nu.coeff_pos]
  obtain ⟨low,paid⟩ := NativeWindowJointNormalForm.correctionJet_small seed 0 horizon nonnegative delta deltaPos
  refine ⟨low,fun radius above M F zero closedM closedF time inside value => ?_⟩
  have small (output input : Coordinate) : ‖NativeWindowPressureStrainHistory.correction seed F radius time output input‖≤delta := by
    simpa only [NativeWindowJointNormalForm.correctionJet_zero] using (paid radius above F time inside output input).le
  have negative := neg_abs_le (correctionForm seed time M F radius value)
  have bound := correction_bound seed time M F radius value zero closedM closedF delta deltaPos.le small
  have gram := form_positive seed time M F value
  have G0 : 0≤gradientMass (complexSharpSupportProjection M value.1) := tsum_nonneg (density_nonnegative _)
  have fraction : 9*delta*productCap≤(nu.coeff/2)*(2*Real.pi)^2 := by
    have denominator : 18*(productCap+1)>0 := by unfold productCap; positivity
    have same : delta*(18*(productCap+1))=nu.coeff*(2*Real.pi)^2 := div_mul_cancel₀ _ denominator.ne'
    nlinarith only [same,deltaPos]
  have cost := mul_le_mul_of_nonneg_right fraction G0
  rw [mul_assoc (nu.coeff/2),← curl_original M value zero] at cost
  rw [actual_diagonal seed time M F radius value zero]
  linarith only [negative,bound,gram,cost]

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedCoercivity

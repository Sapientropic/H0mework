import H0mework.NavierStokes.WindowEnergyAugmented.Coercivity

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowAugmentedGradient
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWindowStressOseenTest (evaluate evaluate_apply)
open NativePhysicalGradient (multiplier multiplier_sum_norm_sq)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def derivativeState (M : Finset IntegerWavevector) (j : Coordinate) (value : physicalSpace M) : ComplexVorticityHilbertState :=
  ∑ k ∈ M,lp.single 2 k (multiplier k j • value.1 k)

theorem derivativeState_apply (M : Finset IntegerWavevector) (j : Coordinate) (value : physicalSpace M) (k : IntegerWavevector) :
    derivativeState M j value k=multiplier k j • value.1 k := by
  simp only [derivativeState,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,Finset.sum_pi_single]
  split_ifs with inside
  · rfl
  · simp only [physical_supported value k inside,smul_zero]

def derivative (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (j : Coordinate) (value : physicalSpace M) : physicalSpace M :=
  ofPhysical M zero (derivativeState M j value)
    (fun k outside => by rw [derivativeState_apply,physical_supported value k outside,smul_zero])
    (fun k inside => by rw [derivativeState_apply,dotProduct_smul,physical_transverse value k inside,smul_zero])
    (by
      intro k
      funext i
      have real := congrFun (physical_reality (fun {_} inside => closed _ inside) value k) i
      simp only [derivativeState_apply,Pi.smul_apply,smul_eq_mul,vectorConj,star_mul] at *
      rw [real]
      rw [NativeWindowStressHeatEnergy.multiplier_star]
      simp [multiplier,complexWavevector,mul_comm])

theorem derivative_apply (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (j : Coordinate) (value : physicalSpace M) (k : IntegerWavevector) :
    (derivative M zero closed j value).1 k=multiplier k j • value.1 k := derivativeState_apply M j value k

theorem evaluate_derivative (M F : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (j input : Coordinate) (value : physicalSpace M) :
    evaluate M F input (derivative M zero closed j value)=NativeWindowPressureStrainPhysical.gradient value.1 F j input := by
  simp only [evaluate_apply,NativeWindowPressureStrainPhysical.gradient,NativeWindowHighPressurePhysical.realSynthesis,
    derivative_apply,Pi.smul_apply,smul_eq_mul]

private theorem curl_row (M : Finset IntegerWavevector) (zero : 0∉M) (value : physicalSpace M) :
    curlPair M value.1 value.1=∑ k ∈ M,integerWaveViscousMultiplier k*complexCoordinateVectorNormSq (value.1 k) := by
  unfold curlPair
  apply Finset.sum_congr rfl
  intro k inside
  rw [← curl_pair_row k (fun same => zero (same ▸ inside)) _ _
    (physical_transverse value k inside) (physical_transverse value k inside),complexCoordinateRealInner_self]

theorem palinstrophy_original (M : Finset IntegerWavevector) (zero : 0∉M) (closed : FiniteModeNegClosed M)
    (value : physicalSpace M) :
    (∑ j : Coordinate,curlPair M (derivative M zero closed j value).1 (derivative M zero closed j value).1)=
      pairing M (NativeWindowOperatorGreen.laplacian M zero closed nu value) (NativeWindowOperatorGreen.laplacian M zero closed nu value) := by
  simp only [curl_row M zero,derivative_apply,complexCoordinateVectorNormSq_smul,Complex.normSq_eq_norm_sq]
  rw [Finset.sum_comm]
  have row (k : IntegerWavevector) : (∑ j : Coordinate,integerWaveViscousMultiplier k*(‖multiplier k j‖^2*complexCoordinateVectorNormSq (value.1 k)))=
      (integerWaveViscousMultiplier k)^2*complexCoordinateVectorNormSq (value.1 k) := by
    rw [← Finset.mul_sum,← Finset.sum_mul,multiplier_sum_norm_sq]
    unfold integerWaveViscousMultiplier
    ring
  simp only [row,pairing_eq,NativeWindowOperatorGreen.laplacian_row,complexCoordinateRealInner_self]
  apply Finset.sum_congr rfl
  intro k _
  change _=complexCoordinateVectorNormSq ((integerWaveViscousMultiplier k:ℂ) • value.1 k)
  rw [complexCoordinateVectorNormSq_smul,Complex.normSq_ofReal]
  ring

def matrixGradient (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector)
    (zero : 0∉M) (closed : FiniteModeNegClosed M) (radius : ℕ) (value : physicalSpace M) : ℝ :=
  ∑ j : Coordinate,∑ output : Coordinate,∑ input : Coordinate,inner ℝ
    (NativeWindowAugmentedSourceForm.matrixField seed time F radius output input)
    (NativeWindowStressHeatSource.physical (evaluate M F output (derivative M zero closed j value)*
      evaluate M F input (derivative M zero closed j value)))

theorem gradient_diagonal (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (M F : Finset IntegerWavevector)
    (zero : 0∉M) (closed : FiniteModeNegClosed M) (radius : ℕ) (value : physicalSpace M) :
    (∑ j : Coordinate,pairing M (derivative M zero closed j value)
      (NativeWindowAugmentedFixedOperator.test seed time M M F radius (derivative M zero closed j value)))=
      (∑ j : Coordinate,pairing M (derivative M zero closed j value) (derivative M zero closed j value))+
        nu.coeff*pairing M (NativeWindowOperatorGreen.laplacian M zero closed nu value)
          (NativeWindowOperatorGreen.laplacian M zero closed nu value)+matrixGradient seed time M F zero closed radius value := by
  simp only [NativeWindowAugmentedFixedOperator.test_pairing,NativeWindowAugmentedFixedOperator.physicalForm,
    LinearMap.add_apply,NativeWindowAugmentedCoercivity.spectral_diagonal M _ zero,
    NativeWindowAugmentedFixedOperator.matrixPhysicalForm,LinearMap.mk₂_apply,
    NativeWindowAugmentedSourceForm.matrixRead,ContinuousLinearMap.comp_apply,innerSL_apply_apply,
    Finset.sum_add_distrib,← Finset.mul_sum]
  rw [palinstrophy_original (nu := nu) M zero closed value]
  rfl

theorem source_diffusion_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F : Finset IntegerWavevector,∀ zero : 0∉M,∀ closed : FiniteModeNegClosed M,
      FiniteModeNegClosed F →∀ time∈Icc 0 horizon,∀ value : physicalSpace M,
        -2*nu.coeff*curlPair M value.1 value.1-
          2*nu.coeff^2*pairing M (NativeWindowOperatorGreen.laplacian M zero closed nu value)
            (NativeWindowOperatorGreen.laplacian M zero closed nu value)-
              2*nu.coeff*matrixGradient seed time M F zero closed radius value≤
          -2*nu.coeff*curlPair M value.1 value.1-
            nu.coeff^2*pairing M (NativeWindowOperatorGreen.laplacian M zero closed nu value)
              (NativeWindowOperatorGreen.laplacian M zero closed nu value) := by
  obtain ⟨low,paid⟩ := NativeWindowAugmentedCoercivity.source_coercivity seed horizon nonnegative
  refine ⟨low,fun radius above M F zero closed closedF time inside value => ?_⟩
  have source := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ =>
    paid radius above M F zero closed closedF time inside (derivative M zero closed j value)
  rw [gradient_diagonal] at source
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at source
  rw [palinstrophy_original (nu := nu) M zero closed value] at source
  have scaled := mul_le_mul_of_nonneg_left source (show 0≤2*nu.coeff from by positivity [nu.coeff_pos])
  nlinarith only [scaled]

end
end SaturationMonoid.NavierStokes.NativeWindowAugmentedGradient

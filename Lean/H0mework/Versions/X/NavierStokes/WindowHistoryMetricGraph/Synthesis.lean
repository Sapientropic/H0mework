import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Synthesis

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowMetricGraphSynthesis
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open NativeFiniteActionResolvent NativeWindowOperatorGreen NativeCommonAdvectorAction NativeResolventAdjoint
open NativeWindowStressOseenTest (evaluate evaluate_apply)
open NativeCompleteStressCarrier (weight weight_pos weight_summable)
open NativeWindowTraceTerminalSynthesis (basis_bound coordinate_square_bound)
noncomputable section

private theorem coordinate_bound (M : Finset IntegerWavevector) (v : physicalSpace M) (k : IntegerWavevector)
    (i : Coordinate) : ‖v.1 k i‖ ≤ ‖coefficients M v‖ := by
  have paid := coordinate_square_bound M {k} v i
  simp only [Finset.sum_singleton] at paid
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp paid

private theorem weighted_row (nu : Viscosity) (M : Finset IntegerWavevector) (zero : 0 ∉ M)
    (closed : FiniteModeNegClosed M) (v : physicalSpace M) (k : IntegerWavevector) (i : Coordinate) :
    ‖v.1 k i‖ ≤ weight k*‖(laplacian M zero closed nu v).1 k i‖ := by
  by_cases nonzero : k=0
  · subst k
    rw [physical_supported v 0 zero,Pi.zero_apply,norm_zero]
    positivity [weight_pos 0]
  · have same : weight k*integerWaveViscousMultiplier k=(2*Real.pi)^2 := by
      rw [weight,if_neg nonzero,integerWaveViscousMultiplier]
      field_simp [(integerWaveNormSq_pos nonzero).ne']
    rw [laplacian_row]
    change _ ≤ weight k*‖(integerWaveViscousMultiplier k : ℝ) • v.1 k i‖
    rw [norm_smul,Real.norm_of_nonneg (integerWaveViscousMultiplier_pos ⟨k,nonzero⟩).le,← mul_assoc,same]
    apply le_mul_of_one_le_left (norm_nonneg _)
    nlinarith [Real.pi_gt_three,sq_nonneg (2*Real.pi-1)]

private theorem finite_high (nu : Viscosity) (M F : Finset IntegerWavevector) (zero : 0 ∉ M)
    (closed : FiniteModeNegClosed M) (v : physicalSpace M) (i : Coordinate) (epsilon : ℝ)
    (positive : 0 < epsilon) (small : ∑ k ∈ F,weight k^2 ≤ epsilon^2) :
    (∑ k ∈ F,‖v.1 k i‖) ≤ epsilon*‖coefficients M (laplacian M zero closed nu v)‖ := by
  let L := laplacian M zero closed nu v
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq F weight (fun k => ‖L.1 k i‖)
  have squared := cauchy.trans (mul_le_mul small (coordinate_square_bound M F L i)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg epsilon))
  have high : (∑ k ∈ F,weight k*‖L.1 k i‖) ≤ epsilon*‖coefficients M L‖ := by
    apply (sq_le_sq₀ (Finset.sum_nonneg fun k _ => mul_nonneg (weight_pos k).le (norm_nonneg _))
      (mul_nonneg positive.le (norm_nonneg _))).mp
    simpa only [mul_pow] using squared
  exact (Finset.sum_le_sum fun k _ => weighted_row nu M zero closed v k i).trans high

theorem exists_evaluate_bound (nu : Viscosity) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M F : Finset IntegerWavevector,∀ zero : 0 ∉ M,∀ closed : FiniteModeNegClosed M,
      ∀ v : physicalSpace M,∀ i : Coordinate,‖evaluate M F i v‖ ≤
        epsilon*‖coefficients M (laplacian M zero closed nu v)‖+C*‖coefficients M v‖ := by
  obtain ⟨low,tail⟩ := weight_summable.vanishing (Iio_mem_nhds (sq_pos_of_pos positive))
  refine ⟨low.card,Nat.cast_nonneg _,fun M F zero closed v i => ?_⟩
  have high := finite_high nu M (F \ low) zero closed v i epsilon positive
    (le_of_lt (tail (F \ low) (Finset.disjoint_left.mpr (fun _ member absent => (Finset.mem_sdiff.mp member).2 absent))))
  have first : (∑ k ∈ F ∩ low,‖v.1 k i‖) ≤ (low.card : ℝ)*‖coefficients M v‖ := by
    apply (Finset.sum_le_sum fun k _ => coordinate_bound M v k i).trans
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : F ∩ low ⊆ low)) (norm_nonneg _)
  have synthesis : ‖evaluate M F i v‖ ≤ ∑ k ∈ F,‖v.1 k i‖ := by
    rw [evaluate_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => basis_bound k _)
  apply synthesis.trans
  rw [← Finset.sum_inter_add_sum_sdiff F low (fun k => ‖v.1 k i‖)]
  linarith only [first,high]

end
end SaturationMonoid.NavierStokes.NativeWindowMetricGraphSynthesis

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedStaticCorrectedReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSymbolicQuantumWindow

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedBinaryRefinement
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open ActualDressedCorrectedGreen ActualDressedEMTensorClock ActualEMCarrierOwn
open ActualSourcePreparedNoetherPi ActualSourcePreparedStaticCorrectedReturn
open LowEnergy.ActualSourceQuantumCoefficientErrorOwn Filter Set
open scoped Topology BigOperators Matrix

private theorem approximation_limit (a : ℕ → ℂ) (z : ℂ) (E : ℕ → ℝ)
    (bound : ∀k, ‖a k-z‖ ≤ E k) (decay : Tendsto E atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 z) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm] using squeeze_zero (fun k => norm_nonneg (a k-z)) bound decay

theorem source_prepared_cleared_matrix (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) :
    (commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0)) =
      sourceStaticCommonDenominator event epsilon sigma n • sourcePreparedStaticPencil event epsilon sigma n := by
  rw [source_prepared_static_pencil_actual event epsilon sigma n positive]
  exact (actual_common_ir_pencil_clear event n epsilon sigma 0 positive).symm

theorem source_binary_entry_error_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (i j : Fin 289) :
    Tendsto (fun bits => sourceStaticEntryError event epsilon sigma n bits i j) atTop (𝓝 0) := by
  unfold sourceStaticEntryError
  have decay := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2 : ℝ)) (by norm_num : (1/2 : ℝ) < 1)
  have paid := (decay.const_mul
    (896 * ActualMixedNoetherTimePriceOwn.sourceCompleteCubicNoetherPrice event
      ((epsilon^2 : ℝ) • n) (PreparationVacuumActionFieldLift.fieldUnit i)
        (PreparationVacuumActionFieldLift.fieldUnit j) / sigma^4)).const_mul
          (‖sourceStaticCommonDenominator event epsilon sigma n‖ * |sigma|)
  simpa only [mul_zero] using paid

theorem source_binary_window_entry_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) (i j : Fin 289) :
    Tendsto (fun bits => sourceStaticClearedWindow event epsilon sigma n bits i j) atTop
      (𝓝 ((commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0)) i j)) := by
  apply approximation_limit _ _ _ _ (source_binary_entry_error_limit event epsilon sigma n i j)
  intro bits
  rw [norm_sub_rev]
  exact sourceStaticClearedWindow_entry_error event epsilon sigma n positive small bits i j

def sourceExactClearedMass (event : DressedEvent) (epsilon sigma : ℝ) (n : PhysicalMomentum) : ℝ :=
  ∑i, ∑j, ‖(commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0)) i j‖

theorem source_binary_window_mass_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) :
    Tendsto (sourceClearedWindowMass event epsilon sigma n) atTop (𝓝 (sourceExactClearedMass event epsilon sigma n)) := by
  unfold sourceClearedWindowMass sourceExactClearedMass
  exact tendsto_finsetSum Finset.univ (fun i _ => tendsto_finsetSum Finset.univ
    (fun j _ => (source_binary_window_entry_limit event epsilon sigma n positive small i j).norm))

theorem source_binary_error_mass_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) : Tendsto (sourceClearedErrorMass event epsilon sigma n) atTop (𝓝 0) := by
  unfold sourceClearedErrorMass
  have paid := tendsto_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) =>
    tendsto_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) =>
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).max
        (source_binary_entry_error_limit event epsilon sigma n i j)))
  simpa only [max_self, Finset.sum_const_zero] using paid

theorem source_binary_determinant_error_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) (order : ℕ) :
    Tendsto (fun bits => sourceClearedDeterminantError event epsilon sigma n bits order) atTop (𝓝 0) := by
  unfold sourceClearedDeterminantError
  have mass := source_binary_window_mass_limit event epsilon sigma n positive small
  have error := source_binary_error_mass_limit event epsilon sigma n
  simpa only [add_zero, sub_self, mul_zero] using
    (((mass.add error).pow order).sub (mass.pow order)).const_mul (Nat.factorial order : ℝ)

theorem source_binary_window_determinant_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) :
    Tendsto (fun bits => (sourceStaticClearedWindow event epsilon sigma n bits).det) atTop
      (𝓝 (MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant event n))) := by
  apply approximation_limit _ _ _ _ (source_binary_determinant_error_limit event epsilon sigma n positive small 289)
  intro bits
  rw [norm_sub_rev]
  exact actual_source_symbolic_denominator_error event epsilon sigma n positive small bits

theorem source_binary_margin_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) :
    Tendsto (sourceCommonDeterminantMargin event epsilon sigma n) atTop
      (𝓝 ‖MvPolynomial.eval (irValues epsilon sigma 0) (commonDeterminant event n)‖) := by
  unfold sourceCommonDeterminantMargin
  simpa only [sub_zero] using (source_binary_window_determinant_limit event epsilon sigma n positive small).norm.sub
    (source_binary_determinant_error_limit event epsilon sigma n positive small 289)

theorem source_binary_margin_eventually_positive (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    ∀ᶠ bits in atTop, 0 < sourceCommonDeterminantMargin event epsilon sigma n bits := by
  have nonzero := actual_common_determinant_nonzero event epsilon sigma 0 n positive regular
  exact (source_binary_margin_limit event epsilon sigma n positive small).eventually
    (Ioi_mem_nhds (norm_pos_iff.mpr nonzero))

theorem source_binary_em_numerator_error_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) (mu nu : Fin 4) :
    Tendsto (fun bits => sourceEMNumeratorError event epsilon sigma n bits mu nu) atTop (𝓝 0) := by
  unfold sourceEMNumeratorError
  have paid := tendsto_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) =>
    tendsto_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) =>
      ((source_binary_determinant_error_limit event epsilon sigma n positive small 288).const_mul
        (‖sourceStaticCommonDenominator event epsilon sigma n‖ * ‖emInsertion i mu‖)).mul_const ‖emInsertion j nu‖))
  simpa only [mul_zero, zero_mul, Finset.sum_const_zero] using paid

theorem source_binary_em_numerator_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) (mu nu : Fin 4) :
    Tendsto (fun bits => sourceEMNumeratorWindow event epsilon sigma n bits mu nu) atTop
      (𝓝 (MvPolynomial.eval (irValues epsilon sigma 0) (commonEMTensorNumerator event n mu nu))) := by
  apply approximation_limit _ _ _ _ (source_binary_em_numerator_error_limit event epsilon sigma n positive small mu nu)
  intro bits
  rw [norm_sub_rev]
  exact actual_source_EM16_numerator_error event epsilon sigma n positive small bits mu nu

theorem source_binary_em_read_error_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (mu nu : Fin 4) :
    Tendsto (fun bits => sourceEMBinaryReadError event epsilon sigma n bits mu nu) atTop (𝓝 0) := by
  have determinant := norm_ne_zero_iff.mpr
    (actual_common_determinant_nonzero event epsilon sigma 0 n positive regular)
  have margin := source_binary_margin_limit event epsilon sigma n positive small
  have de := source_binary_determinant_error_limit event epsilon sigma n positive small 289
  have ne := source_binary_em_numerator_error_limit event epsilon sigma n positive small mu nu
  have numerator := (source_binary_em_numerator_limit event epsilon sigma n positive small mu nu).norm
  unfold sourceEMBinaryReadError
  have paid := (ne.add ((numerator.mul de).div margin determinant)).div margin determinant
  simp only [mul_zero, zero_div, add_zero] at paid
  apply Tendsto.congr' _ paid
  exact Filter.Eventually.of_forall (fun _ => rfl)

end LowEnergy.GaussComposite.ActualSourcePreparedBinaryRefinement

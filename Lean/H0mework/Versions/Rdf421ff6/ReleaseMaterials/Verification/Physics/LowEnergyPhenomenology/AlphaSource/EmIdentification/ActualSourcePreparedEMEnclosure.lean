import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedBinaryRefinement

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMEnclosure
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedEMTensorClock
open ActualDressedUniformMaterialCoefficients ActualEMCarrierOwn ActualEMResponseSplit
open LowEnergy.GaussComposite.ActualDressedVisiblePole
open ActualSourcePreparedStaticCorrectedReturn ActualSourcePreparedBinaryRefinement
open LowEnergy.ActualSourceQuantumCoefficientErrorOwn Filter Set
open scoped Topology BigOperators Matrix

theorem source_binary_green_numerator_error_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) :
    Tendsto (sourceFullGreenNumeratorError event epsilon sigma n) atTop (𝓝 0) := by
  unfold sourceFullGreenNumeratorError
  simpa only [mul_zero] using (source_binary_determinant_error_limit event epsilon sigma n positive small 288).const_mul
    ‖sourceStaticCommonDenominator event epsilon sigma n‖

theorem source_binary_green_numerator_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2) (i j : Fin 289) :
    Tendsto (fun bits => sourceFullGreenNumeratorWindow event epsilon sigma n bits i j) atTop
      (𝓝 (sourceStaticCommonDenominator event epsilon sigma n *
        ((commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0))).adjugate i j)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have bound (bits : ℕ) :
      ‖sourceFullGreenNumeratorWindow event epsilon sigma n bits i j -
        sourceStaticCommonDenominator event epsilon sigma n *
          ((commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0))).adjugate i j‖ ≤
        sourceFullGreenNumeratorError event epsilon sigma n bits := by
    unfold sourceFullGreenNumeratorWindow sourceFullGreenNumeratorError
    rw [← mul_sub, norm_mul, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left
      (actual_source_adjugate_entry_error event epsilon sigma n positive small bits i j) (norm_nonneg _)
  simpa only [dist_eq_norm] using squeeze_zero (fun _ => norm_nonneg _) bound
    (source_binary_green_numerator_error_limit event epsilon sigma n positive small)

theorem source_binary_green_read_error_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (i j : Fin 289) :
    Tendsto (fun bits => sourceFullGreenBinaryError event epsilon sigma n bits i j) atTop (𝓝 0) := by
  have determinant := norm_ne_zero_iff.mpr
    (actual_common_determinant_nonzero event epsilon sigma 0 n positive regular)
  have margin := source_binary_margin_limit event epsilon sigma n positive small
  have de := source_binary_determinant_error_limit event epsilon sigma n positive small 289
  have ne := source_binary_green_numerator_error_limit event epsilon sigma n positive small
  have numerator := (source_binary_green_numerator_limit event epsilon sigma n positive small i j).norm
  unfold sourceFullGreenBinaryError
  have paid := (ne.add ((numerator.mul de).div margin determinant)).div margin determinant
  simp only [mul_zero, zero_div, add_zero] at paid
  apply Tendsto.congr' _ paid
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- One source budget retains all complete-field and all electromagnetic errors. -/
def sourcePreparedBinaryTotalError (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (bits : ℕ) : ℝ :=
  (∑mu : Fin 4, ∑nu : Fin 4, max 0 (sourceEMBinaryReadError event epsilon sigma n bits mu nu)) +
    ∑i : Fin 289, ∑j : Fin 289, max 0 (sourceFullGreenBinaryError event epsilon sigma n bits i j)

theorem source_binary_total_error_limit (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    Tendsto (sourcePreparedBinaryTotalError event epsilon sigma n) atTop (𝓝 0) := by
  unfold sourcePreparedBinaryTotalError
  have em := tendsto_finsetSum Finset.univ (fun mu (_ : mu ∈ Finset.univ) =>
    tendsto_finsetSum Finset.univ (fun nu (_ : nu ∈ Finset.univ) =>
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).max
        (source_binary_em_read_error_limit event epsilon sigma n positive small regular mu nu)))
  have green := tendsto_finsetSum Finset.univ (fun i (_ : i ∈ Finset.univ) =>
    tendsto_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) =>
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).max
        (source_binary_green_read_error_limit event epsilon sigma n positive small regular i j)))
  simpa only [max_self, Finset.sum_const_zero, add_zero] using em.add green

/-- Original regularity generates a finite window with positive computed margin
and requested accuracy; neither price nor positive margin is supplied. -/
theorem source_binary_precision_exists (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) :
    ∃ bits, 0 < sourceCommonDeterminantMargin event epsilon sigma n bits ∧
      sourcePreparedBinaryTotalError event epsilon sigma n bits < tolerance := by
  have margin := source_binary_margin_eventually_positive event epsilon sigma n positive small regular
  have error := (source_binary_total_error_limit event epsilon sigma n positive small regular).eventually
    (Iio_mem_nhds accurate)
  exact (margin.and error).exists

def sourcePreparedBinaryBits (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) : ℕ := by
  classical
  exact Nat.find (source_binary_precision_exists event epsilon sigma n positive small regular tolerance accurate)

theorem source_binary_generated_precision (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) :
    let bits := sourcePreparedBinaryBits event epsilon sigma n positive small regular tolerance accurate
    0 < sourceCommonDeterminantMargin event epsilon sigma n bits ∧
      sourcePreparedBinaryTotalError event epsilon sigma n bits < tolerance := by
  classical
  exact Nat.find_spec (source_binary_precision_exists event epsilon sigma n positive small regular tolerance accurate)

private theorem entry_le_mass {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → κ → ℝ) (i : ι) (j : κ) :
    a i j ≤ ∑r, ∑s, max 0 (a r s) := by
  classical
  exact (le_max_right _ _).trans
    ((Finset.single_le_sum (fun s _ => le_max_left 0 (a i s)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun r _ => Finset.sum_nonneg (fun s _ => le_max_left 0 (a r s))) (Finset.mem_univ i)))

/-- This is the cofactor read of the generated prepared response matrix, not a
new propagator. Its identity with the original Green is paid below. -/
def sourcePreparedFullGreenRead (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ℂ :=
  (sourcePreparedStaticPencil event epsilon sigma n).det⁻¹ •
    (sourcePreparedStaticPencil event epsilon sigma n).adjugate

theorem source_prepared_full_green_original (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourcePreparedFullGreenRead event epsilon sigma n = correctedGreen event epsilon 0 sigma n := by
  have inverse := (source_prepared_static_green_inverse event epsilon sigma n positive regular).2
  have original := Matrix.inv_eq_left_inv inverse
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv', sourcePreparedFullGreenRead] using original

def sourcePreparedEMTensorRead (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  emResponseTensor (sourcePreparedFullGreenRead event epsilon sigma n)

theorem source_prepared_em_tensor_original (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) :
    sourcePreparedEMTensorRead event epsilon sigma n = correctedEMTensor event epsilon 0 sigma n := by
  unfold sourcePreparedEMTensorRead correctedEMTensor
  rw [source_prepared_full_green_original event epsilon sigma n positive regular]

/-- All 289 Green entries and all 16 EM entries receive the same generated
window and requested tolerance from the actual prepared full response. -/
theorem source_prepared_generated_enclosure (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 2)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (tolerance : ℝ) (accurate : 0 < tolerance) :
    let bits := sourcePreparedBinaryBits event epsilon sigma n positive small regular tolerance accurate
    (∀i j, ‖sourcePreparedFullGreenRead event epsilon sigma n i j-
      sourceFullGreenBinaryRead event epsilon sigma n bits i j‖ < tolerance) ∧
    (∀mu nu, ‖sourcePreparedEMTensorRead event epsilon sigma n mu nu-
      sourceEMBinaryRead event epsilon sigma n bits mu nu‖ < tolerance) := by
  dsimp only
  let bits := sourcePreparedBinaryBits event epsilon sigma n positive small regular tolerance accurate
  have paid := source_binary_generated_precision event epsilon sigma n positive small regular tolerance accurate
  change 0 < sourceCommonDeterminantMargin event epsilon sigma n bits ∧
    sourcePreparedBinaryTotalError event epsilon sigma n bits < tolerance at paid
  have em_nonnegative : 0 ≤ ∑mu : Fin 4, ∑nu : Fin 4,
      max 0 (sourceEMBinaryReadError event epsilon sigma n bits mu nu) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  have green_nonnegative : 0 ≤ ∑i : Fin 289, ∑j : Fin 289,
      max 0 (sourceFullGreenBinaryError event epsilon sigma n bits i j) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_left _ _))
  constructor
  · intro i j
    rw [source_prepared_full_green_original event epsilon sigma n positive regular]
    apply (actual_source_full289_green_binary_error event epsilon sigma n positive small bits paid.1 i j).trans_lt
    apply lt_of_le_of_lt (entry_le_mass (fun r s => sourceFullGreenBinaryError event epsilon sigma n bits r s) i j)
    exact lt_of_le_of_lt (le_add_of_nonneg_left em_nonnegative) paid.2
  · intro mu nu
    rw [source_prepared_em_tensor_original event epsilon sigma n positive regular]
    apply (actual_source_EM16_binary_read_error event epsilon sigma n positive small bits paid.1 mu nu).trans_lt
    apply lt_of_le_of_lt (entry_le_mass (fun r s => sourceEMBinaryReadError event epsilon sigma n bits r s) mu nu)
    exact lt_of_le_of_lt (le_add_of_nonneg_right green_nonnegative) paid.2

end LowEnergy.GaussComposite.ActualSourcePreparedEMEnclosure

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalQuantumWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumPrice
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumGaugeSourceInjection ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualEMDressedSchur ActualDressedNullNative ActualDressedSylvester ActualDressedSignal
open ActualDressedConstraintWard ActualDressedNativeConstraint ActualDressedPencil
open ActualSourcePreparedTemporalQuantumWard ActualSourcePreparedNoetherPi
open scoped Matrix BigOperators Topology Interval

/-- The actual field mass is retained; no unit-current or unit-Green premise. -/
def sourceTemporalConstraintPairMass (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (row : Fin 9) : ℝ :=
  (∑ i : Fin 289, ‖originalNullColumn (-(frequencyRay epsilon 0 n)) row i‖) *
    (∑ j : Fin 289, ‖sourceTemporalCorrectedField event epsilon sigma n j‖)

private theorem entry_contraction_bound (M : Matrix (Fin 289) (Fin 289) ℂ)
    (l a : Fin 289 → ℂ) (price : ℝ) (entries : ∀ i j, ‖M i j‖ ≤ price) :
    ‖dotProduct l (M*ᵥa)‖ ≤ (∑ i, ‖l i‖)*(∑ j, ‖a j‖)*price := by
  unfold dotProduct Matrix.mulVec
  calc
    _ ≤ ∑ i, ‖l i * ∑ j, M i j*a j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖l i‖*‖M i j‖*‖a j‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      calc
        _ ≤ ‖l i‖*(∑ j, ‖M i j*a j‖) :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
        _ = _ := by simp only [norm_mul, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ i, ∑ j, ‖l i‖*price*‖a j‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (entries i j) (norm_nonneg _)) (norm_nonneg _)
    _ = (∑ i, ‖l i‖)*(∑ j, ‖a j‖)*price := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Finite-window constraint error is priced by the actual source tail and
both source-generated reader/field masses, keeping the complete history. -/
theorem source_temporal_quantum_window_price (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (row : Fin 9)
    (T : ℝ) (future : 0 ≤ T) :
    ‖sourceCokernel (frequencyRay epsilon 0 n)
      (dressedWindowPolarization event ((epsilon^2 : ℝ) • n) (frequencyRay epsilon 0 n) (sigma : ℂ) T*ᵥ
        sourceTemporalCorrectedField event epsilon sigma n) row‖ ≤
      sourceTemporalConstraintPairMass event epsilon sigma n row *
        dressedSignalTailPrice event ((epsilon^2 : ℝ) • n) (frequencyRay epsilon 0 n) (sigma : ℂ) T := by
  let p := frequencyRay epsilon 0 n
  let a := sourceTemporalCorrectedField event epsilon sigma n
  let full : Matrix (Fin 289) (Fin 289) ℂ :=
    fun i j => sourcePreparedPiEntry event ((epsilon^2 : ℝ) • n) (sigma : ℂ) i j
  let window := dressedWindowPolarization event ((epsilon^2 : ℝ) • n) p (sigma : ℂ) T
  let tail := dressedSignalTailPrice event ((epsilon^2 : ℝ) • n) p (sigma : ℂ) T
  have static : p 0=0 := by
    change -Complex.I*((0*epsilon^2 : ℝ) : ℂ)=0
    simp only [zero_mul, Complex.ofReal_zero, mul_zero]
  have zero : sourceCokernel p (full*ᵥa) row = 0 := by
    simpa only [Pi.zero_apply] using
      congrFun (source_temporal_quantum_cokernel event epsilon sigma n positive regular) row
  have exactDifference : sourceCokernel p (window*ᵥa) row =
      sourceCokernel p ((window-full)*ᵥa) row := by
    rw [Matrix.sub_mulVec, map_sub, Pi.sub_apply, zero, sub_zero]
  have entries : ∀ i j, ‖(window-full) i j‖ ≤ tail := by
    intro i j
    rw [Matrix.sub_apply, norm_sub_rev]
    exact source_prepared_pi_tail event ((epsilon^2 : ℝ) • n) p static (sigma : ℂ)
      (by simpa using positive) T future i j
  change ‖sourceCokernel p (window*ᵥa) row‖ ≤ _
  rw [exactDifference, original_null_cokernel]
  exact entry_contraction_bound (window-full) (originalNullColumn (-p) row) a tail entries

/-- The native Ward and reference-deviation integral is the very same priced
finite-window constraint; contact is not removed from either history. -/
theorem source_temporal_quantum_history_price (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event epsilon 0 sigma n ≠ 0) (row : Fin 9)
    (T : ℝ) (future : 0 ≤ T) :
    ‖∫t in (0 : ℝ)..T, laplaceWeight (sigma : ℂ) t *
      (nativeConstraintHistory event ((epsilon^2 : ℝ) • n) (frequencyRay epsilon 0 n) row
        (sourceTemporalCorrectedField event epsilon sigma n) t -
      nativeConstraintDeviation event ((epsilon^2 : ℝ) • n) (frequencyRay epsilon 0 n) row
        (sourceTemporalCorrectedField event epsilon sigma n) t)‖ ≤
      sourceTemporalConstraintPairMass event epsilon sigma n row *
        dressedSignalTailPrice event ((epsilon^2 : ℝ) • n) (frequencyRay epsilon 0 n) (sigma : ℂ) T := by
  rw [←source_constraint_native_history]
  exact source_temporal_quantum_window_price event epsilon sigma n positive regular row T future

end LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumPrice

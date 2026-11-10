import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMPhaseField
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTemporalSigmaTwo

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMTemporalFreeReturn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic
open ActualDressedFullCoulomb ActualDressedSylvester ActualDressedEMTemporal ActualDressedNoether
open ActualSourcePreparedEMPhaseField ActualSourcePreparedNoetherPi
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedN3MovingResponse
open PreparationVacuumActionFieldLift PreparationVacuumJointFieldResponse
open scoped Matrix BigOperators
attribute [local irreducible] sourcePreparedPiEntry dressedStaticPolarization
  sourceTemporalCorrectedField emTemporalPrice sourcePreparedClockQuantumMatrix

def sourcePreparedEMTemporalPi (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (j : Fin 289) : ℂ :=
  ∑ i : Fin 289, sourceTemporalEMForce i * sourcePreparedPiEntry event transfer lambda i j

/-- The actual EM row and the already generated temporal row are restrictions
of the same source response, at the same preparation, momentum and clock. -/
theorem source_prepared_em_temporal_pi_original (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (j : Fin 289) :
    sourcePreparedEMTemporalPi event transfer lambda j = emTemporalPi event transfer lambda j := by
  unfold sourcePreparedEMTemporalPi emTemporalPi
  rw [source_temporal_force_phase]
  simp_rw [source_prepared_pi_actual event transfer lambda positive]

/-- The original four free-leg variations compute the complete actual EM jet.
The original raw/contact differences remain in the full Noether return. -/
theorem source_actual_em_temporal_four_words (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    ∑ i : Fin 289, sourceTemporalEMForce i *
      (dressedNoetherJet event transfer (fun _ => ⟨force,0,0⟩) age i).value =
      dressedEulerObserver event (emFreeSlope event transfer force age) := by
  rw [source_temporal_force_phase]
  exact actual_em_temporal_jet_free event transfer force age

/-- The stronger original sigma-two source price feeds actual prepared Pi,
without a field norm, charge eigenstate or zero-clock balance premise. -/
theorem source_prepared_em_temporal_pi_two_clock_price (event : DressedEvent)
    (transfer : PhysicalMomentum) (sigma : ℝ) (positive : 0 < sigma) (small : sigma ≤ 1)
    (j : Fin 289) :
    sigma^2 * ‖sourcePreparedEMTemporalPi event transfer (sigma : ℂ) j‖ ≤
      2 * emTemporalPrice event transfer (fieldUnit j) := by
  have paid : 0 < (sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positive
  rw [source_prepared_em_temporal_pi_original event transfer (sigma : ℂ) paid j]
  exact actual_em_temporal_pi_sigma_two_price event transfer sigma positive small j

private theorem matrix_reader {ι : Type*} [Fintype ι] (E a : ι → ℂ) (P : Matrix ι ι ℂ) :
    dotProduct E (P *ᵥ a) = ∑ j, (∑ i, E i * P i j) * a j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The complete original sigma Pi G E0 drive directly consumes all 289
columns of this same EM row, retaining the actual varying source field. -/
theorem source_temporal_quantum_em_driver_return (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) :
    dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n) =
      (sigma : ℂ) * ∑ j : Fin 289, sourcePreparedEMTemporalPi event (e.val^2 • n) (sigma : ℂ) j *
        sourceTemporalCorrectedField event e.val sigma n j := by
  unfold sourceTemporalActualQuantumDriver sourcePreparedClockQuantumMatrix
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, matrix_reader]
  rfl

private theorem finite_row_price {ι : Type*} [Fintype ι]
    (P a : ι → ℂ) (B : ι → ℝ) (sigma : ℝ) (positive : 0 < sigma)
    (price : ∀ j, sigma^2 * ‖P j‖ ≤ 2 * B j) :
    sigma * ‖(sigma : ℂ) * ∑ j, P j * a j‖ ≤ 2 * ∑ j, B j * ‖a j‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ = sigma^2 * ‖∑ j, P j * a j‖ := by ring
    _ ≤ sigma^2 * ∑ j, ‖P j * a j‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (sq_nonneg _)
    _ = ∑ j, (sigma^2 * ‖P j‖) * ‖a j‖ := by simp only [norm_mul, Finset.mul_sum, mul_assoc]
    _ ≤ ∑ j, (2 * B j) * ‖a j‖ :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (price j) (norm_nonneg _))
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

theorem source_temporal_quantum_em_driver_clock_price (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 1) :
    sigma * ‖dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n)‖ ≤
      2 * ∑ j : Fin 289, emTemporalPrice event (e.val^2 • n) (fieldUnit j) *
        ‖sourceTemporalCorrectedField event e.val sigma n j‖ := by
  rw [source_temporal_quantum_em_driver_return]
  exact finite_row_price _ _ _ sigma positive
    (source_prepared_em_temporal_pi_two_clock_price event (e.val^2 • n) sigma positive small)

end LowEnergy.GaussComposite.ActualSourcePreparedEMTemporalFreeReturn

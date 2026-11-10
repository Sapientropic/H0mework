import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumDriverPrice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.CompleteSourceNoetherPrice

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedQuantumNoetherPrice
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumActionFieldLift PreparationVacuumFullOriginResponse PreparationVacuumMixedPrincipal
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedNoetherCoulombUnit ActualDressedStaticResponse
open ActualDressedSylvester
open ActualSourcePreparedNoetherPi ActualSourcePreparedN3MovingResponse ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumIR
open ActualSourcePreparedQuantumDriverCofactor
open ActualSourcePreparedN3EMChargeRead ActualSourcePreparedStaticNativeConstraint
open LowEnergy.ActualMixedNoetherTimePriceOwn
open scoped Matrix BigOperators Matrix.Norms.Operator

private theorem contracted_price (A : Matrix (Fin 289) (Fin 289) ℂ) (v : Fin 289 → ℂ)
    (P : Matrix (Fin 289) (Fin 289) ℝ) (s : ℝ) (positive : 0 < s)
    (nonnegative : ∀ i j, 0 ≤ P i j) (entry : ∀ i j, s^4*‖A i j‖ ≤ 56*P i j) :
    s^4*‖A*ᵥv‖ ≤ 56*∑ i, ∑ j, P i j*‖v j‖ := by
  have row (i : Fin 289) : s^4*‖(A*ᵥv) i‖ ≤ 56*∑ j, P i j*‖v j‖ := by
    have sum_price := norm_sum_le Finset.univ (fun j => A i j*v j)
    calc
      _ ≤ s^4*∑ j, ‖A i j*v j‖ := mul_le_mul_of_nonneg_left sum_price (by positivity)
      _ = ∑ j, (s^4*‖A i j‖)*‖v j‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul]
        ring
      _ ≤ ∑ j, (56*P i j)*‖v j‖ :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (entry i j) (norm_nonneg _))
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have mass_nonnegative (i : Fin 289) : 0 ≤ ∑ j, P i j*‖v j‖ :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (nonnegative i j) (norm_nonneg _))
  have cap (i : Fin 289) : ‖(A*ᵥv) i‖ ≤ (56*∑ i, ∑ j, P i j*‖v j‖)/s^4 := by
    apply (le_div_iff₀ (pow_pos positive 4)).mpr
    rw [mul_comm]
    exact (row i).trans (mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => mass_nonnegative j) (Finset.mem_univ i)) (by norm_num))
  have bound := (pi_norm_le_iff_of_nonneg (show 0 ≤ (56*∑ i, ∑ j, P i j*‖v j‖)/s^4 by
    exact div_nonneg (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mass_nonnegative i)))
      (by positivity))).mpr cap
  exact (mul_comm _ _).trans_le ((le_div_iff₀ (pow_pos positive 4)).mp bound)

def sourceQuantumNoetherMass (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) : ℝ :=
  ∑ i, ∑ j, sourceCompleteCubicNoetherPrice event (e.val^2 • n) (fieldUnit i) (fieldUnit j)*
    ‖sourceTemporalCorrectedField event e.val sigma n j‖

/-- The full source Noether/contact price contracts with the actual corrected
field. Both current legs and every one of the 289 output rows remain present. -/
theorem source_quantum_noether_driver_price (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma) (small : sigma ≤ 1) :
    sigma^3*‖sourceTemporalActualQuantumDriver event e sigma n‖ ≤
      56*sourceQuantumNoetherMass event e sigma n := by
  let A : Matrix (Fin 289) (Fin 289) ℂ :=
    Matrix.of (fun i j => sourcePreparedPiEntry event (e.val^2 • n) (sigma:ℂ) i j)
  let P : Matrix (Fin 289) (Fin 289) ℝ :=
    fun i j => sourceCompleteCubicNoetherPrice event (e.val^2 • n) (fieldUnit i) (fieldUnit j)
  have clock : 0 < (sigma:ℂ).re := by simpa only [Complex.ofReal_re] using positive
  have entry (i j : Fin 289) : sigma^4*‖A i j‖ ≤ 56*P i j := by
    rw [show A i j = dressedStaticPolarization event (e.val^2 • n) (sigma:ℂ) i j from
      source_prepared_pi_actual event _ _ clock i j]
    exact actual_static_polarization_source_sigma_four_price event _ sigma positive small i j
  have paid := contracted_price A (sourceTemporalCorrectedField event e.val sigma n) P sigma positive
    (fun i j => sourceCompleteCubicNoetherPrice_nonnegative event _ (fieldUnit i) (fieldUnit j)) entry
  have scale : sigma^3*‖(sigma:ℂ) • (A*ᵥsourceTemporalCorrectedField event e.val sigma n)‖ =
      sigma^4*‖A*ᵥsourceTemporalCorrectedField event e.val sigma n‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    ring
  simp only [sourceTemporalActualQuantumDriver, sourcePreparedClockQuantumMatrix, Matrix.smul_mulVec]
  change sigma^3*‖(sigma:ℂ) • (A*ᵥsourceTemporalCorrectedField event e.val sigma n)‖ ≤ _
  rw [scale]
  exact paid

theorem source_quantum_noether_native_reader_price (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (clock_small : sigma ≤ 1) :
    sigma^3*‖sourceSpatialStaticSourceReader n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩
      (sourceTemporalActualQuantumDriver event e sigma n)‖ ≤
        ‖sourceQuantumNativeReader e n unit small‖*(56*sourceQuantumNoetherMass event e sigma n) := by
  rw [←source_quantum_native_reader_actual e n unit small (sourceTemporalActualQuantumDriver event e sigma n)]
  have applied := Matrix.linfty_opNorm_mulVec (sourceQuantumNativeReader e n unit small)
    (sourceTemporalActualQuantumDriver event e sigma n)
  have multiplied := mul_le_mul_of_nonneg_left applied (pow_pos positive 3).le
  calc
    _ ≤ sigma^3*(‖sourceQuantumNativeReader e n unit small‖*‖sourceTemporalActualQuantumDriver event e sigma n‖) := multiplied
    _ = ‖sourceQuantumNativeReader e n unit small‖*(sigma^3*‖sourceTemporalActualQuantumDriver event e sigma n‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (source_quantum_noether_driver_price event e sigma n positive clock_small)
      (norm_nonneg _)

/-- The source cubic five-arm price pays the actual reader in the original
native IR error, keeping the full regular/contact/complement read separate. -/
theorem source_quantum_noether_ir_price (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (clock_small : sigma ≤ 1)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, small⟩
    let driver := sourceTemporalActualQuantumDriver event e sigma n
    sigma^3*‖-(e.val:ℂ)^4*(sourceN3TemporalEMCoefficient event e.val sigma n -
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceNativeStaticMatrix e.val n*ᵥsourceTemporalEMForce)-
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceSpatialStaticRegularField n unit kappa driver))-
      noetherPairScale^2*dotProduct sourceTemporalEMForce (sourceSpatialStaticPoleCoefficient n unit kappa driver)‖ ≤
      ‖noetherPairScale^2‖*((∑ i, ‖sourceTemporalEMForce i‖)*
        ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa)‖*
        (2*staticInverseBudget^2*effectiveErrorBudget*kappa.val)*
        ‖sourceQuantumNativeReader e n unit small‖*(56*sourceQuantumNoetherMass event e sigma n)) := by
  have original := source_temporal_quantum_spatial_pole_price event e sigma n unit small positive regular
  have reader := source_quantum_noether_native_reader_price event e sigma n unit small positive clock_small
  have paid := mul_le_mul_of_nonneg_left original (pow_pos positive 3).le
  have error_nonnegative := effectiveErrorBudget_nonneg
  apply paid.trans
  have scale_paid := mul_le_mul_of_nonneg_left reader
    (show 0 ≤ ‖noetherPairScale^2‖*((∑ i, ‖sourceTemporalEMForce i‖)*
      ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit ⟨e.val^2, pow_pos e.property.1 2, small⟩)‖*
      (2*staticInverseBudget^2*effectiveErrorBudget*e.val^2)) by positivity)
  convert scale_paid using 1 <;> ring

end LowEnergy.GaussComposite.ActualSourcePreparedQuantumNoetherPrice

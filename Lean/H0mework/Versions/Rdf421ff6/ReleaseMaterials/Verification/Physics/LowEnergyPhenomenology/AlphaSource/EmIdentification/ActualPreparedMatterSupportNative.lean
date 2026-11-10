import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterSupportPi
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedReducedQuantumCofactor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMPhaseField
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedQuantumColumnClock
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedStaticCorrectedReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterSupport
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open GaussCoreHilbert GaussHistoryHilbert GaussQuantumMultiplier GaussUnitaryHistory
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumGaugeSourceInjection
open PreparationVacuumOriginalGreenFeedback
open ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR ActualSourcePreparedN3MovingResponse
open ActualSourcePreparedEMPhaseField ActualSourcePreparedReducedQuantumCofactor
open ActualSourcePreparedQuantumColumnClock ActualSourcePreparedStaticCorrectedReturn
open ActualSourcePreparedNoetherPi
open ActualEMCarrierOwn ActualEMAction ActualEMDressedSchur ActualEMDressedConstraint
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval

/-- Gauge slots lie strictly inside the active block 9..57, hence are disjoint
from every source-inactive coordinate. -/
private theorem inactive_ne_gauge_slot (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val)
    (mu : Fin 4) (a : Fin 12) : gaugeSlot mu a ≠ i := by
  intro same
  have val := congrArg Fin.val same
  change 9 + 12 * mu.val + a.val = i.val at val
  have := mu.isLt
  have := a.isLt
  omega

/-- The original temporal EM force has zero inactive coordinates: the source
phase field lives entirely inside the active gauge block. -/
theorem actual_em_force_inactive_zero (i : Fin 289) (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) :
    sourceTemporalEMForce i = 0 := by
  have real : (sourcePhaseGaugeField 0) i = 0 := by
    unfold sourcePhaseGaugeField
    simp only [Finset.sum_apply, Pi.smul_apply, gaugeField, Pi.single_apply]
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg (Ne.symm (inactive_ne_gauge_slot i outside 0 a))]
    simp
  rw [show sourceTemporalEMForce i = (sourcePhaseGaugeField 0 i : ℂ) from
    congrFun source_temporal_force_phase i, real]
  simp

/-- The actual native field equation on each source-inactive coordinate: the
original static pencil row reads zero, since the prepared Pi row and the EM
force both vanish there while the actual field stays whole. -/
theorem actual_native_inactive_field_equation (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (i : Fin 289)
    (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) :
    (emOriginalJacobi (frequencyRay e.val 0 n) *ᵥ
      sourceTemporalCorrectedField event e.val sigma n) i = 0 := by
  have pos : 0 < (sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positive
  have equation := congrFun
    (source_temporal_corrected_field_equation event e.val sigma n positive regular) i
  have row_zero : (sourcePreparedClockQuantumMatrix event e.val sigma n *ᵥ
      sourceTemporalCorrectedField event e.val sigma n) i = 0 := by
    simp only [sourcePreparedClockQuantumMatrix, Matrix.mulVec, dotProduct,
      Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    apply Finset.sum_eq_zero
    intro j _
    rw [actual_prepared_inactive_pi_row event ((e.val^2 : ℝ) • n) (sigma : ℂ) pos i outside j]
    simp
  have pencil : sourcePreparedStaticPencil event e.val sigma n =
      emOriginalJacobi (frequencyRay e.val 0 n) -
        sourcePreparedClockQuantumMatrix event e.val sigma n := by
    unfold sourcePreparedStaticPencil sourcePreparedClockQuantumMatrix
    rfl
  rw [pencil, Matrix.sub_mulVec, Pi.sub_apply, row_zero, sub_zero,
    actual_em_force_inactive_zero i outside] at equation
  exact equation

/-- The reduced driver numerator vanishes on each source-inactive coordinate:
the original determinant-cleared drive hits the zero driver row. -/
theorem actual_native_inactive_driver_cofactor (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (i : Fin 289)
    (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) :
    sourceReducedClockDriverNumerator event n e.val sigma i = 0 := by
  have clear := congrFun
    (source_reduced_clock_actual_driver_clear event n e sigma positive regular) i
  rw [Pi.smul_apply, smul_eq_mul,
    actual_quantum_driver_inactive_zero event e sigma n positive i outside, mul_zero] at clear
  exact clear.symm

/-- Highest consumer: the actual full-field numerator row of the original
native Jacobi vanishes on each source-inactive coordinate, including the four
primal/dual background slots 76, 82, 100, 106. Same fieldNum, same determinant,
no additional adjugate or denominator premise. -/
theorem actual_native_inactive_field_cofactor (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0 < sigma)
    (regular : correctedDet event e.val 0 sigma n ≠ 0) (i : Fin 289)
    (outside : (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val) :
    (emOriginalJacobi (frequencyRay e.val 0 n) *ᵥ
      sourceReducedClockFieldNumerator event n e.val sigma) i = 0 := by
  have driver := actual_native_inactive_driver_cofactor event e sigma n positive regular i outside
  unfold sourceReducedClockDriverNumerator at driver
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    actual_em_force_inactive_zero i outside, mul_zero, sub_zero] at driver
  exact driver

end LowEnergy.GaussComposite.ActualPreparedMatterSupport

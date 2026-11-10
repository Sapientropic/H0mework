import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalQuantumRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumIR
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumMixedPrincipal
open PreparationVacuumPhysicalCharacteristic PreparationVacuumFullOriginResponse
open PreparationVacuumOriginalGreenFeedback PreparationVacuumStaticPoleResponse
open PreparationPhysicalStaticSpatialCouplingReturn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedNoetherCoulombUnit
open ActualSourcePreparedN3MovingResponse ActualSourcePreparedN3EMChargeRead ActualSourcePreparedStaticNativeConstraint
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumRead
open scoped Matrix BigOperators Matrix.Norms.Operator

def sourceTemporalActualQuantumDriver (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) : Fin 289 → ℂ :=
  sourcePreparedClockQuantumMatrix event e.val sigma n*ᵥsourceTemporalCorrectedField event e.val sigma n

private theorem contraction (D v w z : Fin 289 → ℂ) (a : ℂ) :
    a*(dotProduct D v-dotProduct D w)-dotProduct D z =
      ∑ i, D i*(a*(v i-w i)-z i) := by
  simp only [dotProduct, mul_sub, Finset.mul_sum, ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual quantum drive consumes the original native spatial pole and
O(epsilon squared) inverse price. Its complete contact/complement read and its
own possibly varying source-reader norm remain explicit. -/
theorem source_temporal_quantum_spatial_pole_price (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (small : e.val^2 ≤ staticRadius)
    (positive : 0 < sigma) (regular : correctedDet event e.val 0 sigma n ≠ 0) :
    let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, small⟩
    let driver := sourceTemporalActualQuantumDriver event e sigma n
    ‖-(e.val : ℂ)^4 * (sourceN3TemporalEMCoefficient event e.val sigma n -
        noetherPairScale^2 * dotProduct sourceTemporalEMForce
          (sourceNativeStaticMatrix e.val n*ᵥsourceTemporalEMForce) -
        noetherPairScale^2 * dotProduct sourceTemporalEMForce
          (sourceSpatialStaticRegularField n unit kappa driver)) -
      noetherPairScale^2 * dotProduct sourceTemporalEMForce
        (sourceSpatialStaticPoleCoefficient n unit kappa driver)‖ ≤
      ‖noetherPairScale^2‖ * ((∑ i, ‖sourceTemporalEMForce i‖) *
        ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa)‖ *
        (2*staticInverseBudget^2*effectiveErrorBudget*kappa.val) *
        ‖sourceSpatialStaticSourceReader n unit kappa driver‖) := by
  let kappa : staticDomain := ⟨e.val^2, pow_pos e.property.1 2, small⟩
  let driver := sourceTemporalActualQuantumDriver event e sigma n
  dsimp only
  rw [source_temporal_actual_quantum_read event e sigma n unit small positive regular]
  change ‖-(e.val : ℂ)^4 * (noetherPairScale^2 * dotProduct sourceTemporalEMForce
      (sourceNativeStaticMatrix e.val n*ᵥdriver) - noetherPairScale^2 *
      dotProduct sourceTemporalEMForce (sourceSpatialStaticRegularField n unit kappa driver)) -
    noetherPairScale^2 * dotProduct sourceTemporalEMForce
      (sourceSpatialStaticPoleCoefficient n unit kappa driver)‖ ≤ _
  have native : sourceNativeStaticMatrix e.val n*ᵥdriver = sourceSpatialStaticNativeField n unit kappa driver := by
    simp only [source_native_static_original e n unit small, sourceSpatialStaticNativeField,
      PreparationVacuumOriginalGreenFeedback.sourceField, kappa]
  have scale : -(e.val : ℂ)^4 = -(kappa.val : ℂ)^2 := by
    change -(e.val : ℂ)^4 = -((e.val^2 : ℝ) : ℂ)^2
    push_cast
    ring
  have generated :
      ‖-(e.val : ℂ)^4 * (dotProduct sourceTemporalEMForce (sourceNativeStaticMatrix e.val n*ᵥdriver) -
        dotProduct sourceTemporalEMForce (sourceSpatialStaticRegularField n unit kappa driver)) -
        dotProduct sourceTemporalEMForce (sourceSpatialStaticPoleCoefficient n unit kappa driver)‖ ≤
      (∑ i, ‖sourceTemporalEMForce i‖) * ‖nativeEffectiveFrame (sourceStaticSpatialPoint n unit kappa)‖ *
        (2*staticInverseBudget^2*effectiveErrorBudget*kappa.val) *
        ‖sourceSpatialStaticSourceReader n unit kappa driver‖ := by
    rw [native, scale, contraction]
    exact sourceStaticSpatialContraction_price n unit kappa driver sourceTemporalEMForce
  have factor (a b c d : ℂ) : a*(noetherPairScale^2*b-noetherPairScale^2*c)-noetherPairScale^2*d =
      noetherPairScale^2*(a*(b-c)-d) := by ring
  rw [factor, norm_mul]
  exact mul_le_mul_of_nonneg_left generated (norm_nonneg _)

end LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumIR

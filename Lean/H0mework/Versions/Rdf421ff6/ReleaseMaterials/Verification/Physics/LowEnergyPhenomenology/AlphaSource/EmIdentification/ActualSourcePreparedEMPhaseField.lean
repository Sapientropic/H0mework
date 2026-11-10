import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedReducedQuantumCofactor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCompleteOrbit
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceGaugeWeightedUnitReader

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMPhaseField
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy StageNineHolonomicField
open Stage10
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumNoetherChart
open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalGaugeMomentumCoupling
open PhysicalEMGaugeRealization ActualEMCompleteOrbit ActualEMCarrierOwn
open ActualSourcePreparedTemporalEMConstraint

/-- Both gauge fields restrict the already identified original Lie occurrence. -/
theorem source_em_phase_field (mu : Fin 4) : emGaugeField mu = sourcePhaseGaugeField mu := by
  have same : p286CoordinateEquiv emDirection = sourcePhaseGaugeLie := by
    rw [← phase_lie_original, LinearEquiv.apply_symm_apply]
  unfold emGaugeField sourcePhaseGaugeField
  rw [same]

theorem source_temporal_force_phase :
    sourceTemporalEMForce = fun i => (sourcePhaseGaugeField 0 i : ℂ) := by
  funext i
  change (emGaugeField 0 i : ℂ) = _
  rw [source_em_phase_field]

/-- The actual electromagnetic Noether reader retains the complete weighted
CAR reader; the phase momentum multiplies that entire object once. -/
theorem source_actual_em_noether_reader_momentum (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    noetherReader (emGaugeField 0) p F 0 =
      ActionNormalization.phaseMomentum • sourceGaugeUnitReader p F := by
  rw [source_em_phase_field, sourceGaugeNoetherReader_momentum]

theorem source_actual_em_noether_contact_zero (force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : noetherReaderContact (emGaugeField 0) force p F = 0 := by
  rw [source_em_phase_field, sourceGaugeNoetherReaderContact_zero]

end LowEnergy.GaussComposite.ActualSourcePreparedEMPhaseField

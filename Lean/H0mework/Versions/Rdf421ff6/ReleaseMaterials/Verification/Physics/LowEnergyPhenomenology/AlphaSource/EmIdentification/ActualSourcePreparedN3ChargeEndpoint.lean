import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3IRNumerator
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3PoleEMActionRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3ChargeEndpoint
open CanonicalGradedSpatialSource ActualDressedFullCoulomb ActualCompositeFieldCurrent
open PhysicalN3SourceEnergy ActualElectronPhysicalJointInverse ActualElectronWholeNoetherObserver ActualElectronWholeChargeSoft
open GaussCoreHilbert GaussHistoryHilbert SourceFamilyHilbert SourceFamilyOperator
open Filter
open scoped InnerProductSpace Topology Matrix BigOperators
attribute [local irreducible] physicalN3PoleState physicalN3PoleCorrection physicalN3PoleEMCalibrationState
  actualNoetherBackground physicalN3RawEMReader physicalN3EMCalibrationPrice physicalN3RawEMPrice

/-- This charge is the actual same-state zero-transfer amputation endpoint,
including its source Rmix correction. -/
def sourceN3AmputatedPoleCharge (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) : ℂ :=
  actualElectronSign leg + inner ℂ (physicalN3PoleState event.momentum leg poles)
    (physicalN3PoleCorrection event.momentum leg poles)

def sourceN3ChargeReadDefect (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) : ℂ :=
  inner ℂ (physicalN3PoleState event.momentum leg poles)
    (physicalN3PoleEMCalibrationState event event.momentum leg poles) -
  inner ℂ (actualNoetherBackground event)
    (GaussUnitaryHistory.reader (physicalN3RawEMReader event) (actualNoetherBackground event))

def sourceN3ChargeReadPrice (event : DressedEvent) : ℝ :=
  physicalN3EMCalibrationPrice event + physicalN3RawEMPrice event

theorem source_n3_amputated_pole_charge_return (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    Tendsto (fun m => physicalN3PoleAmputatedChargeHistoryRead event.momentum event.momentum
      leg leg poles poles m) atTop (𝓝 (sourceN3AmputatedPoleCharge event leg poles)) :=
  (physical_n3_pole_em_action_zero_transfer_return event.momentum leg poles).2.2.2

/-- The current and amputation endpoint share the actual pole state. The event
calibration and prepared-background terms are retained as a computed defect. -/
theorem source_n3_noether_charge_endpoint (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    physicalN3PoleNoetherCurrent event leg poles 0 =
      sourceN3AmputatedPoleCharge event leg poles + sourceN3ChargeReadDefect event leg poles := by
  rw [physical_n3_pole_noether_current_temporal, physical_n3_pole_raw_em_observer_charge]
  simp only [sourceN3AmputatedPoleCharge, sourceN3ChargeReadDefect, inner_add_right]
  ring

private theorem history_reader_bound {I E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : Ultrafilter I) (A : E →L[ℂ] E) :
    ‖lift u (SourceFamilyOperator.constant A)‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  exact SourceBoundaryGram.lift_bound_explicit u (SourceFamilyOperator.constant A) ‖A‖
    (norm_nonneg A) (fun _ y => A.le_opNorm y) x

theorem source_n3_charge_defect_price (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    ‖sourceN3ChargeReadDefect event leg poles‖ ≤ sourceN3ChargeReadPrice event := by
  have reader : ‖GaussUnitaryHistory.reader (physicalN3RawEMReader event)‖ ≤ physicalN3RawEMPrice event := by
    unfold GaussUnitaryHistory.reader
    exact (history_reader_bound GaussUnitaryHistory.sourceFilter (physicalN3RawEMReader event)).trans
      (physical_n3_raw_em_reader_price event)
  have calibration : ‖inner ℂ (physicalN3PoleState event.momentum leg poles)
      (physicalN3PoleEMCalibrationState event event.momentum leg poles)‖ ≤ physicalN3EMCalibrationPrice event := by
    apply (norm_inner_le_norm _ _).trans
    rw [physical_n3_pole_state_norm, one_mul]
    exact physical_n3_pole_em_calibration_bound event event.momentum leg poles
  have background : ‖inner ℂ (actualNoetherBackground event)
      (GaussUnitaryHistory.reader (physicalN3RawEMReader event) (actualNoetherBackground event))‖ ≤ physicalN3RawEMPrice event := by
    apply (norm_inner_le_norm _ _).trans
    rw [actual_noether_background_norm, one_mul]
    apply ((GaussUnitaryHistory.reader (physicalN3RawEMReader event)).le_opNorm _).trans
    rw [actual_noether_background_norm, mul_one]
    exact reader
  exact (norm_sub_le _ _).trans (add_le_add calibration background)

def sourceN3ChargePairPrice (detector source : DressedEvent) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : ℝ :=
  ‖sourceN3AmputatedPoleCharge detector dLeg dPoles‖ * sourceN3ChargeReadPrice source +
    sourceN3ChargeReadPrice detector * ‖sourceN3AmputatedPoleCharge source sLeg sPoles‖ +
    sourceN3ChargeReadPrice detector * sourceN3ChargeReadPrice source

/-- Both source-generated endpoint errors propagate into the actual temporal
charge pair; the mixed product is not discarded. -/
theorem source_n3_charge_pair_price (detector source : DressedEvent) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    ‖physicalN3PoleNoetherCurrent detector dLeg dPoles 0 * physicalN3PoleNoetherCurrent source sLeg sPoles 0 -
      sourceN3AmputatedPoleCharge detector dLeg dPoles * sourceN3AmputatedPoleCharge source sLeg sPoles‖ ≤
      sourceN3ChargePairPrice detector source dLeg sLeg dPoles sPoles := by
  let qD := sourceN3AmputatedPoleCharge detector dLeg dPoles
  let qS := sourceN3AmputatedPoleCharge source sLeg sPoles
  let eD := sourceN3ChargeReadDefect detector dLeg dPoles
  let eS := sourceN3ChargeReadDefect source sLeg sPoles
  have split : physicalN3PoleNoetherCurrent detector dLeg dPoles 0 * physicalN3PoleNoetherCurrent source sLeg sPoles 0 - qD*qS =
      qD*eS + eD*qS + eD*eS := by
    rw [source_n3_noether_charge_endpoint, source_n3_noether_charge_endpoint]
    change (qD+eD)*(qS+eS)-qD*qS = _
    ring
  rw [split]
  apply ((norm_add_le (qD*eS+eD*qS) (eD*eS)).trans
    (add_le_add (norm_add_le (qD*eS) (eD*qS)) le_rfl)).trans
  simp only [norm_mul]
  have pD := source_n3_charge_defect_price detector dLeg dPoles
  have pS := source_n3_charge_defect_price source sLeg sPoles
  exact add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left pS (norm_nonneg qD))
    (mul_le_mul_of_nonneg_right pD (norm_nonneg qS)))
    (mul_le_mul pD pS (norm_nonneg eS) ((norm_nonneg eD).trans pD))

end LowEnergy.GaussComposite.ActualSourcePreparedN3ChargeEndpoint

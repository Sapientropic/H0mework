import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Scratch.AlphaSource.ActualDressedCorrectedElectronReadOwn.ActualDressedElectronProbe
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCorrectedConstraints
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMResponseSplit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback
open PreparationVacuumCurrentSignalOperator ActualDressedFullCoulomb ActualDressedFrequencyHalf
open ActualDressedPhysicalRayNumerator ActualDressedCorrectedGreen ActualCompositeFieldCurrent
open ActualEMDressedConstraint ActualEMDressedSchur ActualEMResponseSplit ActualEMCurrentSplit
open GaussCoreHilbert ActualCompositeGaugeBand ActualCompositeOriginWard CanonicalGradedCharge
open PreparationPhysicalPhaseGaugeRealization
open scoped Matrix
attribute [local irreducible] preparedProbeCurrent ActualCompositeFieldCurrent.compositeCurrent correctedResponse correctedGreen
  correctedDet frequencyResponsePencil physicalRayNumerator physicalRayDenominator
attribute [local irreducible] preparedProbeEndpoint compositeUnitLeg compositeChargeCore
  compositeResolvent compositeChargeMixing compositeInverseNorm chargeReader chargeAction

theorem actual_probe_completed_charge_return (leg : CompositeLeg) :
    chargeReader sourcePhaseGaugeLie (embed (preparedProbeEndpoint leg)) =
      (if leg.dual then (-1 : ℂ) else 1) • embed (preparedProbeEndpoint leg)+
        compositeInverseNorm leg • embed (compositeResolvent leg (compositeChargeMixing leg)) := by
  rw [prepared_probe_endpoint_original]
  have unitReturn := congrArg embed (composite_unit_charge_return leg)
  simp only [map_add, map_smul] at unitReturn
  have original := congrArg (fun A : Module.End ℂ GaussCoreDifferential.QuantumTest =>
    embed (A (compositeUnitLeg leg))) composite_charge_original
  exact (chargeReader_core sourcePhaseGaugeLie (compositeUnitLeg leg)).trans
    (original.symm.trans unitReturn)

def correctedProbeResponse (background : DressedEvent) (ir s sigma : ℝ) (n : PhysicalMomentum)
    (ps : PhysicalMomentum) (sL sR : CompositeLeg) : Fin 289 → ℂ :=
  correctedResponse background ir s sigma n (preparedProbeCurrent ps sL sR)

def correctedProbeRead (background : DressedEvent) (ir s sigma : ℝ) (n : PhysicalMomentum)
    (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (preparedProbeCurrent pd dL dR)
    (correctedProbeResponse background ir s sigma n ps sL sR)

theorem corrected_probe_response_original (background : DressedEvent) (ir s sigma : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg) :
    correctedProbeResponse background ir s sigma n ps sL sR =
      correctedResponse background ir s sigma n (ActualCompositeFieldCurrent.compositeCurrent ps sL sR) := by
  unfold correctedProbeResponse
  exact congrArg (correctedResponse background ir s sigma n) (prepared_probe_current_original ps sL sR)

theorem corrected_probe_read_original (background : DressedEvent) (ir s sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    correctedProbeRead background ir s sigma n pd ps dL dR sL sR =
      dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
        (correctedResponse background ir s sigma n (ActualCompositeFieldCurrent.compositeCurrent ps sL sR)) := by
  unfold correctedProbeRead
  exact congrArg₂ dotProduct (prepared_probe_current_original pd dL dR)
    (corrected_probe_response_original background ir s sigma n ps sL sR)

theorem actual_corrected_probe_raw_read (background : DressedEvent) (ir s sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    correctedProbeRead background ir s sigma n pd ps dL dR sL sR =
      emCurrentObservation (correctedGreen background ir s sigma n)
        (ActualCompositeFieldCurrent.compositeCurrent pd dL dR) (ActualCompositeFieldCurrent.compositeCurrent ps sL sR) := by
  rw [corrected_probe_read_original]
  unfold correctedResponse emCurrentObservation
  rfl

/-- Original charged unit inputs generate both raw full289 probe currents before the corrected read. -/
theorem actual_corrected_electron_read (background : DressedEvent) (ir s sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    PreparedProbe dL ∧ PreparedProbe dR ∧ PreparedProbe sL ∧ PreparedProbe sR ∧
      dotProduct (ActualCompositeFieldCurrent.compositeCurrent pd dL dR)
        (correctedResponse background ir s sigma n (ActualCompositeFieldCurrent.compositeCurrent ps sL sR)) =
      emCurrentObservation (correctedGreen background ir s sigma n)
        (ActualCompositeFieldCurrent.compositeCurrent pd dL dR) (ActualCompositeFieldCurrent.compositeCurrent ps sL sR) := by
  have detector := actual_probe_current_generated pd dL dR
  have source := actual_probe_current_generated ps sL sR
  exact ⟨detector.1, detector.2.1, source.1, source.2.1,
    (corrected_probe_read_original background ir s sigma n pd ps dL dR sL sR).symm.trans
      (actual_corrected_probe_raw_read background ir s sigma n pd ps dL dR sL sR)⟩

theorem actual_corrected_probe_equation (background : DressedEvent) (ir s sigma : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg)
    (positive : 0 < sigma) (regular : correctedDet background ir s sigma n ≠ 0) :
    frequencyResponsePencil background ((ir^2 : ℝ) • n) (frequencyRay ir s n)
      (dampedFourierClock (sourceFrequency ir s) sigma) *ᵥ
        correctedProbeResponse background ir s sigma n ps sL sR = ActualCompositeFieldCurrent.compositeCurrent ps sL sR := by
  rw [corrected_probe_response_original]
  exact actual_corrected_response_equation background ir s sigma n positive regular _

theorem actual_corrected_probe_unique (background : DressedEvent) (ir s sigma : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg)
    (positive : 0 < sigma) (regular : correctedDet background ir s sigma n ≠ 0)
    (a : Fin 289 → ℂ) :
    frequencyResponsePencil background ((ir^2 : ℝ) • n) (frequencyRay ir s n)
      (dampedFourierClock (sourceFrequency ir s) sigma) *ᵥ a = ActualCompositeFieldCurrent.compositeCurrent ps sL sR ↔
        a = correctedProbeResponse background ir s sigma n ps sL sR := by
  rw [corrected_probe_response_original]
  exact actual_corrected_full_solution background ir s sigma n positive regular _ a

theorem actual_corrected_probe_nine (background : DressedEvent) (ir s sigma : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg)
    (positive : 0 < sigma) (regular : correctedDet background ir s sigma n ≠ 0) :
    (sigma : ℂ) • sourceCokernel (frequencyRay ir s n)
      (physicalRayNumerator background ir s sigma n *ᵥ
        correctedProbeResponse background ir s sigma n ps sL sR) =
      -(physicalRayDenominator background ir s sigma n •
        sourceCokernel (frequencyRay ir s n) (ActualCompositeFieldCurrent.compositeCurrent ps sL sR)) := by
  rw [corrected_probe_response_original]
  exact actual_corrected_response_nine background ir s sigma n positive regular _

theorem actual_corrected_probe_four_parts (background : DressedEvent) (ir s sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    let G := correctedGreen background ir s sigma n
    let fd := ActualCompositeFieldCurrent.compositeCurrent pd dL dR
    let fs := ActualCompositeFieldCurrent.compositeCurrent ps sL sR
    correctedProbeRead background ir s sigma n pd ps dL dR sL sR =
      emPureObservation G fd fs+
        emCurrentObservation G (emCurrentForce fd) (emCurrentResidual fs)+
        emCurrentObservation G (emCurrentResidual fd) (emCurrentForce fs)+
        emCurrentObservation G (emCurrentResidual fd) (emCurrentResidual fs) := by
  dsimp only
  exact (actual_corrected_probe_raw_read background ir s sigma n pd ps dL dR sL sR).trans
    (em_response_four_parts (correctedGreen background ir s sigma n)
      (ActualCompositeFieldCurrent.compositeCurrent pd dL dR) (ActualCompositeFieldCurrent.compositeCurrent ps sL sR))

end LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead

#print axioms LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead.actual_corrected_electron_read
#print axioms LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead.actual_corrected_probe_nine
#print axioms LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead.actual_corrected_probe_four_parts
#print axioms LowEnergy.GaussComposite.ActualDressedCorrectedElectronRead.actual_probe_completed_charge_return

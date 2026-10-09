import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseSeedCharge
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseConstraintAction
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonPreparationConsumer

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit
elab "checked_phase_embedding_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_embedding_generated).type
theorem checked_phase_embedding_generated : checked_phase_embedding_generatedContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_embedding_generated

elab "checked_phase_packet_chargeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_packet_charge).type
theorem checked_phase_packet_charge : checked_phase_packet_chargeContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_packet_charge

elab "checked_actual_seed_coordinatesContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_coordinates).type
theorem checked_actual_seed_coordinates : checked_actual_seed_coordinatesContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_coordinates

elab "checked_actual_seed_phase_chargeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_charge).type
theorem checked_actual_seed_phase_charge : checked_actual_seed_phase_chargeContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_charge

elab "checked_actual_seed_phase_projectionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_projection).type
theorem checked_actual_seed_phase_projection : checked_actual_seed_phase_projectionContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_projection

elab "checked_phase_seed_test_chargeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_charge).type
theorem checked_phase_seed_test_charge : checked_phase_seed_test_chargeContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_charge

elab "checked_phase_seed_test_projectionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_projection).type
theorem checked_phase_seed_test_projection : checked_phase_seed_test_projectionContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_projection

elab "checked_prepared_phase_projectionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.prepared_phase_projection).type
theorem checked_prepared_phase_projection : checked_prepared_phase_projectionContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.prepared_phase_projection

elab "checked_phase_input_core_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_core_original).type
theorem checked_phase_input_core_original : checked_phase_input_core_originalContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_core_original

elab "checked_phase_input_completed_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_completed_original).type
theorem checked_phase_input_completed_original : checked_phase_input_completed_originalContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_completed_original

elab "checked_actual_creation_phase_inputContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_creation_phase_input).type
theorem checked_actual_creation_phase_input : checked_actual_creation_phase_inputContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_creation_phase_input

elab "checked_actual_background_phase_projectionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_background_phase_projection).type
theorem checked_actual_background_phase_projection : checked_actual_background_phase_projectionContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_background_phase_projection

elab "checked_phase_constraint_projected_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_action).type
theorem checked_phase_constraint_projected_action : checked_phase_constraint_projected_actionContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_action

elab "checked_phase_constraint_projected_chargeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_charge).type
theorem checked_phase_constraint_projected_charge : checked_phase_constraint_projected_chargeContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_charge

elab "checked_phase_constraint_hamiltonian_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_hamiltonian_return).type
theorem checked_phase_constraint_hamiltonian_return : checked_phase_constraint_hamiltonian_returnContract := @LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_hamiltonian_return

elab "checked_same_event_charge_quantum_poleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_charge_quantum_pole).type
theorem checked_same_event_charge_quantum_pole : checked_same_event_charge_quantum_poleContract := @LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_charge_quantum_pole

elab "checked_same_event_full_constraintContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_full_constraint).type
theorem checked_same_event_full_constraint : checked_same_event_full_constraintContract := @LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_full_constraint

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert CanonicalCompletedSector GaussCoreDifferential GaussDensityCore
open SourceQuantumScalarChart SourceQuantumFockGauge PreparationVacuumPhysicalFeedback
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedConstraintEndpoint
open PreparationVacuumSourcePreparedResponse SourceGraph CanonicalGradedCharge
open PreparationVacuumHalfDensityFiber PreparationVacuumWeightedChargeActionWard
open GaussFockPair GaussQuantumMultiplier PreparationPhysicalPhaseGaugeRealization
open scoped Matrix Topology

theorem actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp
  }⟩

theorem actual_original_seed_packet :
    quantized (chargeMatrix sourcePhaseGaugeLie) CanonicalCompletedSector.seed=phaseSeedPacket :=
  actual_seed_phase_charge

theorem actual_same_created_charge (event : DressedEvent) :
    chargeReader sourcePhaseGaugeLie (ActualDressedSourcePreparation.sourceDressedUnit event.epsilon event.precision)=
      (1/2:ℂ) • ActualDressedSourcePreparation.sourceDressedUnit event.epsilon event.precision+actualPhaseInput event :=
  actual_creation_phase_input event

theorem actual_full_phase_endpoint (event : DressedEvent) :
    PreparationVacuumNoetherOrdinaryWard.sourceHamiltonian event.momentum event.frame
        (phaseConstraintReader event.momentum event.frame
          (ActualDressedSourcePreparation.sourceDressedUnit event.epsilon event.precision))-
      phaseConstraintReader event.momentum event.frame
        (PreparationVacuumNoetherOrdinaryWard.sourceHamiltonian event.momentum event.frame
          (ActualDressedSourcePreparation.sourceDressedUnit event.epsilon event.precision))=
      phaseConstraintChannels event.momentum 0 event.frame
        (ActualDressedSourcePreparation.sourceDressedUnit event.epsilon event.precision) := by
  simpa only [add_zero] using phase_constraint_hamiltonian_return event.momentum 0 event.frame
    (ActualDressedSourcePreparation.sourceDressedUnit event.epsilon event.precision)

end LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit


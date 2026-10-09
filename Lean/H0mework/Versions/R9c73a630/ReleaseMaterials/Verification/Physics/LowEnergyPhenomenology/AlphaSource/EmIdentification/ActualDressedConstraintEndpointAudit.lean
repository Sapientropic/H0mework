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

open Lean Elab Command
private def packageCertChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def packageCertClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (packageCertChildren info).toList ++ pending
      seen := seen.insert name
  return seen


private def packageCertRequire (env : Environment) (root : Name) (required : Array Name) : CommandElabM Unit := do
  let mut pending := [root]
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !pending.isEmpty && !(required.all found.contains) do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      let children := packageCertChildren info
      for target in required do
        if name == target || children.contains target then found := found.insert target
      pending := children.toList ++ pending
      seen := seen.insert name
  for name in required do
    unless found.contains name do throwError m!"UNCONSUMED_DIRECT {root} {name}"

elab "#audit_dressed_constraint_common" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseSeedCharge,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhaseConstraintAction,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonPreparationConsumer]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseColorProjection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phasePrimalPacket,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_embedding_generated,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_packet_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseSeedPacket,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_coordinates,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseSeedSection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.prepared_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseInputCore,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_core_original,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseInputCompleted,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_completed_original,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actualPhaseInput,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_creation_phase_input,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_background_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseConstraintCore,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseConstraintReader,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_action,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseConstraintChannels,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_hamiltonian_return,
    ``LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_charge_quantum_pole,
    ``LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_full_constraint]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_embedding_generated,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_packet_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_actual_seed_coordinates,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_actual_seed_phase_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_actual_seed_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_seed_test_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_seed_test_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_prepared_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_input_core_original,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_input_completed_original,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_actual_creation_phase_input,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_actual_background_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_constraint_projected_action,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_constraint_projected_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_phase_constraint_hamiltonian_return,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_same_event_charge_quantum_pole,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.checked_same_event_full_constraint,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.actual_original_seed_packet,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.actual_same_created_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpointAudit.actual_full_phase_endpoint]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_embedding_generated,#[
    ``LowEnergy.GaussComposite.ActualEMCompleteOrbit.phase_lie_original]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_packet_charge,#[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_embedding_generated]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_charge,#[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_coordinates,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_packet_charge]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.prepared_phase_projection,#[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_projection]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_core_original,#[
    ``LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn.sourceJointInputCore,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_charge]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_creation_phase_input,#[
    ``LowEnergy.GaussComposite.ActualDressedJointWard.dressed_joint_unit_return,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_completed_original]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_action,#[
    ``LowEnergy.GaussComposite.ActualDressedPhaseConfiguration.phase_dev_gauss_return,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseConstraintReader]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_charge,#[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_action,
    ``LowEnergy.CanonicalGradedCharge.chargeReader_core]),
    (``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_hamiltonian_return,#[
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.leftAction_source,
    ``LowEnergy.PreparationVacuumWeightedChargeActionWard.rightAction_source,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phaseConstraintChannels]),
    (``LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_charge_quantum_pole,#[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_creation_phase_input,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.temporal_quantum_preparation_return,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.static_pole_preparation_return]),
    (``LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_full_constraint,#[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_hamiltonian_return])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_embedding_generated,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_packet_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_coordinates,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.prepared_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_core_original,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_completed_original,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_creation_phase_input,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_background_phase_projection,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_action,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_charge,
    ``LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_hamiltonian_return,
    ``LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_charge_quantum_pole,
    ``LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_full_constraint]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.CanonicalCompletedSector.seed,
    ``LowEnergy.CanonicalCompletedSector.seedCoordinates,
    ``LowEnergy.CanonicalGradedCharge.chargeMatrix,
    ``LowEnergy.CanonicalGradedCharge.chargeReader,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedTemporalForm.emActionForm,
    ``LowEnergy.PreparationVacuumNoetherOrdinaryWard.sourceHamiltonian,
    ``LowEnergy.GaussComposite.ActualDressedTemporalResidual.preparationWardObserver,
    ``LowEnergy.GaussComposite.ActualDressedTemporalHalf.temporalGaussHalfJet,
    ``LowEnergy.GaussComposite.ActualDressedStaticPole.staticPoleLeadingOperator]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let mut axioms : Nat := 0
  let mut opaques : Nat := 0
  for name in all.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
    if info.isUnsafe || info.isPartial then throwError m!"UNTRUSTED {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaques := opaques + 1
    if let .axiomInfo _ := info then
      axioms := axioms + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio,
      `SaturationMonoid.StandardModelConstraint.alphaStrongDisplayed] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_CONSTRAINT_COMMON_AUDIT_OUTPUT") then
    let project := all.toArray.filter fun name =>
      match owner name with
      | none => false
      | some m => !(#["Mathlib","Init","Lean","Std","Batteries","Aesop","Qq","Plausible","ImportGraph","ProofWidgets"].any (fun h => h.isPrefixOf m.toString))
    liftIO <| IO.FS.writeFile path <| (Json.mkObj [
      ("owned",toJson (owned.map Name.toString)),("public",toJson (mouths.map Name.toString)),
      ("tests",toJson (tests.map Name.toString)),("nodes",toJson all.size),("opaque_read",toJson opaques),
      ("axioms",toJson axioms),("anchors",toJson (anchors.map Name.toString)),
      ("direct",toJson (direct.map fun p => (p.1.toString,p.2.map Name.toString))),
      ("project",toJson (project.map fun n => (n.toString,(owner n).map Name.toString)))]).compress
  logInfo m!"DRESSED_CONSTRAINT_COMMON_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_constraint_common
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_embedding_generated
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_packet_charge
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_coordinates
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_charge
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_seed_phase_projection
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_charge
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_seed_test_projection
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.prepared_phase_projection
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_core_original
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_input_completed_original
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_creation_phase_input
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.actual_background_phase_projection
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_action
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_projected_charge
#print axioms LowEnergy.GaussComposite.ActualDressedConstraintEndpoint.phase_constraint_hamiltonian_return
#print axioms LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_charge_quantum_pole
#print axioms LowEnergy.GaussComposite.ActualDressedCommonPreparationConsumer.same_event_full_constraint

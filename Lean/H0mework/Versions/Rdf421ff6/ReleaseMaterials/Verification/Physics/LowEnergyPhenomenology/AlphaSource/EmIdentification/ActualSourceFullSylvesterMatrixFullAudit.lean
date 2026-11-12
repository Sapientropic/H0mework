import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFullSylvesterMatrix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFullNoetherMatrixRead

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit
elab "checked_source_green_inverseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_green_inverse).type
theorem checked_source_green_inverse : checked_source_green_inverseContract := @LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_green_inverse

elab "checked_source_matrix_inverseContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_matrix_inverse).type
theorem checked_source_matrix_inverse : checked_source_matrix_inverseContract := @LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_matrix_inverse

elab "checked_source_inverse_weightsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_weights).type
theorem checked_source_inverse_weights : checked_source_inverse_weightsContract := @LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_weights

elab "checked_source_whole_action_mkContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_mk).type
theorem checked_source_whole_action_mk : checked_source_whole_action_mkContract := @LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_mk

elab "checked_source_whole_action_basisContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_basis).type
theorem checked_source_whole_action_basis : checked_source_whole_action_basisContract := @LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_basis

elab "checked_source_inverse_matrix_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_matrix_return).type
theorem checked_source_inverse_matrix_return : checked_source_inverse_matrix_returnContract := @LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_matrix_return

elab "checked_source_noether_half_matrix_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_noether_half_matrix_return).type
theorem checked_source_noether_half_matrix_return : checked_source_noether_half_matrix_returnContract := @LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_noether_half_matrix_return

elab "checked_source_full_noether_polarization_matrixContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_full_noether_polarization_matrix).type
theorem checked_source_full_noether_polarization_matrix : checked_source_full_noether_polarization_matrixContract := @LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_full_noether_polarization_matrix

end LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit

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

elab "#audit_actual_source_full_sylvester_matrix" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFullSylvesterMatrix,`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFullNoetherMatrixRead]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.ActualOperator,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.ActualTransfer,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.SourceCarrier,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourcePowerBasis,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.SourceIndex,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourcePencil,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceGreen,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_green_inverse,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourcePencilMatrix,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceGreenMatrix,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_matrix_inverse,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceInverseWeights,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_weights,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceWholeAction,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_mk,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_basis,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_matrix_return,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_noether_half_matrix_return,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceDirectMoments,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceDrivenMoments,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceFullNoetherMatrixEntry,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_full_noether_polarization_matrix]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit.checked_source_green_inverse,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit.checked_source_matrix_inverse,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit.checked_source_inverse_weights,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit.checked_source_whole_action_mk,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit.checked_source_whole_action_basis,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit.checked_source_inverse_matrix_return,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit.checked_source_noether_half_matrix_return,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrixFullAudit.checked_source_full_noether_polarization_matrix]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.SourceCarrier,#[
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationPolynomial]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourcePowerBasis,#[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.SourceCarrier,
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationPolynomial_monic]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_green_inverse,#[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceGreen,
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationPolynomial_offAxis]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_matrix_inverse,#[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_green_inverse]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_weights,#[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_matrix_inverse]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_mk,#[
    ``LowEnergy.SourcePropagationAlgebraicResponse.sourceEvolution_annihilated]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_basis,#[
    ``LowEnergy.SourcePropagationAlgebraicResponse.sourceEvolution_annihilated]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_matrix_return,#[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_weights,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_basis,
    ``LowEnergy.SourcePropagationAlgebraicResponse.polynomialResolvent_future]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_noether_half_matrix_return,#[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_matrix_return,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noether_static_half_inverse,
    ``LowEnergy.PreparationVacuumPropagationPencil.driveOperator_apply]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceDirectMoments,#[
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noetherStaticInitial]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceDrivenMoments,#[
    ``LowEnergy.PreparationVacuumPropagationPencil.driveOperator,
    ``LowEnergy.PreparationVacuumPropagationPencil.rawInitial]),
    (``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_full_noether_polarization_matrix,#[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_noether_half_matrix_return,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.dressedStaticPolarization,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.sourceFullNoetherMatrixEntry])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_green_inverse,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_matrix_inverse,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_weights,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_mk,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_basis,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_matrix_return,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_noether_half_matrix_return,
    ``LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_full_noether_polarization_matrix]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedKinematicPoint,
    ``LowEnergy.SourcePropagationResolvent.sourceInverse,
    ``LowEnergy.SourcePropagationResolvent.twoTimeMap,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointGenerator,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.PreparationVacuumNoetherChart.noetherReaderContact,
    ``LowEnergy.PreparationVacuumRawJointFeedback.rawReaderContact,
    ``LowEnergy.GaussComposite.ActualDressedSylvester.noetherStaticContact,
    ``LowEnergy.PreparationVacuumPropagationPencil.rawInitial,
    ``LowEnergy.PreparationVacuumPropagationPencil.slopeInitial,
    ``LowEnergy.PreparationVacuumPropagationPencil.leftCurrent,
    ``LowEnergy.PreparationVacuumPropagationPencil.rightCurrent,
    ``LowEnergy.PreparationVacuumPropagationPencil.driveOperator,
    ``LowEnergy.PreparationVacuumPropagationPencil.evolutionGenerator,
    ``LowEnergy.SourcePropagationAlgebraicResponse.sourceEvolution_annihilated,
    ``LowEnergy.SourcePropagationAlgebraicResponse.sourceEvolution_integral,
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationPolynomial,
    ``LowEnergy.SourcePropagationAlgebraicResponse.propagationPolynomial_offAxis,
    ``LowEnergy.SourcePropagationAlgebraicResponse.actualJoint_annihilated,
    ``LowEnergy.SourcePropagationAlgebraicResponse.jointPolynomial,
    ``LowEnergy.SourcePropagationAlgebraicResponse.compressionPolynomial]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_ACTUAL_SOURCE_FULL_SYLVESTER_MATRIX_AUDIT_OUTPUT") then
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
  logInfo m!"ACTUAL_SOURCE_FULL_SYLVESTER_MATRIX_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_actual_source_full_sylvester_matrix
#print axioms LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_green_inverse
#print axioms LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_matrix_inverse
#print axioms LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_weights
#print axioms LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_mk
#print axioms LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_whole_action_basis
#print axioms LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_inverse_matrix_return
#print axioms LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_noether_half_matrix_return
#print axioms LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix.source_full_noether_polarization_matrix

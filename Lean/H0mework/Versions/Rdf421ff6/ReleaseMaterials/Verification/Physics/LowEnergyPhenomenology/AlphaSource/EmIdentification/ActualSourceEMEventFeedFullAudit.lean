import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceEMEventFeed

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceEMEventFeedFullAudit
elab "checked_actual_preparation_weightContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_preparation_weight).type
theorem checked_actual_preparation_weight : checked_actual_preparation_weightContract := @LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_preparation_weight

elab "checked_actual_dressed_photon_connected_feedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_dressed_photon_connected_feed).type
theorem checked_actual_dressed_photon_connected_feed : checked_actual_dressed_photon_connected_feedContract := @LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_dressed_photon_connected_feed

end LowEnergy.GaussComposite.ActualSourceEMEventFeedFullAudit

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

elab "#audit_event_feed" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceEMEventFeed]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actualPreparationLeg,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actualPreparationScale,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_preparation_weight,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_dressed_photon_connected_feed]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeedFullAudit.checked_actual_preparation_weight,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeedFullAudit.checked_actual_dressed_photon_connected_feed]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_preparation_weight,#[
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_original,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm]),
    (``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_dressed_photon_connected_feed,#[
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_preparation_weight,
    ``LowEnergy.PreparationVacuumFullFieldRiesz.currentVertex_original_pair,
    ``LowEnergy.PreparationPhysicalDressedPhotonCouplingReturn.sourcePhotonWholeConfiguration_generated,
    ``LowEnergy.PreparationPhysicalSourcePreparedPhotonReturn.sourcePreparedPhotonAmplitude])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_preparation_weight,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_dressed_photon_connected_feed]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_EVENT_FEED_AUDIT_OUTPUT") then
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
  logInfo m!"EVENT_FEED_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_event_feed
#print axioms LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_preparation_weight
#print axioms LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_dressed_photon_connected_feed

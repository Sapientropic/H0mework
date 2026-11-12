import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceEventCutElimination

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceEventCutFullAudit
elab "checked_actual_cut_free_kinematicsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_kinematics).type
theorem checked_actual_cut_free_kinematics : checked_actual_cut_free_kinematicsContract := @LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_kinematics

elab "checked_actual_cut_free_observerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_observer).type
theorem checked_actual_cut_free_observer : checked_actual_cut_free_observerContract := @LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_observer

elab "checked_actual_cut_free_staticContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_static).type
theorem checked_actual_cut_free_static : checked_actual_cut_free_staticContract := @LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_static

elab "checked_actual_cut_free_physical_n3_windowContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_physical_n3_window).type
theorem checked_actual_cut_free_physical_n3_window : checked_actual_cut_free_physical_n3_windowContract := @LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_physical_n3_window

elab "checked_actual_cut_free_sixth_ir_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_sixth_ir_return).type
theorem checked_actual_cut_free_sixth_ir_return : checked_actual_cut_free_sixth_ir_returnContract := @LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_sixth_ir_return

end LowEnergy.GaussComposite.ActualSourceEventCutFullAudit

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

elab "#audit_event_cut" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceEventCutElimination]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_kinematics,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_observer,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_static,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_physical_n3_window,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_sixth_ir_return]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualSourceEventCutFullAudit.checked_actual_cut_free_kinematics,
    ``LowEnergy.GaussComposite.ActualSourceEventCutFullAudit.checked_actual_cut_free_observer,
    ``LowEnergy.GaussComposite.ActualSourceEventCutFullAudit.checked_actual_cut_free_static,
    ``LowEnergy.GaussComposite.ActualSourceEventCutFullAudit.checked_actual_cut_free_physical_n3_window,
    ``LowEnergy.GaussComposite.ActualSourceEventCutFullAudit.checked_actual_cut_free_sixth_ir_return]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_static,#[
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_kinematics,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_observer]),
    (``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_physical_n3_window,#[
    ``LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver.actual_physical_euler_observer_value,
    ``LowEnergy.GaussComposite.ActualElectronWholeNoetherObserver.actualFullNoetherVariation]),
    (``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_sixth_ir_return,#[
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_static,
    ``LowEnergy.GaussComposite.ActualDressedIRReturn.actual_sixth_ir_return])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_kinematics,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_observer,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_static,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_physical_n3_window,
    ``LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_sixth_ir_return]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_EVENT_CUT_AUDIT_OUTPUT") then
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
  logInfo m!"EVENT_CUT_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_event_cut
#print axioms LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_kinematics
#print axioms LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_observer
#print axioms LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_static
#print axioms LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_physical_n3_window
#print axioms LowEnergy.GaussComposite.ActualSourceEMEventFeed.actual_cut_free_sixth_ir_return

import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeCoulombDressing

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit
elab "checked_composite_bottom_overlap_boundsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_overlap_bounds).type
theorem checked_composite_bottom_overlap_bounds : checked_composite_bottom_overlap_boundsContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_overlap_bounds

elab "checked_composite_bottom_born_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_read).type
theorem checked_composite_bottom_born_read : checked_composite_bottom_born_readContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_read

elab "checked_composite_bottom_born_boundsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_bounds).type
theorem checked_composite_bottom_born_bounds : checked_composite_bottom_born_boundsContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_bounds

elab "checked_composite_sharp_bottom_overlapContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_sharp_bottom_overlap).type
theorem checked_composite_sharp_bottom_overlap : checked_composite_sharp_bottom_overlapContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_sharp_bottom_overlap

elab "checked_composite_weight_born_dressingContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing).type
theorem checked_composite_weight_born_dressing : checked_composite_weight_born_dressingContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing

elab "checked_composite_coulomb_overlap_boundsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_overlap_bounds).type
theorem checked_composite_coulomb_overlap_bounds : checked_composite_coulomb_overlap_boundsContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_overlap_bounds

elab "checked_composite_coulomb_coefficient_dressingContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing).type
theorem checked_composite_coulomb_coefficient_dressing : checked_composite_coulomb_coefficient_dressingContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing

elab "checked_composite_coulomb_dressing_errorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_dressing_error).type
theorem checked_composite_coulomb_dressing_error : checked_composite_coulomb_dressing_errorContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_dressing_error

elab "checked_composite_coulomb_spatial_dressingContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_spatial_dressing).type
theorem checked_composite_coulomb_spatial_dressing : checked_composite_coulomb_spatial_dressingContract := @LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_spatial_dressing

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open LowEnergy.GaussComposite.ActualCompositeFieldCurrent
open LowEnergy.GaussComposite.ActualCompositeCoulombDressing

theorem checked_all_sharp_dressing (dL dR sL sR : CompositeLeg)
    (hdL : dL.sharp=true) (hdR : dR.sharp=true) (hsL : sL.sharp=true) (hsR : sR.sharp=true) :
    compositeCoulombOverlap dL dR sL sR=1 := by
  simp only [compositeCoulombOverlap,(composite_sharp_bottom_overlap dL hdL).1,
    (composite_sharp_bottom_overlap dR hdR).1,(composite_sharp_bottom_overlap sL hsL).1,
    (composite_sharp_bottom_overlap sR hsR).1,one_mul]

theorem checked_born_nonzero (leg : CompositeLeg) : compositeBottomBornWeight leg≠0 :=
  (composite_bottom_born_bounds leg).1.ne'

theorem checked_complete_overlap_nonzero (dL dR sL sR : CompositeLeg) :
    compositeCoulombOverlap dL dR sL sR≠0 :=
  (composite_coulomb_overlap_bounds dL dR sL sR).1.ne'
end LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit

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

elab "#audit_coulomb_dressing" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualCompositeCoulombDressing]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.compositeBottomOverlap,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.compositeBottomBornWeight,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_overlap_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_read,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_sharp_bottom_overlap,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.compositeBaseUnitWeight,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.compositeCoulombOverlap,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_overlap_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_dressing_error,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_spatial_dressing]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_bottom_overlap_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_bottom_born_read,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_bottom_born_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_sharp_bottom_overlap,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_weight_born_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_coulomb_overlap_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_coulomb_coefficient_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_coulomb_dressing_error,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_composite_coulomb_spatial_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_all_sharp_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_born_nonzero,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressingAudit.checked_complete_overlap_nonzero]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_read,#[
    ``LowEnergy.GaussComposite.ActualCompositeGaugeBand.composite_response_bottom,
    ``LowEnergy.GaussComposite.ActualCompositeFieldCurrent.compositeUnitLeg]),
    (``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_overlap_bounds,#[
    ``LowEnergy.GaussComposite.ActualCompositeFieldCurrent.composite_response_nonzero,
    ``LowEnergy.GaussComposite.ActualCompositeGaugeBand.composite_response_bottom]),
    (``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing,#[
    ``LowEnergy.GaussComposite.ActualCompositeGaugeBand.composite_weight_sharp_left,
    ``LowEnergy.GaussComposite.ActualCompositeGaugeBand.composite_weight_sharp_right]),
    (``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing,#[
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing]),
    (``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_dressing_error,#[
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_overlap_bounds]),
    (``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_spatial_dressing,#[
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombPacket.composite_coulomb_spatial_limit])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_overlap_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_read,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_sharp_bottom_overlap,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_overlap_bounds,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_dressing_error,
    ``LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_spatial_dressing]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualCompositeFieldCurrent.compositeResponse,
    ``LowEnergy.GaussComposite.ActualCompositeFieldCurrent.compositeUnitLeg,
    ``LowEnergy.GaussComposite.ActualCompositeGaugeBand.composite_response_bottom,
    ``LowEnergy.GaussComposite.ActualCompositeGaugeBand.compositeBase,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_COULOMB_DRESSING_AUDIT_OUTPUT") then
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
  logInfo m!"COULOMB_DRESSING_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_coulomb_dressing
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_overlap_bounds
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_read
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_bottom_born_bounds
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_sharp_bottom_overlap
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_weight_born_dressing
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_overlap_bounds
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_coefficient_dressing
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_dressing_error
#print axioms LowEnergy.GaussComposite.ActualCompositeCoulombDressing.composite_coulomb_spatial_dressing

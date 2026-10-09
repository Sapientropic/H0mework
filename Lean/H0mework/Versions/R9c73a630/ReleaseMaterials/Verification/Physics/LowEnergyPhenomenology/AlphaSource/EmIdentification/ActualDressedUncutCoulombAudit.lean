import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutCoulomb

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit
elab "checked_dressed_uncut_current_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_generated).type
theorem checked_dressed_uncut_current_generated : checked_dressed_uncut_current_generatedContract := @LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_generated

elab "checked_dressed_uncut_current_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_original).type
theorem checked_dressed_uncut_current_original : checked_dressed_uncut_current_originalContract := @LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_original

elab "checked_dressed_uncut_temporal_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_temporal_return).type
theorem checked_dressed_uncut_temporal_return : checked_dressed_uncut_temporal_returnContract := @LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_temporal_return

elab "checked_dressed_uncut_matrix_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_read).type
theorem checked_dressed_uncut_matrix_read : checked_dressed_uncut_matrix_readContract := @LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_read

elab "checked_dressed_uncut_matrix_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_generated).type
theorem checked_dressed_uncut_matrix_generated : checked_dressed_uncut_matrix_generatedContract := @LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_generated

elab "checked_dressed_uncut_static_full_originContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_full_origin).type
theorem checked_dressed_uncut_static_full_origin : checked_dressed_uncut_static_full_originContract := @LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_full_origin

elab "checked_dressed_uncut_green_contactContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_green_contact).type
theorem checked_dressed_uncut_green_contact : checked_dressed_uncut_green_contactContract := @LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_green_contact

elab "checked_dressed_uncut_static_potentialContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_potential).type
theorem checked_dressed_uncut_static_potential : checked_dressed_uncut_static_potentialContract := @LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_potential

elab "checked_dressed_uncut_coulomb_packet_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_coulomb_packet_original).type
theorem checked_dressed_uncut_coulomb_packet_original : checked_dressed_uncut_coulomb_packet_originalContract := @LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_coulomb_packet_original

elab "checked_dressed_cut_then_coulomb_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_cut_then_coulomb_spatial_limit).type
theorem checked_dressed_cut_then_coulomb_spatial_limit : checked_dressed_cut_then_coulomb_spatial_limitContract := @LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_cut_then_coulomb_spatial_limit

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullFieldRiesz PreparationVacuumFullOriginResponse
open ActualWholeStatic ActualEMCarrierOwn MeasureTheory Filter Set
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldCovector
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open ActualDressedSourcePreparation ActualDressedSourceResponse ActualDressedJointWard ActualDressedActionPhase
open PhysicalEMTransferCurrent PhysicalEMTransferResolver CanonicalPhysicalYResolvent
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap InnerProductSpace
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩

attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceDressedAddition sourceProfile finiteFull sourceDressedResponse currentVertex

open ActualDressedFullCoulomb ActualDressedUncutCurrent

open PreparationVacuumTemporalCharge PreparationVacuumJointFieldResponse
open ActualDressedCofinal ActualDressedReaderComponents ActualDressedTemporalCurrent ActualDressedNoether

open ActualDressedUncutCoulomb GaussComposite.SourceGraph

theorem checked_actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp }⟩

theorem checked_actual_unit_nonzero (event : DressedEvent) : sourceDressedUnit event.epsilon event.precision≠0 := by
  intro h
  have paid:=source_dressed_unit_norm event.epsilon event.precision
  rw [h,norm_zero] at paid
  exact zero_ne_one paid

theorem checked_generic_matrix_not_selfadjoint : ¬IsSelfAdjoint (!![(0:ℂ),1;0,0] : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have entry:=congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ=>A 0 1) h
  norm_num [Matrix.star_apply] at entry

end LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit

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

elab "#audit_dressed_uncut_coulomb" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutCurrent,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutCoulomb]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressedUncutCurrent,
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_generated,
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_original,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_temporal_return,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressedUncutMatrixRead,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_read,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_generated,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressedUncutOriginCurrent,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_full_origin,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_green_contact,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_potential,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressedUncutCoulombPacket,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_coulomb_packet_original,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_cut_then_coulomb_spatial_limit]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_current_generated,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_current_original,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_temporal_return,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_matrix_read,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_matrix_generated,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_static_full_origin,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_green_contact,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_static_potential,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_uncut_coulomb_packet_original,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_dressed_cut_then_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulombAudit.checked_generic_matrix_not_selfadjoint]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedCofinal.dressed_two_response_limits,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original]),
    (``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_original,#[
    ``LowEnergy.PreparationVacuumFullFieldRiesz.currentRestriction_original_pair,
    ``LowEnergy.PreparationVacuumFieldCovector.sourceCovector,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressed_euler_observer_original]),
    (``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_temporal_return,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_generated,
    ``LowEnergy.GaussComposite.ActualDressedCofinal.dressed_temporal_common_cut_limit]),
    (``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_generated,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_generated,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read]),
    (``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_full_origin,#[
    ``LowEnergy.GaussComposite.ActualWholeStatic.wholeStaticLimit,
    ``LowEnergy.PreparationVacuumStaticPoleResponse.staticInverse]),
    (``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_green_contact,#[
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.contactInverse]),
    (``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_potential,#[
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_static_green_scaled]),
    (``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_coulomb_packet_original,#[
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_coulomb_ir_packet_integrable,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressedUncutCoulombPacket]),
    (``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_cut_then_coulomb_spatial_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_generated,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_full_origin,
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_coulomb_ir_packet_limit,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_generated,
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_original,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_temporal_return,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_read,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_generated,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_full_origin,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_green_contact,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_potential,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_coulomb_packet_original,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_cut_then_coulomb_spatial_limit]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedNoetherKernel,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.PreparationVacuumFieldCovector.sourceCovector,
    ``LowEnergy.PreparationVacuumFullOriginResponse.fullNativeOrigin,
    ``LowEnergy.PreparationVacuumStaticPoleResponse.staticInverse,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.GaussComposite.ActualWholeStatic.wholeCoulombIRPacket]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_UNCUT_COULOMB_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_UNCUT_COULOMB_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_uncut_coulomb
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_generated
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressed_uncut_current_original
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_temporal_return
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_read
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_generated
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_full_origin
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_green_contact
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_potential
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_coulomb_packet_original
#print axioms LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_cut_then_coulomb_spatial_limit

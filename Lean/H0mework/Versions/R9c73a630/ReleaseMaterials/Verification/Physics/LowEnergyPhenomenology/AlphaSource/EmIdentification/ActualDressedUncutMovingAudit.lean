import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutMomentum
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutMovingCoulomb

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUncutMovingAudit
elab "checked_dressed_uncut_current_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous).type
theorem checked_dressed_uncut_current_continuous : checked_dressed_uncut_current_continuousContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous

elab "checked_dressed_uncut_matrix_joint_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous).type
theorem checked_dressed_uncut_matrix_joint_continuous : checked_dressed_uncut_matrix_joint_continuousContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous

elab "checked_dressed_uncut_moving_potentialContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_moving_potential).type
theorem checked_dressed_uncut_moving_potential : checked_dressed_uncut_moving_potentialContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_moving_potential

elab "checked_dressed_moving_static_uniformContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform).type
theorem checked_dressed_moving_static_uniform : checked_dressed_moving_static_uniformContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform

elab "checked_dressed_moving_static_dominationContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination).type
theorem checked_dressed_moving_static_domination : checked_dressed_moving_static_dominationContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination

elab "checked_moving_coulomb_radius_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_radius_positive).type
theorem checked_moving_coulomb_radius_positive : checked_moving_coulomb_radius_positiveContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_radius_positive

elab "checked_moving_cut_symbol_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_cut_symbol_return).type
theorem checked_moving_cut_symbol_return : checked_moving_cut_symbol_returnContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_cut_symbol_return

elab "checked_moving_coulomb_symbol_boundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound).type
theorem checked_moving_coulomb_symbol_bound : checked_moving_coulomb_symbol_boundContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound

elab "checked_moving_coulomb_packet_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_integrable).type
theorem checked_moving_coulomb_packet_integrable : checked_moving_coulomb_packet_integrableContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_integrable

elab "checked_moving_coulomb_packet_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit).type
theorem checked_moving_coulomb_packet_limit : checked_moving_coulomb_packet_limitContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit

elab "checked_moving_coulomb_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit).type
theorem checked_moving_coulomb_spatial_limit : checked_moving_coulomb_spatial_limitContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit

elab "checked_moving_coulomb_origin_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_origin_spatial_limit).type
theorem checked_moving_coulomb_origin_spatial_limit : checked_moving_coulomb_origin_spatial_limitContract := @LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_origin_spatial_limit

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalPoleSheet PreparationVacuumStaticPoleResponse
open PreparationPhysicalStaticSpatialCouplingReturn ActualWholeStatic ActualEMCarrierOwn
open PreparationVacuumOriginalGreenFeedback MeasureTheory Filter Set
open ActualDressedFullCoulomb ActualDressedUncutCurrent ActualDressedUncutCoulomb
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap
local instance : MeasurableSpace WholeMatrix := borel _
local instance : BorelSpace WholeMatrix := ⟨rfl⟩
open ActualDressedUncutMoving
attribute [local irreducible] wholeCoulombIRSymbol wholeStaticLimit dressedUncutCurrent

theorem checked_true_fourier_endpoints (detector source : DressedEvent) (scale : ℝ) (k : PhysicalMomentum) :
    dressedUncutMatrixRead detector source (scale • k) (wholeCoulombIRSymbol scale k)=
      dotProduct (dressedUncutCurrent detector (-(scale • k)))
        (wholeCoulombIRSymbol scale k*ᵥdressedUncutCurrent source (scale • k)) := by
  exact dressed_uncut_matrix_read detector source (scale • k) (wholeCoulombIRSymbol scale k)

theorem checked_actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp }⟩

theorem checked_actual_active_window_nonempty (detector source : DressedEvent) :
    ∃scale : ℝ,0 < scale ∧ ∃k : PhysicalMomentum,0 < spatialSquare k ∧
      scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source := by
  have oneNotZero : (1:Fin 3)≠0 := by decide
  have twoNotZero : (2:Fin 3)≠0 := by decide
  refine ⟨movingCoulombRadius detector source/2,half_pos (moving_coulomb_radius_positive detector source),
    (fun i=>if i=0 then 1 else 0),?_,?_⟩
  · norm_num [spatialSquare,oneNotZero,twoNotZero]
  · norm_num [spatialSquare,oneNotZero,twoNotZero]
    linarith [moving_coulomb_radius_positive detector source]

theorem checked_zero_momentum_inactive (detector source : DressedEvent) (scale : ℝ) : movingCoulombSymbol detector source scale 0=0 := by
  norm_num [movingCoulombSymbol,spatialSquare]

end LowEnergy.GaussComposite.ActualDressedUncutMovingAudit

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

elab "#audit_dressed_uncut_moving" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutMomentum,`H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUncutMovingCoulomb]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_moving_potential,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressedMovingBudget,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.movingCoulombRadius,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.movingCoulombSymbol,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_cut_symbol_return,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.movingCoulombPacket,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_origin_spatial_limit]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_dressed_uncut_current_continuous,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_dressed_uncut_matrix_joint_continuous,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_dressed_uncut_moving_potential,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_dressed_moving_static_uniform,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_dressed_moving_static_domination,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_moving_cut_symbol_return,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_moving_coulomb_origin_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_true_fourier_endpoints,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_actual_active_window_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_zero_momentum_inactive]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous,#[
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointResolvent_continuous,
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressedUncutCurrent]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressedUncutMatrixRead]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_moving_potential,#[
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_static_green_scaled]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous,
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_static_green_uniform]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_radius_positive,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_cut_symbol_return,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_generated,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.movingCoulombSymbol]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination,
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_coulomb_ir_symbol_actual]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_integrable,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_physical_coulomb_budget_integrable,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_physical_coulomb_budget_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_origin_spatial_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_static_full_origin]),
    (``LowEnergy.GaussComposite.ActualDressedUncutMovingAudit.checked_true_fourier_endpoints,#[
    ``LowEnergy.GaussComposite.ActualDressedUncutCoulomb.dressed_uncut_matrix_read,
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressedUncutCurrent])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_moving_potential,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_cut_symbol_return,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_origin_spatial_limit]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedNoether.dressedEulerObserver,
    ``LowEnergy.GaussComposite.ActualDressedUncutCurrent.dressedUncutCurrent,
    ``LowEnergy.PreparationVacuumJointFieldResponse.jointResolvent,
    ``LowEnergy.PreparationVacuumFullPoleContinuation.actualJointResolvent_continuous,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.GaussComposite.ActualWholeStatic.wholeCoulombIRSymbol,
    ``LowEnergy.PreparationVacuumStaticPoleResponse.staticInverse]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_UNCUT_MOVING_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_UNCUT_MOVING_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_uncut_moving
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_current_continuous
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_matrix_joint_continuous
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_uncut_moving_potential
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_uniform
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.dressed_moving_static_domination
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_radius_positive
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_cut_symbol_return
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_symbol_bound
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_packet_limit
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_spatial_limit
#print axioms LowEnergy.GaussComposite.ActualDressedUncutMoving.moving_coulomb_origin_spatial_limit

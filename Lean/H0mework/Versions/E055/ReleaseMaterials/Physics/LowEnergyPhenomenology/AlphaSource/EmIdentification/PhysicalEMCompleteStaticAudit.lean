import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMCompleteStaticCharge
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

open Lean Elab Command

noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMCompleteStaticAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumStaticPoleResponse PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationPhysicalStaticSpatialCouplingReturn PreparationPhysicalStaticCompositeProjectionReturn
open PreparationPhysicalJointEMCouplingUnitReturn
open GaussComposite.PhysicalEMCompleteStaticScalar GaussComposite.PhysicalEMCompleteStaticCharge
open CanonicalGradedSpatialSource
open GaussUnitaryHistory (Index)
open Filter
open scoped BigOperators Topology

theorem checked_complete_source_seed :
    emStaticCompleteSeed=(9023/9000:ℂ)*rootTwo*rootFifteen :=
  em_static_seed_generated

section Prepared
variable (direction : PhysicalMomentum) (unit : spatialSquare direction=1)
  (epsD : ℝ) (precD : 0<epsD) (pD kD : PhysicalMomentum) (FD : Index) (cutD : ℕ)
  (zD wD : ℂ) (lD rD : Bool) (aD sD bD tD : Fin 2)
  (epsS : ℝ) (precS : 0<epsS) (pS kS : PhysicalMomentum) (FS : Index) (cutS : ℕ)
  (zS wS : ℂ) (lS rS : Bool) (aS sS bS tS : Fin 2)

theorem checked_ordinary_full_static_scalar :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      sourceStaticSpatialInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed 0:ℝ):ℂ))
      staticApproach (𝓝 (emCompleteStaticReducedScalar
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)) :=
  em_complete_static_reduced_limit direction unit
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS

theorem checked_actual_charge_full_static_scalar :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      emCompleteStaticChargeInteraction direction unit kappa
        epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
        epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed 0:ℝ):ℂ))
      staticApproach (𝓝 (((sourceJointIncrement lD+sourceJointIncrement rD)*
        emCompleteStaticScalar
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS-
        emCompleteStaticInputResidue
          epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
          epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS)/
        ((Stage10.ActionNormalization.phaseMomentum*sourceSpeed 0:ℝ):ℂ))) :=
  em_complete_static_charge_reduced_limit direction unit
    epsD precD pD kD FD cutD zD wD lD rD aD sD bD tD
    epsS precS pS kS FS cutS zS wS lS rS aS sS bS tS

end Prepared
end LowEnergy.GaussComposite.PhysicalEMCompleteStaticAudit
end

private def completeStaticChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def completeStaticClosure (env : Environment)
    (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (completeStaticChildren info).toList ++ pending
      seen := seen.insert name
  return seen

elab "#audit_complete_static_scalar" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners := #[`PhysicalEMCompleteStaticScalar,`H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMCompleteStaticCharge]
  for name in owners do
    unless modules.contains name do throwError m!"MISSING_MODULE {name}"
  let owned := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some index => if owners.contains modules[index.toNat]! then some name else none
    | none => none
  if owned.isEmpty then throwError "EMPTY_OWNED_CLOSURE"
  let mouths := #[
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.emStaticCompleteSeed,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_static_seed_generated,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.emCompleteStaticScalar,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_complete_static_residue,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_complete_static_limit,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.emCompleteStaticReducedScalar,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_complete_static_reduced_limit,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.emCompleteStaticChargeInteraction,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.emCompleteStaticInputInteraction,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.emCompleteStaticInputResidue,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.em_complete_static_charge_split,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.em_complete_static_charge_limit,
    ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.em_complete_static_charge_reduced_limit]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_PUBLIC {name}"
  let consumers := #[
    (``LowEnergy.GaussComposite.PhysicalEMCompleteStaticAudit.checked_complete_source_seed,
      #[``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_static_seed_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMCompleteStaticAudit.checked_ordinary_full_static_scalar,
      #[``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_complete_static_reduced_limit]),
    (``LowEnergy.GaussComposite.PhysicalEMCompleteStaticAudit.checked_actual_charge_full_static_scalar,
      #[``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.em_complete_static_charge_reduced_limit])]
  let all ← completeStaticClosure env (owned ++ (consumers.map Prod.fst).toList)
  let anchors := #[
    ``LowEnergy.PreparationVacuumStaticPoleResponse.staticInverse,
    ``LowEnergy.PreparationVacuumStaticPoleResponse.staticInverseTerms,
    ``LowEnergy.PreparationVacuumStaticPoleResponse.staticResidue,
    ``LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn.sourceStaticComposite_origin,
    ``LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn.sourceStaticCompositeWeight,
    ``LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn.sourceSpatialStaticNativeFieldResidue,
    ``LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn.sourceStaticSpatialInteraction_generated,
    ``LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn.sourceJointChargedCurrent_generated,
    ``LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn.sourceJointCompleted_charge,
    ``SaturationMonoid.PhysicsCore.Stage10.ActionNormalization.phaseMomentum,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_complete_static_residue,
      #[``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_static_seed_generated,
        ``LowEnergy.PreparationPhysicalStaticCompositeProjectionReturn.sourceStaticComposite_origin]),
    (``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_complete_static_limit,
      #[``LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn.sourceStaticSpatialInteraction_generated,
        ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_complete_static_residue]),
    (``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.em_complete_static_charge_split,
      #[``LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn.sourceJointChargedCurrent_generated]),
    (``LowEnergy.GaussComposite.PhysicalEMCompleteStaticCharge.em_complete_static_charge_limit,
      #[``LowEnergy.PreparationPhysicalStaticSpatialCouplingReturn.sourceSpatialStaticNativeFieldResidue,
        ``LowEnergy.GaussComposite.PhysicalEMCompleteStaticScalar.em_complete_static_residue,
        ``LowEnergy.PreparationPhysicalJointEMCouplingUnitReturn.sourceJointChargedCurrent_generated])]
  for (mouth, required) in direct ++ consumers do
    let closed ← completeStaticClosure env [mouth]
    for name in required do
      unless closed.contains name do throwError m!"UNCONSUMED_DIRECT {mouth} {name}"
  let allowed := #[``propext,``Classical.choice,``Quot.sound]
  let mut axioms : Nat := 0
  let mut opaqueCount : Nat := 0
  for name in all.toArray do
    let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
    if info.isUnsafe || info.isPartial then throwError m!"UNTRUSTED {name}"
    match info with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
      unless (info.value? (allowOpaque := true)).isSome do throwError m!"UNREAD {name}"
    | _ => pure ()
    if let .opaqueInfo _ := info then opaqueCount := opaqueCount + 1
    if let .axiomInfo _ := info then
      axioms := axioms + 1
      unless allowed.contains name do throwError m!"UNAUTHORIZED_AXIOM {name}"
  for name in owned ++ (consumers.map Prod.fst).toList do
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do throwError m!"UNAUTHORIZED_ROOT_AXIOM {name} {axiomName}"
  for name in #[`SaturationMonoid.StandardModelConstraint.alphaEMIntegerDenominator,
      `SaturationMonoid.StandardModelConstraint.alphaEMFromIntegerConstraint,
      `SaturationMonoid.StandardModelConstraint.gutWeakMixingInformationRatio] do
    if all.contains name then throwError m!"TARGET_CONTAMINATION {name}"
  for moduleName in modules do
    if (moduleName.toString.toLower.splitOn ".").contains "scratch" then
      throwError m!"SCRATCH_IMPORT {moduleName}"
  logInfo m!"EM_COMPLETE_STATIC_PASS public={mouths.size} owned={owned.length} nodes={all.size} anchors={anchors.size} direct={direct.size} consumers={consumers.size} opaque_all_read={opaqueCount} axioms={axioms} unknown=0 unsafe=0 partial=0"

#audit_complete_static_scalar

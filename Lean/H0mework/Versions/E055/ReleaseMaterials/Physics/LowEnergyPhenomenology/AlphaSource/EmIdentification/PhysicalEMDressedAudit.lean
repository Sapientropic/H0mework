import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMDressedPreparedRead
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

open Lean Elab Command

noncomputable section
namespace LowEnergy.GaussComposite.PhysicalEMDressedAudit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction SourceQuantumScalarChart StageNineHolonomicField
open StageNineDynamicBreakingVacuum
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction
open StageNineP286GaugeConnectionVariation StageNineResidualLimitScalarBalanceClosure
open GaussComposite.PhysicalEMGaugeRealization
open GaussComposite.PhysicalEMDressedCharacter GaussComposite.PhysicalEMDressedPreparedRead
open PreparationPhysicalDressedSpinChargeReturn
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open PreparationVacuumFieldConstraintResponse
open CanonicalGradedSpatialSource GaussComposite.SourceGraph
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open GaussUnitaryHistory (Index)
open Electromagnetic.Identification
open scoped BigOperators InnerProductSpace

theorem checked_em_joint_source_unit (a s : Fin 2) (phi : Scalar)
    (psi : DiracExteriorMatterCarrier) :
    emDressedChargeUnit = (1/2:ℚ) ∧
    originalRead a s (scalarMotherLieAction (p286LieBlockEmbed emDirection) phi) psi+
      originalRead a s phi (emGaugeAction psi)=
      (-(emDressedChargeUnit:ℂ)*Complex.I)*originalRead a s phi psi :=
  ⟨emDressedChargeUnit_value,em_dressed_read a s phi psi⟩

theorem checked_em_actual_prepared_source (epsilon : ℝ) (precision : 0<epsilon)
    (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ)
    (left right : Bool) (a s b t : Fin 2) :
    emDressedPreparedCovector epsilon precision p k F n z w left right a s b t=
      fun i=>(star (emDressedCharacter left)+emDressedCharacter right)*
        sourceCovector p
          (sourceTestApprox F ((finiteFull (p+k) F n z).adjoint
            (completedLeg left a s (sourceProfile epsilon precision))))
          (sourceTestApprox F (finiteFull p F n w
            (completedLeg right b t (sourceProfile epsilon precision)))) i :=
  em_dressed_prepared_source epsilon precision p k F n z w left right a s b t

theorem checked_gt_actual_em_prepared_normalization (epsilon : ℝ) (precision : 0<epsilon)
    (p k : PhysicalMomentum) (F : Index) (n : ℕ) (z w : ℂ)
    (left right : Bool) (a s b t : Fin 2) :
    sourceDressedPreparedCovector epsilon precision p k F n z w left right a s b t=
      fun i=>(-(10/11):ℂ)*
        emDressedPreparedCovector epsilon precision p k F n z w left right a s b t i :=
  em_dressed_gt_prepared epsilon precision p k F n z w left right a s b t

end LowEnergy.GaussComposite.PhysicalEMDressedAudit
end

private def dressedChildren (info : ConstantInfo) : Array Name := Id.run do
  let mut children := info.type.getUsedConstants
  if let some value := info.value? (allowOpaque := true) then
    children := children ++ value.getUsedConstants
  if let .inductInfo value := info then children := children ++ value.ctors.toArray
  if let .recInfo value := info then
    for rule in value.rules do children := children ++ rule.rhs.getUsedConstants
  return children

private def dressedClosure (env : Environment) (roots : List Name) : CommandElabM NameSet := do
  let mut pending := roots
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    unless seen.contains name do
      let some info := env.checked.get.find? name | throwError m!"UNKNOWN {name}"
      pending := (dressedChildren info).toList ++ pending
      seen := seen.insert name
  return seen

elab "#audit_actual_em_dressed_read" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owners := #[`PhysicalEMDressedCharacter,`H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMDressedPreparedRead]
  for name in owners do
    unless modules.contains name do throwError m!"MISSING_MODULE {name}"
  let owned := env.constants.toList.filterMap fun (name, _) =>
    match env.getModuleIdxFor? name with
    | some index => if owners.contains modules[index.toNat]! then some name else none
    | none => none
  if owned.isEmpty then throwError "EMPTY_OWNED_CLOSURE"
  let mouths := #[
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedFundamentalWeight,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedExteriorWeight,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressed_exterior,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedInternalWeight,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedWholeWeight,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressed_basis,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressed_matrix,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_scalar,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_matter,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_scalar_weight,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_matter_weight,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_total_weight,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedChargeUnit,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedChargeUnit_value,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedChargeUnit_pos,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedChargeUnit_ne_zero,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedCharacter,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_read,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_dual,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedFullGenerator,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_creation,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_annihilation,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedFiber,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedTest,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedTest_return,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedLetter,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedLetter_return,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCore,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCore_return,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCompleted,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCompleted_core,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCompleted_return,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedPreparedCovector,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_return,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_source,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_price,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_gt_character,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_gt_completed,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_gt_prepared]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_PUBLIC {name}"
  let consumers := #[
    (``LowEnergy.GaussComposite.PhysicalEMDressedAudit.checked_em_joint_source_unit,
      #[``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedChargeUnit_value,
        ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_read]),
    (``LowEnergy.GaussComposite.PhysicalEMDressedAudit.checked_em_actual_prepared_source,
      #[``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_source]),
    (``LowEnergy.GaussComposite.PhysicalEMDressedAudit.checked_gt_actual_em_prepared_normalization,
      #[``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_gt_prepared])]
  let all ← dressedClosure env (owned ++ (consumers.map Prod.fst).toList)
  let anchors := #[
    ``LowEnergy.GaussComposite.PhysicalEMGaugeRealization.emDirection,
    ``LowEnergy.GaussComposite.PhysicalEMGaugeRealization.emGaugeAction,
    ``LowEnergy.GaussComposite.PhysicalEMVoltage.emGaugeChargeMatrix,
    ``SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.Identification.Composite.scalarBasis,
    ``SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.Identification.Composite.matterBasis,
    ``LowEnergy.PreparationPhysicalDressedSpinChargeReturn.sourceDressedCompleted_return,
    ``LowEnergy.PreparationPhysicalDressedSpinChargeReturn.sourceDressedPrepared_return,
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual]
  for name in anchors do
    unless all.contains name do throwError m!"UNCONSUMED_SOURCE {name}"
  let direct := #[
    (``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_read,
      #[``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressed_exterior,
        ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.em_dressed_total_weight]),
    (``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCompleted_return,
      #[``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_creation,
        ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_annihilation]),
    (``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_source,
      #[``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCompleted_return]),
    (``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_price,
      #[``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_return]),
    (``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_gt_prepared,
      #[``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_gt_character,
        ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_return])]
  for (mouth, required) in direct ++ consumers do
    let closed ← dressedClosure env [mouth]
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
  logInfo m!"EM_DRESSED_READ_PASS public={mouths.size} owned={owned.length} nodes={all.size} anchors={anchors.size} direct={direct.size} consumers={consumers.size} opaque_all_read={opaqueCount} axioms={axioms} unknown=0 unsafe=0 partial=0"

#audit_actual_em_dressed_read

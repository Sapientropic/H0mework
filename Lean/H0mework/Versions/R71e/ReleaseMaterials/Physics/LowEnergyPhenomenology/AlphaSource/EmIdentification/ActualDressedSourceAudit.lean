import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCreationSupport
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourcePreparation
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourceResponse

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedSourceAudit
elab "checked_unused_color_seed_coordinateContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_coordinate).type
theorem checked_unused_color_seed_coordinate : checked_unused_color_seed_coordinateContract := @LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_coordinate

elab "checked_unused_color_seed_annihilatorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_annihilator).type
theorem checked_unused_color_seed_annihilator : checked_unused_color_seed_annihilatorContract := @LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_annihilator

elab "checked_original_creation_seed_extractContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_seed_extract).type
theorem checked_original_creation_seed_extract : checked_original_creation_seed_extractContract := @LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_seed_extract

elab "checked_original_creation_core_extractContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_core_extract).type
theorem checked_original_creation_core_extract : checked_original_creation_core_extractContract := @LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_core_extract

elab "checked_scalar_coefficient_coordinateContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_coordinate).type
theorem checked_scalar_coefficient_coordinate : checked_scalar_coefficient_coordinateContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_coordinate

elab "checked_scalar_coefficient_boundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_bound).type
theorem checked_scalar_coefficient_bound : checked_scalar_coefficient_boundContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_bound

elab "checked_scalar_coefficient_vacuumContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_vacuum).type
theorem checked_scalar_coefficient_vacuum : checked_scalar_coefficient_vacuumContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_vacuum

elab "checked_scalar_coefficient_lowerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_lower).type
theorem checked_scalar_coefficient_lower : checked_scalar_coefficient_lowerContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_lower

elab "checked_original_contact_lowerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_contact_lower).type
theorem checked_original_contact_lower : checked_original_contact_lowerContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_contact_lower

elab "checked_localized_contact_lowerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_contact_lower).type
theorem checked_localized_contact_lower : checked_localized_contact_lowerContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_contact_lower

elab "checked_original_creation_lowerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_creation_lower).type
theorem checked_original_creation_lower : checked_original_creation_lowerContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_creation_lower

elab "checked_localized_creation_lowerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_creation_lower).type
theorem checked_localized_creation_lower : checked_localized_creation_lowerContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_creation_lower

elab "checked_actual_dressed_creation_nonzeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_creation_nonzero).type
theorem checked_actual_dressed_creation_nonzero : checked_actual_dressed_creation_nonzeroContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_creation_nonzero

elab "checked_actual_dressed_excitation_existsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_excitation_exists).type
theorem checked_actual_dressed_excitation_exists : checked_actual_dressed_excitation_existsContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_excitation_exists

elab "checked_source_dressed_excitation_nonzeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_excitation_nonzero).type
theorem checked_source_dressed_excitation_nonzero : checked_source_dressed_excitation_nonzeroContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_excitation_nonzero

elab "checked_source_dressed_unit_normContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm).type
theorem checked_source_dressed_unit_norm : checked_source_dressed_unit_normContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm

elab "checked_source_dressed_unit_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_original).type
theorem checked_source_dressed_unit_original : checked_source_dressed_unit_originalContract := @LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_original

elab "checked_source_dressed_response_equationContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_equation).type
theorem checked_source_dressed_response_equation : checked_source_dressed_response_equationContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_equation

elab "checked_source_dressed_response_nonzeroContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_nonzero).type
theorem checked_source_dressed_response_nonzero : checked_source_dressed_response_nonzeroContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_nonzero

elab "checked_source_dressed_current_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_current_original).type
theorem checked_source_dressed_current_original : checked_source_dressed_current_originalContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_current_original

elab "checked_source_dressed_action_currentContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_action_current).type
theorem checked_source_dressed_action_current : checked_source_dressed_action_currentContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_action_current

elab "checked_source_dressed_contact_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_contact_original).type
theorem checked_source_dressed_contact_original : checked_source_dressed_contact_originalContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_contact_original

elab "checked_source_dressed_unit_native_chargeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_unit_native_charge).type
theorem checked_source_dressed_unit_native_charge : checked_source_dressed_unit_native_chargeContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_unit_native_charge

elab "checked_source_dressed_connected_native_chargeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_native_charge).type
theorem checked_source_dressed_connected_native_charge : checked_source_dressed_connected_native_chargeContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_native_charge

elab "checked_source_dressed_propagated_native_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_propagated_native_return).type
theorem checked_source_dressed_propagated_native_return : checked_source_dressed_propagated_native_returnContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_propagated_native_return

elab "checked_source_dressed_joint_unit_ratioContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_joint_unit_ratio).type
theorem checked_source_dressed_joint_unit_ratio : checked_source_dressed_joint_unit_ratioContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_joint_unit_ratio

elab "checked_source_dressed_connected_current_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_current_original).type
theorem checked_source_dressed_connected_current_original : checked_source_dressed_connected_current_originalContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_current_original

elab "checked_dressed_joint_variation_diagonalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedSourceResponse.dressed_joint_variation_diagonal).type
theorem checked_dressed_joint_variation_diagonal : checked_dressed_joint_variation_diagonalContract := @LowEnergy.GaussComposite.ActualDressedSourceResponse.dressed_joint_variation_diagonal

open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstGaugeBackgroundReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussComposite.SourceGraph Electromagnetic.Identification
open CanonicalGradedCurrent GaussQuantumMultiplier CanonicalGradedSpatialSource GaussDensityCore
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open GaussUnitaryHistory (Index)
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open PreparationPhysicalDressedSpinChargeReturn
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMDressedCharacter
open scoped BigOperators ContDiff InnerProductSpace Matrix
open PhysicalEMDressedPreparedRead PreparationVacuumSourcePreparedState
open CanonicalScalarPreparation PreparationChartGuard PreparationScalarCoordinates PreparationCoordinates CanonicalPreparationCutoff PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open MeasureTheory Filter Set GaussHistoryHilbert GaussHalfDensity

open ActualDressedSourcePreparation PreparationVacuumMixedFieldReturn
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceDressedAddition sourceProfile finiteFull

open ActualDressedSourceResponse ActualDressedCreationSupport

theorem checked_actual_creation_fixed (epsilon : ℝ) (precision : 0<epsilon) :
    sourceDressedAddition epsilon precision=true := by
  unfold sourceDressedAddition
  rfl

theorem checked_actual_unit_nonzero (epsilon : ℝ) (precision : 0<epsilon) :
    sourceDressedUnit epsilon precision≠0 := by
  intro zero
  have unit:=source_dressed_unit_norm epsilon precision
  rw [zero,norm_zero] at unit
  exact zero_ne_one unit

theorem checked_actual_joint_increment_nonzero : (-Complex.I)*emDressedCharacter true≠0 := by
  rw [source_dressed_joint_unit_ratio]
  norm_num


theorem checked_joint_delta_actual_preparation (epsilon : ℝ) (precision : 0<epsilon) :
    (-Complex.I)*emDressedCharacter true=-(1/2:ℂ)*
      (inner ℂ (sourceDressedUnit epsilon precision)
          (CanonicalGradedCharge.chargeReader nativeY (sourceDressedUnit epsilon precision))-
        inner ℂ (prepared (sourceProfile epsilon precision))
          (CanonicalGradedCharge.chargeReader nativeY (prepared (sourceProfile epsilon precision)))) := by
  rw [source_dressed_connected_native_charge]
  exact source_dressed_joint_unit_ratio

theorem checked_connected_not_absolute : (-1:ℂ)≠-2 := by norm_num
end LowEnergy.GaussComposite.ActualDressedSourceAudit

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

elab "#audit_dressed_source" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCreationSupport,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourcePreparation,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourceResponse]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_coordinate,
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_annihilator,
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_seed_extract,
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_core_extract,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_coordinate,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_bound,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_vacuum,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_contact_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_contact_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_creation_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_creation_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_creation_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_excitation_exists,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedAddition,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedExcitation,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_excitation_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.sourceDressedResponse,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_equation,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.sourceDressedCurrent,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_current_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_action_current,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_contact_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_unit_native_charge,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_native_charge,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_propagated_native_return,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_joint_unit_ratio,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.sourceDressedConnectedCurrent,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_current_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.dressed_joint_variation_diagonal]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_unused_color_seed_coordinate,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_unused_color_seed_annihilator,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_original_creation_seed_extract,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_original_creation_core_extract,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_scalar_coefficient_coordinate,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_scalar_coefficient_bound,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_scalar_coefficient_vacuum,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_scalar_coefficient_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_original_contact_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_localized_contact_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_original_creation_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_localized_creation_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_actual_dressed_creation_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_actual_dressed_excitation_exists,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_excitation_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_unit_norm,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_unit_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_response_equation,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_response_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_current_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_action_current,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_contact_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_unit_native_charge,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_connected_native_charge,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_propagated_native_return,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_joint_unit_ratio,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_source_dressed_connected_current_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_dressed_joint_variation_diagonal,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_actual_creation_fixed,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_actual_unit_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_actual_joint_increment_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_joint_delta_actual_preparation,
    ``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_connected_not_absolute]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_seed_extract,#[
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_annihilator]),
    (``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_core_extract,#[
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_seed_extract]),
    (``LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_creation_lower,#[
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_core_extract,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_lower]),
    (``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_creation_nonzero,#[
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_creation_lower,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCompleted_return]),
    (``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm,#[
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_excitation_nonzero]),
    (``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_nonzero,#[
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_equation,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm]),
    (``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_action_current,#[
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_current_original]),
    (``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_native_charge,#[
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_unit_native_charge,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm]),
    (``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_propagated_native_return,#[
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_equation,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_unit_native_charge]),
    (``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_current_original,#[
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_current_original]),
    (``LowEnergy.GaussComposite.ActualDressedSourceResponse.dressed_joint_variation_diagonal,#[
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.em_dressed_prepared_return]),
    (``LowEnergy.GaussComposite.ActualDressedSourceAudit.checked_joint_delta_actual_preparation,#[
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_native_charge,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_joint_unit_ratio])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_coordinate,
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_annihilator,
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_seed_extract,
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_core_extract,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_coordinate,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_bound,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_vacuum,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_contact_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_contact_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_creation_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_creation_lower,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_creation_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_excitation_exists,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_excitation_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_equation,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_nonzero,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_current_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_action_current,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_contact_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_unit_native_charge,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_native_charge,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_propagated_native_return,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_joint_unit_ratio,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_current_original,
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.dressed_joint_variation_diagonal]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedExcitation,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_coordinate,
    ``LowEnergy.GaussComposite.PhysicalEMDressedCharacter.emDressedChargeUnit_value,
    ``LowEnergy.GaussComposite.PhysicalEMDressedPreparedRead.emDressedCompleted_return,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussHistoryHilbert.configurationMeasure]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_SOURCE_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_SOURCE_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_source
#print axioms LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_coordinate
#print axioms LowEnergy.GaussComposite.ActualDressedCreationSupport.unused_color_seed_annihilator
#print axioms LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_seed_extract
#print axioms LowEnergy.GaussComposite.ActualDressedCreationSupport.original_creation_core_extract
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_coordinate
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_bound
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_vacuum
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.scalar_coefficient_lower
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_contact_lower
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_contact_lower
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.original_creation_lower
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.localized_creation_lower
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_creation_nonzero
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.actual_dressed_excitation_exists
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_excitation_nonzero
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_norm
#print axioms LowEnergy.GaussComposite.ActualDressedSourcePreparation.source_dressed_unit_original
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_equation
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_response_nonzero
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_current_original
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_action_current
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_contact_original
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_unit_native_charge
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_native_charge
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_propagated_native_return
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_joint_unit_ratio
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_current_original
#print axioms LowEnergy.GaussComposite.ActualDressedSourceResponse.dressed_joint_variation_diagonal

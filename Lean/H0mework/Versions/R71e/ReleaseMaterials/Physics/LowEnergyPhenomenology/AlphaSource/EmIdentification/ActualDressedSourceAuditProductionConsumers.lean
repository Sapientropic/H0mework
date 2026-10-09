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


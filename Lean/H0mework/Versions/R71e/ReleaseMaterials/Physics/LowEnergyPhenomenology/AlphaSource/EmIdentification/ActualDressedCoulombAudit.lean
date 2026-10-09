import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFullCoulomb
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedMovingCoulomb
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCoulombWard

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCoulombAudit
elab "checked_dressed_current_physical_transferContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_physical_transfer).type
theorem checked_dressed_current_physical_transfer : checked_dressed_current_physical_transferContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_physical_transfer

elab "checked_dressed_pair_static_same_fourierContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_pair_static_same_fourier).type
theorem checked_dressed_pair_static_same_fourier : checked_dressed_pair_static_same_fourierContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_pair_static_same_fourier

elab "checked_dressed_current_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_original).type
theorem checked_dressed_current_original : checked_dressed_current_originalContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_original

elab "checked_dressed_current_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_continuous).type
theorem checked_dressed_current_continuous : checked_dressed_current_continuousContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_continuous

elab "checked_dressed_matrix_readContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read).type
theorem checked_dressed_matrix_read : checked_dressed_matrix_readContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read

elab "checked_dressed_matrix_read_complex_smulContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read_complex_smul).type
theorem checked_dressed_matrix_read_complex_smul : checked_dressed_matrix_read_complex_smulContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read_complex_smul

elab "checked_dressed_static_full_originContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin).type
theorem checked_dressed_static_full_origin : checked_dressed_static_full_originContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin

elab "checked_dressed_green_contactContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_green_contact).type
theorem checked_dressed_green_contact : checked_dressed_green_contactContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_green_contact

elab "checked_dressed_coulomb_packet_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_original).type
theorem checked_dressed_coulomb_packet_original : checked_dressed_coulomb_packet_originalContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_original

elab "checked_dressed_coulomb_packet_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_limit).type
theorem checked_dressed_coulomb_packet_limit : checked_dressed_coulomb_packet_limitContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_limit

elab "checked_dressed_coulomb_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_spatial_limit).type
theorem checked_dressed_coulomb_spatial_limit : checked_dressed_coulomb_spatial_limitContract := @LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_spatial_limit

elab "checked_dressed_matrix_joint_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_matrix_joint_continuous).type
theorem checked_dressed_matrix_joint_continuous : checked_dressed_matrix_joint_continuousContract := @LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_matrix_joint_continuous

elab "checked_dressed_moving_static_uniformContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_uniform).type
theorem checked_dressed_moving_static_uniform : checked_dressed_moving_static_uniformContract := @LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_uniform

elab "checked_dressed_moving_static_dominationContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_domination).type
theorem checked_dressed_moving_static_domination : checked_dressed_moving_static_dominationContract := @LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_domination

elab "checked_moving_coulomb_radius_positiveContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_radius_positive).type
theorem checked_moving_coulomb_radius_positive : checked_moving_coulomb_radius_positiveContract := @LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_radius_positive

elab "checked_moving_coulomb_symbol_boundContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_symbol_bound).type
theorem checked_moving_coulomb_symbol_bound : checked_moving_coulomb_symbol_boundContract := @LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_symbol_bound

elab "checked_moving_coulomb_packet_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_integrable).type
theorem checked_moving_coulomb_packet_integrable : checked_moving_coulomb_packet_integrableContract := @LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_integrable

elab "checked_moving_coulomb_packet_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_limit).type
theorem checked_moving_coulomb_packet_limit : checked_moving_coulomb_packet_limitContract := @LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_limit

elab "checked_moving_coulomb_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_spatial_limit).type
theorem checked_moving_coulomb_spatial_limit : checked_moving_coulomb_spatial_limitContract := @LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_spatial_limit

elab "checked_dressed_joint_connected_current_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_connected_current_return).type
theorem checked_dressed_joint_connected_current_return : checked_dressed_joint_connected_current_returnContract := @LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_connected_current_return

elab "checked_dressed_joint_whole_four_termsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_whole_four_terms).type
theorem checked_dressed_joint_whole_four_terms : checked_dressed_joint_whole_four_termsContract := @LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_whole_four_terms

elab "checked_dressed_joint_static_four_termsContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_static_four_terms).type
theorem checked_dressed_joint_static_four_terms : checked_dressed_joint_static_four_termsContract := @LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_static_four_terms

elab "checked_dressed_connected_reader_contactContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_reader_contact).type
theorem checked_dressed_connected_reader_contact : checked_dressed_connected_reader_contactContract := @LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_reader_contact

elab "checked_dressed_connected_action_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_action_derivative).type
theorem checked_dressed_connected_action_derivative : checked_dressed_connected_action_derivativeContract := @LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_action_derivative

elab "checked_dressed_moving_origin_spatial_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_moving_origin_spatial_limit).type
theorem checked_dressed_moving_origin_spatial_limit : checked_dressed_moving_origin_spatial_limitContract := @LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_moving_origin_spatial_limit

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open ActualWholeStatic ActualEMCarrierOwn MeasureTheory Filter Set
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldCovector
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open ActualDressedSourcePreparation ActualDressedSourceResponse ActualDressedJointWard ActualDressedActionPhase
open ActualDressedFullCoulomb ActualDressedMovingCoulomb CanonicalPhysicalYResolvent
open CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap InnerProductSpace
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull
  currentVertex chargeReader dressedJointInput sourceDressedResponse

open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalFeedback PreparationVacuumFullOriginResponse
open ActualDressedCoulombWard
attribute [local irreducible] dressedCurrent dressedOriginCurrent dressedMatrixRead sourceTestApprox fieldForm fieldJets sourceCovector

theorem actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.ofNonempty
    cut := 0
    energy := Complex.I
    nonreal := by simp
  }⟩

theorem real_energy_excluded (event : DressedEvent) : event.energy≠0 := by
  intro zero
  exact event.nonreal (by rw [zero]; simp)

theorem actual_moving_window_nonempty (detector source : DressedEvent) :
    ∃ scale : ℝ, 0 < scale ∧ scale < movingCoulombRadius detector source := by
  have positive := moving_coulomb_radius_positive detector source
  exact ⟨movingCoulombRadius detector source / 2, by linarith, by linarith⟩


theorem checked_active_moving_endpoints (detector source : DressedEvent)
    (scale : ℝ) (k : PhysicalMomentum) (positive : 0 < scale) (spatial : 0 < spatialSquare k)
    (inside : scale * Real.sqrt (spatialSquare k) < movingCoulombRadius detector source) :
    movingCoulombSymbol detector source scale k =
      dotProduct (dressedCurrent detector (-(scale • k)))
        (wholeCoulombIRSymbol scale k *ᵥ dressedCurrent source (scale • k)) := by
  rw [movingCoulombSymbol, if_pos ⟨positive, spatial, inside⟩, dressed_matrix_read]
end LowEnergy.GaussComposite.ActualDressedCoulombAudit

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

elab "#audit_dressed_coulomb" : command => do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => (env.getModuleIdxFor? name).map fun i => modules[i.toNat]!
  let candidates := #[`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFullCoulomb,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedMovingCoulomb,`H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCoulombWard]
  let owned := env.constants.toList.filterMap fun (name, _) =>
    if (owner name).any candidates.contains then some name else none
  let mouths := #[
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.DressedEvent,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressedCurrent,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_physical_transfer,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_pair_static_same_fourier,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_original,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_continuous,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressedMatrixRead,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read_complex_smul,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressedOriginCurrent,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_green_contact,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressedCoulombPacket,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_original,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_matrix_joint_continuous,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_uniform,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressedMovingBudget,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_domination,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.movingCoulombRadius,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.movingCoulombSymbol,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.movingCoulombPacket,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressedBackgroundCurrent,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressedBackgroundChargedCurrent,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressedJointConnectedCurrent,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressedJointCurrentRemainder,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_connected_current_return,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_whole_four_terms,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_static_four_terms,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_reader_contact,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressedConnectedForm,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_action_derivative,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_moving_origin_spatial_limit]
  for name in mouths do
    unless owned.contains name do throwError m!"MISSING_MOUTH {name}"
  let tests := #[
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_current_physical_transfer,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_pair_static_same_fourier,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_current_original,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_current_continuous,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_matrix_read,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_matrix_read_complex_smul,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_static_full_origin,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_green_contact,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_coulomb_packet_original,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_matrix_joint_continuous,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_moving_static_uniform,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_moving_static_domination,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_joint_connected_current_return,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_joint_whole_four_terms,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_joint_static_four_terms,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_connected_reader_contact,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_connected_action_derivative,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_dressed_moving_origin_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.actual_event_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.real_energy_excluded,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.actual_moving_window_nonempty,
    ``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_active_moving_endpoints]
  let direct := #[
    (``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_pair_static_same_fourier,#[
    ``LowEnergy.PreparationVacuumFullOriginResponse.actualMomentum,
    ``LowEnergy.PreparationVacuumPhysicalCurrentLaplaceReturn.sourcePhysicalTransfer]),
    (``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_original,#[
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_connected_current_original]),
    (``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_continuous,#[
    ``LowEnergy.GaussComposite.PhysicalEMTransferCurrent.currentVertex_transfer_continuous]),
    (``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin,#[
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressedOriginCurrent,
    ``LowEnergy.GaussComposite.ActualWholeStatic.wholeStaticLimit]),
    (``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_green_contact,#[
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen]),
    (``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_original,#[
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_coulomb_ir_packet_integrable,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read_complex_smul]),
    (``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_limit,#[
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_coulomb_ir_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin]),
    (``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_spatial_limit,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_limit]),
    (``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_matrix_joint_continuous,#[
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_continuous]),
    (``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_uniform,#[
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_matrix_joint_continuous,
    ``LowEnergy.GaussComposite.ActualWholeStatic.whole_static_green_uniform]),
    (``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_symbol_bound,#[
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_domination]),
    (``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_integrable,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_physical_coulomb_budget_integrable,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_symbol_bound]),
    (``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_uniform,
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_physical_coulomb_budget_integrable]),
    (``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_spatial_limit,#[
    ``LowEnergy.GaussComposite.ActualEMCarrierOwn.em_newton_massless_convolution,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_limit]),
    (``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_connected_current_return,#[
    ``LowEnergy.GaussComposite.ActualDressedJointWard.dressed_joint_current_return,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressedBackgroundChargedCurrent,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressedJointCurrentRemainder]),
    (``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_whole_four_terms,#[
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_connected_current_return,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressedJointCurrentRemainder]),
    (``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_static_four_terms,#[
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_whole_four_terms,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin]),
    (``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_reader_contact,#[
    ``LowEnergy.GaussComposite.ActualDressedSourceResponse.source_dressed_contact_original]),
    (``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_action_derivative,#[
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_original,
    ``LowEnergy.PreparationVacuumFieldCovector.sourceCovector_derivative]),
    (``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_moving_origin_spatial_limit,#[
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin]),
    (``LowEnergy.GaussComposite.ActualDressedCoulombAudit.checked_active_moving_endpoints,#[
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.movingCoulombSymbol,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read])]
  for (mouth,required) in direct do packageCertRequire env mouth required
  let testProducers := #[
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_physical_transfer,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_pair_static_same_fourier,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_original,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_continuous,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read_complex_smul,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_green_contact,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_original,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_matrix_joint_continuous,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_uniform,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_domination,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_radius_positive,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_symbol_bound,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_integrable,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_limit,
    ``LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_spatial_limit,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_connected_current_return,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_whole_four_terms,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_static_four_terms,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_reader_contact,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_action_derivative,
    ``LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_moving_origin_spatial_limit]
  for i in [:testProducers.size] do packageCertRequire env tests[i]! #[testProducers[i]!]
  let all ← packageCertClosure env (owned ++ tests.toList)
  let anchors := #[
    ``SaturationMonoid.PhysicsCore.StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource,
    ``SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.actual,
    ``LowEnergy.PreparationVacuumSourcePreparedResponse.sourceProfile,
    ``LowEnergy.GaussComposite.ActualDressedSourcePreparation.sourceDressedUnit,
    ``LowEnergy.CanonicalPhysicalYResolvent.finiteFull,
    ``LowEnergy.PreparationVacuumFullOriginResponse.actualMomentum,
    ``LowEnergy.PreparationVacuumOriginalGreenFeedback.sourceGreen,
    ``LowEnergy.PreparationVacuumFullOriginResponse.fullNativeOrigin,
    ``LowEnergy.PreparationVacuumStaticPoleResponse.staticInverse,
    ``LowEnergy.GaussComposite.ActualDressedJointWard.dressedJointInput,
    ``LowEnergy.PreparationVacuumFullFieldRiesz.contactVertex,
    ``LowEnergy.PreparationVacuumStaticSpatialSource.sourceSpatialMomentum]
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
  if let some path ← liftIO (IO.getEnv "ALPHA_DRESSED_COULOMB_AUDIT_OUTPUT") then
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
  logInfo m!"DRESSED_COULOMB_PASS public={mouths.size} owned={owned.length} tests={tests.size} nodes={all.size} anchors={anchors.size} direct={direct.size} opaque_all_read={opaques} axioms={axioms} unknown=0 unsafe=0 partial=0"
#audit_dressed_coulomb
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_physical_transfer
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_pair_static_same_fourier
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_original
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_current_continuous
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_matrix_read_complex_smul
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_static_full_origin
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_green_contact
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_original
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_packet_limit
#print axioms LowEnergy.GaussComposite.ActualDressedFullCoulomb.dressed_coulomb_spatial_limit
#print axioms LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_matrix_joint_continuous
#print axioms LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_uniform
#print axioms LowEnergy.GaussComposite.ActualDressedMovingCoulomb.dressed_moving_static_domination
#print axioms LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_radius_positive
#print axioms LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_symbol_bound
#print axioms LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_integrable
#print axioms LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_packet_limit
#print axioms LowEnergy.GaussComposite.ActualDressedMovingCoulomb.moving_coulomb_spatial_limit
#print axioms LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_connected_current_return
#print axioms LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_whole_four_terms
#print axioms LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_joint_static_four_terms
#print axioms LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_reader_contact
#print axioms LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_connected_action_derivative
#print axioms LowEnergy.GaussComposite.ActualDressedCoulombWard.dressed_moving_origin_spatial_limit

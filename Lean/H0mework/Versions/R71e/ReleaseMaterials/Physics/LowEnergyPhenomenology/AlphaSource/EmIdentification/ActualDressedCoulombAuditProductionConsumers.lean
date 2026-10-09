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


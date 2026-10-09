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


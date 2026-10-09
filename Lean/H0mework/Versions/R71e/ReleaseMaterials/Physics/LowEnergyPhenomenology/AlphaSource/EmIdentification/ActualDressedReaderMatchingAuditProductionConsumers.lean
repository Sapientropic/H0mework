import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderComponents
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCutReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedReaderMatching

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit
elab "checked_temporal_fiber_residual_sourceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source).type
theorem checked_temporal_fiber_residual_source : checked_temporal_fiber_residual_sourceContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_source

elab "checked_temporal_fiber_residual_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_integrable).type
theorem checked_temporal_fiber_residual_integrable : checked_temporal_fiber_residual_integrableContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_residual_integrable

elab "checked_temporal_fiber_firstContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first).type
theorem checked_temporal_fiber_first : checked_temporal_fiber_firstContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_fiber_first

elab "checked_temporal_reader_form_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated).type
theorem checked_temporal_reader_form_generated : checked_temporal_reader_form_generatedContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_form_generated

elab "checked_temporal_reader_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated).type
theorem checked_temporal_reader_generated : checked_temporal_reader_generatedContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_generated

elab "checked_temporal_reader_compensation_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_compensation_price).type
theorem checked_temporal_reader_compensation_price : checked_temporal_reader_compensation_priceContract := @LowEnergy.GaussComposite.ActualDressedReaderComponents.temporal_reader_compensation_price

elab "checked_cut_tail_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated).type
theorem checked_cut_tail_generated : checked_cut_tail_generatedContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_tail_generated

elab "checked_cut_jet_error_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price).type
theorem checked_cut_jet_error_price : checked_cut_jet_error_priceContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_jet_error_price

elab "checked_cut_retainer_leak_retainedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_retainer_leak_retained).type
theorem checked_cut_retainer_leak_retained : checked_cut_retainer_leak_retainedContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_retainer_leak_retained

elab "checked_joint_generator_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.joint_generator_original).type
theorem checked_joint_generator_original : checked_joint_generator_originalContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.joint_generator_original

elab "checked_cut_resolvent_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return).type
theorem checked_cut_resolvent_return : checked_cut_resolvent_returnContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_return

elab "checked_cut_resolvent_error_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_error_price).type
theorem checked_cut_resolvent_error_price : checked_cut_resolvent_error_priceContract := @LowEnergy.GaussComposite.ActualDressedCutReturn.cut_resolvent_error_price

elab "checked_temporal_cut_noether_matchContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match).type
theorem checked_temporal_cut_noether_match : checked_temporal_cut_noether_matchContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.temporal_cut_noether_match

elab "checked_dressed_temporal_cut_noetherContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether).type
theorem checked_dressed_temporal_cut_noether : checked_dressed_temporal_cut_noetherContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_cut_noether

elab "checked_dressed_temporal_coulomb_matchContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_coulomb_match).type
theorem checked_dressed_temporal_coulomb_match : checked_dressed_temporal_coulomb_matchContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_temporal_coulomb_match

elab "checked_dressed_original_retainedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained).type
theorem checked_dressed_original_retained : checked_dressed_original_retainedContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_retained

elab "checked_dressed_original_right_leakContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_right_leak).type
theorem checked_dressed_original_right_leak : checked_dressed_original_right_leakContract := @LowEnergy.GaussComposite.ActualDressedReaderMatching.dressed_original_right_leak

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard


open ActualDressedActionPhase PreparationVacuumTemporalCharge PreparationVacuumLowerClassical


open ActualDressedTemporalNormalization GaussFockPair PreparationVacuumSourceActionJets
open MeasureTheory Filter Set


open ActualDressedTemporalForm ActualDressedJointTemporal ActualDressedJointOrbitCurrent
open ActualDressedFullCoulomb PreparationVacuumWeightedChargeActionWard
open PreparationVacuumSourceChargeWard PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open scoped Topology InnerProductSpace
open PreparationVacuumFieldConstraintResponse CanonicalPhysicalYResolvent PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalScalarPreparation GaussComposite.SourceGraph
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse chargeReader


open PreparationVacuumFieldCovector PreparationVacuumRawJointFeedback PreparationVacuumCausalFieldResponse
open PreparationVacuumActionDecomposition PreparationVacuumGradedTransport
open ActualDressedTemporalCurrent


open ActualDressedReaderComponents ActualDressedCutReturn ActualDressedNoether
open CanonicalPhysicalYResolvent
attribute [local irreducible] currentVertex currentRestriction temporalReaderCompensation noetherReader
  jointResolvent dressedEulerObserver


open ActualDressedReaderMatching
open PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open CanonicalPhysicalSpatial FullYSourceCutoffVolterra
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

theorem checked_generic_leak_cannot_drop : (0:ℂ)-1≠0-0*1 := by norm_num

end LowEnergy.GaussComposite.ActualDressedReaderMatchingAudit


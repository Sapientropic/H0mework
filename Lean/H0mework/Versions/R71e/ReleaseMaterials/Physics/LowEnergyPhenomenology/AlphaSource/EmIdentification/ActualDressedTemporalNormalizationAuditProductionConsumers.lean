import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalNormalization
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalForm
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalCurrent

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit
elab "checked_original_temporal_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action).type
theorem checked_original_temporal_action : checked_original_temporal_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalNormalization.original_temporal_action

elab "checked_canonical_temporal_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action).type
theorem checked_canonical_temporal_action : checked_canonical_temporal_actionContract := @LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_action

elab "checked_canonical_temporal_quantizedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized).type
theorem checked_canonical_temporal_quantized : checked_canonical_temporal_quantizedContract := @LowEnergy.GaussComposite.ActualDressedTemporalNormalization.canonical_temporal_quantized

elab "checked_temporal_action_fiberContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber).type
theorem checked_temporal_action_fiber : checked_temporal_action_fiberContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_fiber

elab "checked_temporal_action_formContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_form).type
theorem checked_temporal_action_form : checked_temporal_action_formContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_form

elab "checked_temporal_action_global_readerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_global_reader).type
theorem checked_temporal_action_global_reader : checked_temporal_action_global_readerContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_global_reader

elab "checked_temporal_action_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_integrable).type
theorem checked_temporal_action_integrable : checked_temporal_action_integrableContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.temporal_action_integrable

elab "checked_em_action_fiberContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber).type
theorem checked_em_action_fiber : checked_em_action_fiberContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_fiber

elab "checked_em_action_formContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form).type
theorem checked_em_action_form : checked_em_action_formContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_form

elab "checked_em_action_integrableContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_integrable).type
theorem checked_em_action_integrable : checked_em_action_integrableContract := @LowEnergy.GaussComposite.ActualDressedTemporalForm.em_action_integrable

elab "checked_dressed_temporal_action_integralContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_integral).type
theorem checked_dressed_temporal_action_integral : checked_dressed_temporal_action_integralContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_integral

elab "checked_dressed_temporal_action_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_limit).type
theorem checked_dressed_temporal_action_limit : checked_dressed_temporal_action_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_temporal_action_limit

elab "checked_original_temporal_weight_coreContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core).type
theorem checked_original_temporal_weight_core : checked_original_temporal_weight_coreContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.original_temporal_weight_core

elab "checked_temporal_raw_noether_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return).type
theorem checked_temporal_raw_noether_return : checked_temporal_raw_noether_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_raw_noether_return

elab "checked_actual_temporal_Y_action_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.actual_temporal_Y_action_limit).type
theorem checked_actual_temporal_Y_action_limit : checked_actual_temporal_Y_action_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.actual_temporal_Y_action_limit

elab "checked_temporal_noether_reader_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return).type
theorem checked_temporal_noether_reader_return : checked_temporal_noether_reader_returnContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.temporal_noether_reader_return

elab "checked_dressed_em_action_limitContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_em_action_limit).type
theorem checked_dressed_em_action_limit : checked_dressed_em_action_limitContract := @LowEnergy.GaussComposite.ActualDressedTemporalCurrent.dressed_em_action_limit

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


open ActualDressedTemporalCurrent
theorem checked_actual_unit_nonzero (event : DressedEvent) : sourceDressedUnit event.epsilon event.precision≠0 := by
  intro h
  have paid:=source_dressed_unit_norm event.epsilon event.precision
  rw [h,norm_zero] at paid
  exact zero_ne_one paid

theorem checked_actual_Y_action_visible (event : DressedEvent) :
    ∀ᶠ readFrame : GaussUnitaryHistory.Index in GaussUnitaryHistory.sourceFilter,
      temporalActionForm 11 event.momentum
        (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))
        (sourceTestApprox readFrame (sourceDressedUnit event.epsilon event.precision))-
      temporalActionForm 11 event.momentum
        (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))
        (sourceTestApprox readFrame (prepared (sourceProfile event.epsilon event.precision)))≠0 := by
  exact (actual_temporal_Y_action_limit event).eventually_ne (by norm_num)

theorem checked_Y_input_nonzero (event : DressedEvent) :
    ActualDressedYJoint.dressedYInput event≠0 := by
  rw [ActualDressedYNoether.actual_Y_input_return]
  intro h
  have zero : sourceDressedUnit event.epsilon event.precision=0 := neg_eq_zero.mp h
  have paid:=source_dressed_unit_norm event.epsilon event.precision
  rw [zero,norm_zero] at paid
  exact zero_ne_one paid

end LowEnergy.GaussComposite.ActualDressedTemporalNormalizationAudit


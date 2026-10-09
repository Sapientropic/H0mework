import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyPolarization
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMGaugeCurvature
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedGaugePole

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit
elab "checked_voltage_transverse_exactContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_transverse_exact).type
theorem checked_voltage_transverse_exact : checked_voltage_transverse_exactContract := @LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_transverse_exact

elab "checked_voltage_initial_transverse_irContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_transverse_ir).type
theorem checked_voltage_initial_transverse_ir : checked_voltage_initial_transverse_irContract := @LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_transverse_ir

elab "checked_voltage_magnetic_irContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_magnetic_ir).type
theorem checked_voltage_magnetic_ir : checked_voltage_magnetic_irContract := @LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_magnetic_ir

elab "checked_voltage_initial_magnetic_irContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_magnetic_ir).type
theorem checked_voltage_initial_magnetic_ir : checked_voltage_initial_magnetic_irContract := @LowEnergy.GaussComposite.ActualEMCauchyDynamic.voltage_initial_magnetic_ir

elab "checked_full_gauge_curvature_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original).type
theorem checked_full_gauge_curvature_original : checked_full_gauge_curvature_originalContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_original

elab "checked_full_gauge_curvature_derivativeContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative).type
theorem checked_full_gauge_curvature_derivative : checked_full_gauge_curvature_derivativeContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_derivative

elab "checked_full_gauge_curvature_holonomicContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_holonomic).type
theorem checked_full_gauge_curvature_holonomic : checked_full_gauge_curvature_holonomicContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_holonomic

elab "checked_full_gauge_curvature_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_continuous).type
theorem checked_full_gauge_curvature_continuous : checked_full_gauge_curvature_continuousContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_curvature_continuous

elab "checked_full_gauge_bf_hessianContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_bf_hessian).type
theorem checked_full_gauge_bf_hessian : checked_full_gauge_bf_hessianContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_bf_hessian

elab "checked_full_gauge_cauchy_eventContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_cauchy_event).type
theorem checked_full_gauge_cauchy_event : checked_full_gauge_cauchy_eventContract := @LowEnergy.GaussComposite.ActualEMGaugeCurvature.full_gauge_cauchy_event

elab "checked_dressed_voltage_spectral_continuousContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_voltage_spectral_continuous).type
theorem checked_dressed_voltage_spectral_continuous : checked_dressed_voltage_spectral_continuousContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_voltage_spectral_continuous

elab "checked_dressed_gauge_clockContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_clock).type
theorem checked_dressed_gauge_clock : checked_dressed_gauge_clockContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_clock

elab "checked_dressed_gauge_field_originalContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_field_original).type
theorem checked_dressed_gauge_field_original : checked_dressed_gauge_field_originalContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_field_original

elab "checked_dressed_gauge_classical_poleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole).type
theorem checked_dressed_gauge_classical_pole : checked_dressed_gauge_classical_poleContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_classical_pole

elab "checked_dressed_gauge_frequency_poleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole).type
theorem checked_dressed_gauge_frequency_pole : checked_dressed_gauge_frequency_poleContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_pole

elab "checked_dressed_gauge_curvature_poleContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_curvature_pole).type
theorem checked_dressed_gauge_curvature_pole : checked_dressed_gauge_curvature_poleContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_curvature_pole

elab "checked_dressed_gauge_frequency_fluxContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux).type
theorem checked_dressed_gauge_frequency_flux : checked_dressed_gauge_frequency_fluxContract := @LowEnergy.GaussComposite.ActualEMDressedGaugePole.dressed_gauge_frequency_flux

open SaturationMonoid.PhysicsCore
open LowEnergy.GaussComposite.ActualEMCauchyDynamic LowEnergy.GaussComposite.ActualEMGaugeCurvature
open LowEnergy.GaussComposite.ActualEMDressedGaugePole
open LowEnergy.PreparationVacuumPhysicalCharacteristic LowEnergy.PreparationVacuumPhysicalFeedback
open LowEnergy.CanonicalGradedSpatialSource
open scoped Matrix BigOperators Topology

theorem checked_scale_nonempty : scaleApproach.NeBot := scaleApproach_nonempty

theorem checked_full_curvature_channels : Fintype.card (Fin 6 × Fin 12) = 72 := by decide

theorem checked_restricted_channels_distinct : Fintype.card (Fin 6 × Fin 12) ≠ 36 := by decide

theorem checked_transverse_not_arbitrary_zero :
    voltageTransverseRead (![1,0,0]) (![0,1,0]) 0 1 = 1 := by
  norm_num [voltageTransverseRead]

theorem checked_imaginary_jet_not_real :
    (gaugeFourierJet 0 (fun _ => Complex.I) true).1 0 ≠
      (gaugeFourierJet 0 (fun _ => Complex.I) false).1 0 := by
  norm_num [gaugeFourierJet]
end LowEnergy.GaussComposite.ActualEMDressedGaugePoleAudit


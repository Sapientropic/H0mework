import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhysicalClockJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeClockFlux
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMDressedGaugePole
import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit
elab "checked_dressed_coincident_polarization_kernelContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel).type
theorem checked_dressed_coincident_polarization_kernel : checked_dressed_coincident_polarization_kernelContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_polarization_kernel

elab "checked_dressed_coincident_clock_jet_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated).type
theorem checked_dressed_coincident_clock_jet_generated : checked_dressed_coincident_clock_jet_generatedContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_coincident_clock_jet_generated

elab "checked_dressed_synchronized_pencil_original_actionContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action).type
theorem checked_dressed_synchronized_pencil_original_action : checked_dressed_synchronized_pencil_original_actionContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_synchronized_pencil_original_action

elab "checked_dressed_native_clock_flux_generatedContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_clock_flux_generated).type
theorem checked_dressed_native_clock_flux_generated : checked_dressed_native_clock_flux_generatedContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_clock_flux_generated

elab "checked_dressed_native_physical_frequency_fluxContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_physical_frequency_flux).type
theorem checked_dressed_native_physical_frequency_flux : checked_dressed_native_physical_frequency_fluxContract := @LowEnergy.GaussComposite.ActualDressedPhysicalClock.dressed_native_physical_frequency_flux

open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumOriginalGreenFeedback
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil ActualDressedHistoryKernel
open ActualDressedClockMoment ActualDressedPhysicalClock ActualEMDressedGaugePole
open MeasureTheory
open scoped Matrix BigOperators Topology Interval

theorem actual_synchronized_window_zero (event : DressedEvent) (transfer : PhysicalMomentum) (z : ℂ) :
    dressedSynchronizedPencil event transfer z 0=0 := by
  rw [dressed_synchronized_pencil_original_action]
  ext i j
  simp [dressedWindowPolarization]

theorem actual_source_sheet_clock (event : DressedEvent) (e s : ℝ) (n : PhysicalMomentum) (T : ℝ) :
    dressedSynchronizedPencil event ((e^2:ℝ) • n) (-Complex.I*(sourceFrequency e s:ℂ)) T=
      dressedNativeWindowPencil event ((e^2:ℝ) • n) (frequencyRay e s n)
        (-Complex.I*(sourceFrequency e s:ℂ)) T := by
  have original:=congrArg
    (fun p=>dressedNativeWindowPencil event ((e^2:ℝ) • n) p (-Complex.I*(sourceFrequency e s:ℂ)) T)
    (dressed_gauge_clock e s n)
  simpa only [dressedSynchronizedPencil,dressedGaugeMomentum] using original

theorem actual_physical_memory_lag_unit (omega t s : ℝ) :
    ‖Complex.exp (((s-t:ℝ):ℂ)*(-Complex.I*(omega:ℂ)))‖=1 := by
  simp [Complex.norm_exp,Complex.mul_re]

end LowEnergy.GaussComposite.ActualDressedPhysicalClockAudit


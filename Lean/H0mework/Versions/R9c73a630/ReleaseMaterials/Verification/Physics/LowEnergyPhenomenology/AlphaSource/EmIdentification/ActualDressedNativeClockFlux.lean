import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhysicalClockJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMAction

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhysicalClock
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumCurrentNativeLaplaceBridge PreparationVacuumOriginalGreenFeedback
open SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil ActualDressedHistoryKernel
open ActualDressedClockMoment ActualEMAction Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] dressedNativeWindowPencil dressedWindowPolarization nativeHessian originalJacobi

/-- Spatial transfer is held in the actual event while both original Fourier clocks vary together. -/
def dressedSynchronizedPencil (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  dressedNativeWindowPencil event transfer
    (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial transfer) z) z T

private theorem window_same_input_clock (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) :
    dressedWindowPolarization event transfer p lambda T=
      dressedWindowPolarization event transfer (sourceInputClock (p 0)) lambda T := by
  funext i j
  unfold dressedWindowPolarization
  apply intervalIntegral.integral_congr
  intro t _
  have same : dressedSignalMatrix event transfer p t i j=
      dressedSignalMatrix event transfer (sourceInputClock (p 0)) t i j := by
    rw [dressed_signal_history_matrix,dressed_signal_history_matrix]
    simp only [sourceInputClock,Pi.single_eq_same]
  simpa only using! congrArg (fun c : ℂ=>laplaceWeight lambda t*c) same

/-- The literal original action and the complete quantum tensor use the same synchronized event. -/
theorem dressed_synchronized_pencil_original_action (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (T : ℝ) :
    dressedSynchronizedPencil event transfer z T=
      (T:ℂ) • emOriginalJacobi
        (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial transfer) z)-
      dressedWindowPolarization event transfer (sourceInputClock z) z T := by
  have timeFactor : dressedClassicalTimeFactor
      (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial transfer) z) z T=(T:ℂ) := by
    simpa only [fullMomentum,Fin.cases_zero] using
      dressed_coincident_clock_factor (fullMomentum (PreparationVacuumPhysicalFeedback.physicalSpatial transfer) z) T
  rw [dressedSynchronizedPencil,dressedNativeWindowPencil,timeFactor,nativeActionFourierHessian_original,
    ←em_jacobi_source,window_same_input_clock]
  rfl

/-- The full original action frequency derivative includes the actual quantum memory jet. -/
def dressedNativeClockFlux (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  (T:ℂ) • (sourceTemporalFirst (PreparationVacuumPhysicalFeedback.physicalSpatial transfer)+
    (2*z) • sourceTemporalSecond)-dressedCoincidentClockJet event transfer z T

private theorem native_clock_entry_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (T : ℝ) (i j : Fin 289) :
    HasDerivAt (fun w=>dressedSynchronizedPencil event transfer w T i j)
      (dressedNativeClockFlux event transfer z T i j) z := by
  have quantum : HasDerivAt
      (fun w=>dressedWindowPolarization event transfer (sourceInputClock w) w T i j)
      (dressedCoincidentClockJet event transfer z T i j) z := by
    with_reducible_and_instances
      exact hasDerivAt_pi.mp (hasDerivAt_pi.mp
        (dressed_coincident_clock_jet_generated event transfer z T) i) j
  let spatial := PreparationVacuumPhysicalFeedback.physicalSpatial transfer
  have original : (fun w=>dressedSynchronizedPencil event transfer w T i j)=
      fun w=>(T:ℂ)*(originalJacobi (fullMomentum spatial 0) i j+
        w*sourceTemporalFirst spatial i j+w^2*sourceTemporalSecond i j)-
        dressedWindowPolarization event transfer (sourceInputClock w) w T i j := by
    funext w
    rw [dressed_synchronized_pencil_original_action,em_jacobi_source,sourceTemporalPencil_original]
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,spatial]
  rw [original]
  have initial := hasDerivAt_const z (originalJacobi (fullMomentum spatial 0) i j)
  have first := (hasDerivAt_id z).mul_const (sourceTemporalFirst spatial i j)
  have second := ((hasDerivAt_id z).pow 2).mul_const (sourceTemporalSecond i j)
  have generated := (((initial.add first).add second).const_mul (T:ℂ)).sub quantum
  convert! generated using 1
  simp [dressedNativeClockFlux,spatial]
  ring

theorem dressed_native_clock_flux_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (T : ℝ) :
    HasDerivAt (fun w=>dressedSynchronizedPencil event transfer w T)
      (dressedNativeClockFlux event transfer z T) z := by
  exact hasDerivAt_pi.mpr (fun i=>hasDerivAt_pi.mpr (fun j=>
    native_clock_entry_derivative event transfer z T i j))

/-- The physical real frequency has its original minus-i clock coefficient, exactly once. -/
theorem dressed_native_physical_frequency_flux (event : DressedEvent) (transfer : PhysicalMomentum)
    (omega : ℝ) (T : ℝ) :
    HasDerivAt (fun w : ℝ=>dressedSynchronizedPencil event transfer (-Complex.I*(w:ℂ)) T)
      ((-Complex.I) • dressedNativeClockFlux event transfer (-Complex.I*(omega:ℂ)) T) omega := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have native:=native_clock_entry_derivative event transfer (-Complex.I*(omega:ℂ)) T i j
  have physical:=native.comp (omega:ℂ) ((hasDerivAt_id (omega:ℂ)).const_mul (-Complex.I))
  simpa only [id_eq,one_mul,mul_one,Function.comp_def,Matrix.smul_apply,smul_eq_mul,mul_comm (-Complex.I)] using!
    physical.comp_ofReal

end LowEnergy.GaussComposite.ActualDressedPhysicalClock

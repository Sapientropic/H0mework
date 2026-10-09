import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMSourceLockedCarrier
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPencil

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMSourceDirection
open SaturationMonoid.PhysicsCore StageNineHolonomicField ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] nativeHessian dressedSignalRawEuler dressedSignalQuadrature

/-- The whole actual quantum tensor consumes each source-generated color+Dirac-spin current direction. -/
def lockedWindowPolarization (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (mu : Fin 4) : Matrix (Fin 289) (Fin 3) ℂ :=
  dressedWindowPolarization event transfer p lambda T*lockedInput mu

/-- No quantum output row or source field slot is removed from this generated action response. -/
def lockedWindowPencil (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (mu : Fin 4) : Matrix (Fin 289) (Fin 3) ℂ :=
  dressedNativeWindowPencil event transfer p lambda T*lockedInput mu

/-- The original source clock multiplies the original full289 action Hessian before the actual quantum tensor. -/
theorem locked_pencil_original (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (mu : Fin 4) :
    lockedWindowPencil event transfer p lambda T mu=
      dressedClassicalTimeFactor p lambda T • (nativeFourierHessian nativeHessian p*lockedInput mu)-
        lockedWindowPolarization event transfer p lambda T mu := by
  rw [lockedWindowPencil,dressedNativeWindowPencil,Matrix.sub_mul,Matrix.smul_mul]
  rfl

/-- The actual unit-minus-background signal, with both genuine quadratures, generates this entire response family. -/
theorem locked_window_quantum_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (mu : Fin 4) (n : Fin 3→ℝ) :
    dressedSignalWindow event transfer p lambda T (lockedAmplitude mu n)=
      lockedWindowPolarization event transfer p lambda T mu*ᵥ(fun i=>(n i:ℂ)) := by
  rw [dressed_window_polarization_actual,lockedAmplitude,Matrix.mulVec_mulVec]
  rfl

/-- This is an actual original nonlinear source action consumer, with the same finite prepared duration. -/
theorem locked_original_action_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (mu : Fin 4) (n : Fin 3→ℝ) (future : 0≤T)
    (inside : T<dressedSignalDuration event transfer p (lockedAmplitude mu n)) :
    (fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*
      deriv (fun r=>dressedSignalRawEuler event transfer p (lockedAmplitude mu n) r t i) 0)=
      lockedWindowPencil event transfer p lambda T mu*ᵥ(fun i=>(n i:ℂ)) := by
  rw [dressed_native_window_pencil_generated event transfer p lambda T future (lockedAmplitude mu n) inside]
  rw [lockedAmplitude,Matrix.mulVec_mulVec]
  rfl

/-- The source preparation itself supplies a nonempty time window for every actual locked-direction input. -/
theorem locked_action_window_positive (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (mu : Fin 4) (n : Fin 3→ℝ) :
    0<dressedSignalDuration event transfer p (lockedAmplitude mu n) :=
  dressed_signal_duration_positive event transfer p (lockedAmplitude mu n)

end LowEnergy.GaussComposite.ActualEMSourceDirection

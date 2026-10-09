import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNativeClockFlux

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFieldCovariance
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationNativeActionHessian SourcePropagationMotherEulerKernel
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedPhysicalClock Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] nativeHessian dressedSignalRawEuler dressedSignalMatrix dressedNativeWindowPencil

/-- This is a real coordinate change on the original field, extended to its original Fourier amplitudes. -/
def sourceUnitMatrix (S : Matrix (Fin 289) (Fin 289) ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  S.map Complex.ofRealHom

/-- The same nonlinear Euler one-form is evaluated on the transformed amplitude and reader. -/
def unitRawEuler (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (S : Matrix (Fin 289) (Fin 289) ℝ) (a : SignalAmplitude) (r t : ℝ) : SignalAmplitude :=
  (sourceUnitMatrix S).transpose*ᵥ(fun j=>dressedSignalRawEuler event transfer p (sourceUnitMatrix S*ᵥa) r t j)

/-- Field units do not replace the source's own prepared-history duration. -/
def sourceUnitDuration (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (S : Matrix (Fin 289) (Fin 289) ℝ) (a : SignalAmplitude) : ℝ :=
  dressedSignalDuration event transfer p (sourceUnitMatrix S*ᵥa)

theorem source_unit_duration_positive (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (S : Matrix (Fin 289) (Fin 289) ℝ) (a : SignalAmplitude) :
    0<sourceUnitDuration event transfer p S a :=
  dressed_signal_duration_positive event transfer p (sourceUnitMatrix S*ᵥa)

/-- The original source derivative is generated before its coordinate contraction. -/
theorem unit_raw_euler_generated (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (S : Matrix (Fin 289) (Fin 289) ℝ) (a : SignalAmplitude) (t : ℝ) (future : 0 ≤ t)
    (inside : t<sourceUnitDuration event transfer p S a) (i : Fin 289) :
    HasDerivAt (fun r=>unitRawEuler event transfer p S a r t i)
      (((sourceUnitMatrix S).transpose*ᵥ
        (nativeFourierHessian nativeHessian p*ᵥ
          sourceSignalAmplitude p (sourceUnitMatrix S*ᵥa) (nativeTimePoint t)-
            dressedSignalMatrix event transfer p t*ᵥ(sourceUnitMatrix S*ᵥa))) i) 0 := by
  change HasDerivAt (fun r=>∑j,(sourceUnitMatrix S).transpose i j*
      dressedSignalRawEuler event transfer p (sourceUnitMatrix S*ᵥa) r t j)
    (∑j,(sourceUnitMatrix S).transpose i j*
      ((nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p (sourceUnitMatrix S*ᵥa) (nativeTimePoint t)) j-
        (dressedSignalMatrix event transfer p t*ᵥ(sourceUnitMatrix S*ᵥa)) j)) 0
  apply HasDerivAt.fun_sum
  intro j _
  exact (dressed_signal_raw_euler_generated event transfer p (sourceUnitMatrix S*ᵥa) t future inside j).const_mul _

/-- This reads the original coupled nonlinear finite response in the new field units. -/
def unitWindowResponse (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (S : Matrix (Fin 289) (Fin 289) ℝ) (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) : SignalAmplitude :=
  (sourceUnitMatrix S).transpose*ᵥ(fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*
    deriv (fun r=>dressedSignalRawEuler event transfer p (sourceUnitMatrix S*ᵥa) r t i) 0)

/-- The complete quantum and classical response transform together as one source one-form. -/
def unitWindowPencil (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (S : Matrix (Fin 289) (Fin 289) ℝ) (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  (sourceUnitMatrix S).transpose*dressedNativeWindowPencil event transfer p lambda T*sourceUnitMatrix S

theorem unit_window_generated (event : DressedEvent) (transfer : PhysicalMomentum) (p : Fin 4→ℂ)
    (S : Matrix (Fin 289) (Fin 289) ℝ) (lambda : ℂ) (T : ℝ) (future : 0 ≤ T) (a : SignalAmplitude)
    (inside : T<sourceUnitDuration event transfer p S a) :
    unitWindowResponse event transfer p S lambda T a=unitWindowPencil event transfer p S lambda T*ᵥa := by
  rw [unitWindowResponse,dressed_native_window_pencil_generated event transfer p lambda T future
    (sourceUnitMatrix S*ᵥa) inside]
  simp only [unitWindowPencil,Matrix.mulVec_mulVec,Matrix.mul_assoc]

/-- Synchronization changes no field unit factor or actual source clock. -/
theorem unit_synchronized_clock_flux (event : DressedEvent) (transfer : PhysicalMomentum)
    (S : Matrix (Fin 289) (Fin 289) ℝ) (z : ℂ) (T : ℝ) :
    HasDerivAt (fun w=>(sourceUnitMatrix S).transpose*dressedSynchronizedPencil event transfer w T*sourceUnitMatrix S)
      ((sourceUnitMatrix S).transpose*dressedNativeClockFlux event transfer z T*sourceUnitMatrix S) z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  change HasDerivAt
    (fun w=>∑l,(∑m,(sourceUnitMatrix S).transpose i m*dressedSynchronizedPencil event transfer w T m l)*
      sourceUnitMatrix S l j)
    (∑l,(∑m,(sourceUnitMatrix S).transpose i m*dressedNativeClockFlux event transfer z T m l)*
      sourceUnitMatrix S l j) z
  apply HasDerivAt.fun_sum
  intro l _
  apply HasDerivAt.mul_const
  apply HasDerivAt.fun_sum
  intro m _
  have original : HasDerivAt (fun w=>dressedSynchronizedPencil event transfer w T m l)
      (dressedNativeClockFlux event transfer z T m l) z := by
    with_reducible_and_instances
      exact hasDerivAt_pi.mp (hasDerivAt_pi.mp
        (dressed_native_clock_flux_generated event transfer z T) m) l
  exact original.const_mul _

end LowEnergy.GaussComposite.ActualDressedFieldCovariance

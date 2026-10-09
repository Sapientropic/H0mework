import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFrequencyHalf

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFrequencyHalf
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumCurrentNativeLaplaceBridge
open SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedStaticResponse ActualEMAction
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
attribute [local irreducible] frequencyHalfPolarization frequencyHalfPencil
  dressedWindowPolarization dressedNativeWindowPencil dressedClassicalTimeFactor emOriginalJacobi

/-- The inverse original input integral, before choosing a Fourier read. -/
def frequencyInputNormalizer (p : Fin 4→ℂ) (lambda : ℂ) : ℂ :=
  (sourcePlaneHalfScalar (p 0) lambda)⁻¹

def frequencyQuantumCorrection (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  frequencyInputNormalizer p lambda • frequencyHalfPolarization event transfer p lambda

def frequencyResponsePencil (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  emOriginalJacobi p-frequencyQuantumCorrection event transfer p lambda

def frequencyNormalizedWindow (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  frequencyInputNormalizer p lambda • dressedNativeWindowPencil event transfer p lambda T

attribute [local irreducible] frequencyInputNormalizer frequencyQuantumCorrection
  frequencyResponsePencil frequencyNormalizedWindow

theorem frequency_input_normalizer_generated (p : Fin 4→ℂ) (lambda : ℂ)
    (off : (p 0).re<lambda.re) : frequencyInputNormalizer p lambda=lambda-p 0 := by
  unfold frequencyInputNormalizer
  rw [sourcePlaneHalfScalar_actual (p 0) lambda off,inv_inv]

theorem frequency_amputation_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : (p 0).re<lambda.re) :
    frequencyInputNormalizer p lambda • frequencyHalfPencil event transfer p lambda=
      frequencyResponsePencil event transfer p lambda := by
  have nonzero : lambda-p 0≠0 := by
    intro zero
    have realzero:=congrArg Complex.re zero
    simp only [Complex.sub_re,Complex.zero_re] at realzero
    linarith
  unfold frequencyHalfPencil frequencyResponsePencil frequencyQuantumCorrection
  rw [frequency_input_normalizer_generated p lambda off,smul_sub,smul_smul,
    mul_inv_cancel₀ nonzero,one_smul]

theorem frequency_normalized_window_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re) :
    Tendsto (frequencyNormalizedWindow event transfer p lambda) atTop
      (𝓝 (frequencyResponsePencil event transfer p lambda)) := by
  have inputOff : (p 0).re<lambda.re := (le_max_right 0 (p 0).re).trans_lt off
  have original:=(tendsto_const_nhds (x:=frequencyInputNormalizer p lambda)).smul
    (frequency_half_pencil_limit event transfer p lambda off)
  unfold frequencyNormalizedWindow
  simpa only [frequency_amputation_return event transfer p lambda inputOff] using! original

theorem frequency_input_endpoint (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) :
    1-(lambda-p 0)*dressedClassicalTimeFactor p lambda T=
      Complex.exp ((p 0-lambda)*(T:ℂ)) := by
  have paid:=sourcePlaneWindowScalar_derivative (p 0) lambda T
  change (p 0-lambda)*sourcePlaneWindowScalar (p 0) lambda T=
    Complex.exp ((p 0-lambda)*(T:ℂ))-1 at paid
  rw [static_classical_time_factor p lambda T]
  linear_combination paid

theorem frequency_response_window_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (off : sourceClockGrowth p<lambda.re)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖frequencyResponsePencil event transfer p lambda i j-
      frequencyNormalizedWindow event transfer p lambda T i j‖ ≤
      Real.exp (((p 0).re-lambda.re)*T)*‖emOriginalJacobi p i j‖+
        ‖lambda-p 0‖*dressedSignalTailPrice event transfer p lambda T := by
  have inputOff : (p 0).re<lambda.re := (le_max_right 0 (p 0).re).trans_lt off
  have action : nativeFourierHessian nativeHessian p=emOriginalJacobi p :=
    (nativeActionFourierHessian_original p).trans (em_jacobi_source p).symm
  have endpoint:=frequency_input_endpoint p lambda T
  have difference : frequencyResponsePencil event transfer p lambda i j-
      frequencyNormalizedWindow event transfer p lambda T i j=
        Complex.exp ((p 0-lambda)*(T:ℂ))*emOriginalJacobi p i j-
          (lambda-p 0)*(frequencyHalfPolarization event transfer p lambda i j-
            dressedWindowPolarization event transfer p lambda T i j) := by
    unfold frequencyResponsePencil frequencyNormalizedWindow frequencyQuantumCorrection dressedNativeWindowPencil
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,action,
      frequency_input_normalizer_generated p lambda inputOff]
    calc
      _=(1-(lambda-p 0)*dressedClassicalTimeFactor p lambda T)*emOriginalJacobi p i j-
          (lambda-p 0)*(frequencyHalfPolarization event transfer p lambda i j-
            dressedWindowPolarization event transfer p lambda T i j) := by ring
      _=_ := congrArg (fun z : ℂ=>z*emOriginalJacobi p i j-
        (lambda-p 0)*(frequencyHalfPolarization event transfer p lambda i j-
          dressedWindowPolarization event transfer p lambda T i j)) endpoint
  rw [difference]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul,norm_mul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (frequency_polarization_tail event transfer p lambda off T future i j) (norm_nonneg _))

/-- The input normalization consumes the original nonlinear residual on its generated positive window. -/
theorem frequency_normalized_window_nonlinear (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (future : 0≤T) (a : SignalAmplitude)
    (inside : T<dressedSignalDuration event transfer p a) :
    frequencyInputNormalizer p lambda •
      (fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*
        deriv (fun r=>dressedSignalRawEuler event transfer p a r t i) 0)=
      frequencyNormalizedWindow event transfer p lambda T*ᵥa := by
  rw [dressed_native_window_pencil_generated event transfer p lambda T future a inside]
  unfold frequencyNormalizedWindow
  exact (Matrix.smul_mulVec _ _ _).symm

end LowEnergy.GaussComposite.ActualDressedFrequencyHalf

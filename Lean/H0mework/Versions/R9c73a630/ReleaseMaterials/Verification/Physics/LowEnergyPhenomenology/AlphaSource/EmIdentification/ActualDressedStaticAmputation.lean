import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticHalfPencil

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedStaticResponse
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalHalfAxis PreparationVacuumCurrentNativeLaplaceBridge
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualEMAction
open Filter Set MeasureTheory
open scoped Topology Matrix BigOperators Interval
attribute [local irreducible] dressedWindowPolarization dressedStaticPolarization
  dressedClassicalTimeFactor dressedNativeWindowPencil emOriginalJacobi staticHalfPencil

/-- The amputation is the inverse of the original constant-input halfline factor. -/
def staticInputNormalizer (lambda : ℂ) : ℂ := (sourcePlaneHalfScalar 0 lambda)⁻¹

def staticQuantumCorrection (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  staticInputNormalizer lambda • dressedStaticPolarization event transfer lambda

def staticResponsePencil (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) : Matrix (Fin 289) (Fin 289) ℂ :=
  emOriginalJacobi p-staticQuantumCorrection event transfer lambda

def staticNormalizedWindow (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  staticInputNormalizer lambda • dressedNativeWindowPencil event transfer p lambda T

attribute [local irreducible] staticInputNormalizer staticQuantumCorrection
  staticResponsePencil staticNormalizedWindow

theorem static_input_normalizer_generated (lambda : ℂ) (positive : 0<lambda.re) :
    staticInputNormalizer lambda=lambda := by
  unfold staticInputNormalizer
  rw [sourcePlaneHalfScalar_actual 0 lambda (by simpa using positive),sub_zero,inv_inv]

/-- The complete actual matrix is normalized once by the generated input factor. -/
theorem static_amputation_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (positive : 0<lambda.re) :
    staticInputNormalizer lambda • staticHalfPencil event transfer p lambda=
      staticResponsePencil event transfer p lambda := by
  have nonzero : lambda≠0 := by
    intro zero
    have realzero:=congrArg Complex.re zero
    change lambda.re=0 at realzero
    linarith
  unfold staticHalfPencil staticResponsePencil staticQuantumCorrection
  rw [static_input_normalizer_generated lambda positive,smul_sub,smul_smul,
    mul_inv_cancel₀ nonzero,one_smul]

theorem static_normalized_window_limit (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (staticNormalizedWindow event transfer p lambda) atTop
      (𝓝 (staticResponsePencil event transfer p lambda)) := by
  have original:=(tendsto_const_nhds (x:=staticInputNormalizer lambda)).smul
    (static_half_pencil_limit event transfer p static lambda positive)
  unfold staticNormalizedWindow
  simpa only [static_amputation_return event transfer p lambda positive] using! original

theorem static_constant_input_endpoint (p : Fin 4→ℂ) (static : p 0=0)
    (lambda : ℂ) (T : ℝ) :
    1-lambda*dressedClassicalTimeFactor p lambda T=laplaceWeight lambda T := by
  have paid:=sourcePlaneWindowScalar_derivative 0 lambda T
  change (0-lambda)*sourcePlaneWindowScalar 0 lambda T=
    Complex.exp ((0-lambda)*(T:ℂ))-1 at paid
  have factor:=static_classical_time_factor p lambda T
  rw [static] at factor
  rw [factor]
  unfold laplaceWeight
  simp only [zero_sub] at paid
  linear_combination paid

theorem static_quantum_correction_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖staticQuantumCorrection event transfer lambda i j-
      staticInputNormalizer lambda*dressedWindowPolarization event transfer p lambda T i j‖ ≤
        ‖lambda‖*dressedSignalTailPrice event transfer p lambda T := by
  unfold staticQuantumCorrection
  simp only [Matrix.smul_apply,smul_eq_mul]
  rw [static_input_normalizer_generated lambda positive,←mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left
    (dressed_static_polarization_tail event transfer p static lambda positive T future i j) (norm_nonneg lambda)

/-- Both the original classical endpoint and the complete quantum operator tail are paid. -/
theorem static_response_window_tail (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (static : p 0=0) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (i j : Fin 289) :
    ‖staticResponsePencil event transfer p lambda i j-staticNormalizedWindow event transfer p lambda T i j‖ ≤
      Real.exp (-lambda.re*T)*‖emOriginalJacobi p i j‖+
        ‖lambda‖*dressedSignalTailPrice event transfer p lambda T := by
  have action : SourcePropagationNativeActionHessian.nativeFourierHessian
      SourcePropagationNativeActionHessian.nativeHessian p=emOriginalJacobi p :=
    (SourcePropagationNativeActionHessian.nativeActionFourierHessian_original p).trans (em_jacobi_source p).symm
  have endpoint:=static_constant_input_endpoint p static lambda T
  have difference : staticResponsePencil event transfer p lambda i j-
      staticNormalizedWindow event transfer p lambda T i j=
        laplaceWeight lambda T*emOriginalJacobi p i j-
          lambda*(dressedStaticPolarization event transfer lambda i j-
            dressedWindowPolarization event transfer p lambda T i j) := by
    unfold staticResponsePencil staticNormalizedWindow staticQuantumCorrection dressedNativeWindowPencil
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,action,
      static_input_normalizer_generated lambda positive]
    calc
      _=(1-lambda*dressedClassicalTimeFactor p lambda T)*emOriginalJacobi p i j-
          lambda*(dressedStaticPolarization event transfer lambda i j-
            dressedWindowPolarization event transfer p lambda T i j) := by ring
      _=_ := congrArg (fun z : ℂ=>z*emOriginalJacobi p i j-
        lambda*(dressedStaticPolarization event transfer lambda i j-
          dressedWindowPolarization event transfer p lambda T i j)) endpoint
  rw [difference]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul,norm_mul,laplace_norm]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (dressed_static_polarization_tail event transfer p static lambda positive T future i j) (norm_nonneg lambda))

end LowEnergy.GaussComposite.ActualDressedStaticResponse

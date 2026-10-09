import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalTensor

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPencil
open SaturationMonoid.PhysicsCore StageNineHolonomicField ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open SourcePropagationMotherEulerKernel SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal
open MeasureTheory Filter Set
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] nativeHessian dressedSignalQuadrature dressedSignalRawEuler

private theorem signal_matrix_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (i j : Fin 289) : Continuous (fun t=>dressedSignalMatrix event transfer p t i j) := by
  simp only [dressedSignalMatrix,dressed_signal_complex_original]
  exact (continuous_apply i).comp
    (continuous_clm_apply.1 (dressed_signal_quadrature_continuous event transfer p)
      (Pi.single j (1:ℂ)))

private theorem weight_continuous (lambda : ℂ) : Continuous (laplaceWeight lambda) := by
  unfold laplaceWeight
  fun_prop

private theorem weighted_matrix_integral (A : ℝ→Matrix (Fin 289) (Fin 289) ℂ)
    (continuousA : ∀i j,Continuous (fun t=>A t i j)) (lambda : ℂ) (T : ℝ) (a : Fin 289→ℂ) :
    (fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*(A t*ᵥa) i)=
      (fun i j=>∫t in (0:ℝ)..T,laplaceWeight lambda t*A t i j)*ᵥa := by
  funext i
  change (∫t in (0:ℝ)..T,laplaceWeight lambda t*(∑j,A t i j*a j))=
    ∑j,(∫t in (0:ℝ)..T,laplaceWeight lambda t*A t i j)*a j
  calc
    _=(∫t in (0:ℝ)..T,∑j,(laplaceWeight lambda t*A t i j)*a j) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [Finset.mul_sum,mul_assoc]
    _=∑j,∫t in (0:ℝ)..T,(laplaceWeight lambda t*A t i j)*a j :=
      intervalIntegral.integral_finsetSum (s:=Finset.univ) (μ:=volume)
        (fun j _=>(((weight_continuous lambda).mul (continuousA i j)).mul_const (a j)).intervalIntegrable 0 T)
    _=_ := by simp only [intervalIntegral.integral_mul_const]

/-- No row, field direction or contact is dropped from this actual finite quantum response. -/
def dressedWindowPolarization (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>∫t in (0:ℝ)..T,laplaceWeight lambda t*dressedSignalMatrix event transfer p t i j

theorem dressed_window_polarization_actual (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) :
    dressedSignalWindow event transfer p lambda T a=dressedWindowPolarization event transfer p lambda T*ᵥa := by
  rw [dressed_signal_window_actual]
  simp_rw [dressed_signal_matrix_actual]
  exact weighted_matrix_integral _ (signal_matrix_continuous event transfer p) lambda T a

/-- This is the original Fourier input's time factor, before any amputation. -/
def dressedClassicalTimeFactor (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : ℂ :=
  ∫t in (0:ℝ)..T,laplaceWeight lambda t*Complex.exp ((t:ℂ)*p 0)

private theorem amplitude_on_time (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) :
    sourceSignalAmplitude p a (nativeTimePoint t)=Complex.exp ((t:ℂ)*p 0) • a := by
  funext i
  rw [sourceSignalAmplitude,sourcePhase_time]
  rfl

private theorem classical_integral (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (a : SignalAmplitude) (i : Fin 289) :
    (∫t in (0:ℝ)..T,laplaceWeight lambda t*
      (nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a (nativeTimePoint t)) i)=
      dressedClassicalTimeFactor p lambda T*(nativeFourierHessian nativeHessian p*ᵥa) i := by
  simp_rw [amplitude_on_time,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,←mul_assoc]
  rw [intervalIntegral.integral_mul_const]
  rfl

/-- The whole finite response keeps the actual input time factor and complete quantum tensor. -/
def dressedNativeWindowPencil (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  dressedClassicalTimeFactor p lambda T • nativeFourierHessian nativeHessian p-
    dressedWindowPolarization event transfer p lambda T

/-- The original nonlinear coupled residual generates this entire unaveraged pencil. -/
theorem dressed_native_window_pencil_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (lambda : ℂ) (T : ℝ) (future : 0 ≤ T) (a : SignalAmplitude)
    (inside : T<dressedSignalDuration event transfer p a) :
    (fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*
      deriv (fun r=>dressedSignalRawEuler event transfer p a r t i) 0)=
      dressedNativeWindowPencil event transfer p lambda T*ᵥa := by
  funext i
  have generated : (∫t in (0:ℝ)..T,laplaceWeight lambda t*
      deriv (fun r=>dressedSignalRawEuler event transfer p a r t i) 0)=
      ∫t in (0:ℝ)..T,laplaceWeight lambda t*
        ((nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a (nativeTimePoint t)) i-
          (dressedSignalMatrix event transfer p t*ᵥa) i) := by
    apply intervalIntegral.integral_congr
    intro t member
    rw [uIcc_of_le future] at member
    dsimp only
    rw [(dressed_signal_raw_euler_generated event transfer p a t member.1
      (member.2.trans_lt inside) i).deriv]
  have classicalContinuous : Continuous (fun t=>laplaceWeight lambda t*
      (nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a (nativeTimePoint t)) i) := by
    simp_rw [amplitude_on_time,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul]
    have exponential : Continuous (fun t : ℝ=>Complex.exp ((t:ℂ)*p 0)) := by fun_prop
    exact (weight_continuous lambda).mul (exponential.mul_const _)
  have quantumContinuous : Continuous (fun t=>laplaceWeight lambda t*
      (dressedSignalMatrix event transfer p t*ᵥa) i) := by
    simp_rw [←dressed_signal_matrix_actual]
    exact (weight_continuous lambda).mul ((continuous_apply i).comp
      ((dressed_signal_quadrature_continuous event transfer p).clm_apply continuous_const))
  rw [generated]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub (classicalContinuous.intervalIntegrable 0 T)
    (quantumContinuous.intervalIntegrable 0 T),classical_integral]
  have quantum:=congrFun (weighted_matrix_integral (dressedSignalMatrix event transfer p)
    (signal_matrix_continuous event transfer p) lambda T a) i
  rw [quantum]
  change dressedClassicalTimeFactor p lambda T*(nativeFourierHessian nativeHessian p*ᵥa) i-
    (dressedWindowPolarization event transfer p lambda T*ᵥa) i=
      (dressedNativeWindowPencil event transfer p lambda T*ᵥa) i
  rw [dressedNativeWindowPencil,Matrix.sub_mulVec,Matrix.smul_mulVec]
  rfl

theorem dressed_coincident_clock_factor (p : Fin 4→ℂ) (T : ℝ) :
    dressedClassicalTimeFactor p (p 0) T=(T:ℂ) := by
  have actual (t : ℝ) : laplaceWeight (p 0) t*Complex.exp ((t:ℂ)*p 0)=1 := by
    rw [laplaceWeight,←Complex.exp_add]
    rw [show -(p 0)*(t:ℂ)+(t:ℂ)*p 0=0 by ring,Complex.exp_zero]
  simp only [dressedClassicalTimeFactor,actual,intervalIntegral.integral_const,
    sub_zero,Complex.real_smul,mul_one]

end LowEnergy.GaussComposite.ActualDressedPencil

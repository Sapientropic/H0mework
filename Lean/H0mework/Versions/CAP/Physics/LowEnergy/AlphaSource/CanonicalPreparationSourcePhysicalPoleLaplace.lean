import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePhysicalPoleEulerPrice

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalPoleHalfResponse
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCurrentLaplaceReturn PreparationVacuumPhysicalHalfAxis
open PreparationVacuumCurrentNativeLaplaceBridge PreparationVacuumCurrentSignalOperator
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumFieldConstraintResponse PreparationVacuumGaugeSourceInjection
open Filter Set MeasureTheory
open scoped BigOperators Topology Matrix Interval
attribute [local irreducible] sourcePoleActionEuler sourcePoleEulerCorrection sourcePoleEulerInitial
  sourcePoleCorrectionCoefficient

def sourcePoleLaplaceEta (lambda : ℂ) : ℝ:=lambda.re/8

def sourcePoleCorrectionDecay (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (i : Fin 289) : ℝ:=
  sourcePoleCorrectionCoefficient q pL pR left right (sourcePoleLaplaceEta lambda) i

def sourcePoleCurrentDecay (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (i : Fin 289) : ℝ:=
  ‖sourcePoleEulerInitial q pL pR left right i‖+sourcePoleCorrectionDecay q pL pR left right lambda i

theorem sourcePoleCorrectionDecay_nonnegative (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (i : Fin 289) :
    0 ≤ sourcePoleCorrectionDecay q pL pR left right lambda i:=
  sourcePoleCorrectionCoefficient_nonnegative q pL pR left right _ (by unfold sourcePoleLaplaceEta;positivity) i

theorem sourcePoleCorrection_weighted_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (t : ℝ) (future : 0 ≤ t) (i : Fin 289) :
    ‖laplaceWeight lambda t*sourcePoleEulerCorrection q pL pR left right t i‖ ≤
      sourcePoleCorrectionDecay q pL pR left right lambda i*Real.exp (-(lambda.re/2)*t) :=by
  rw [norm_mul,laplace_norm]
  have paid:=sourcePoleEulerCorrection_price q pL pR left right (sourcePoleLaplaceEta lambda) t
    (by unfold sourcePoleLaplaceEta;positivity) future i
  refine (mul_le_mul_of_nonneg_left paid (Real.exp_pos _).le).trans_eq ?_
  unfold sourcePoleCorrectionDecay
  rw [mul_left_comm,←Real.exp_add]
  congr 1
  congr 1
  unfold sourcePoleLaplaceEta
  ring

private theorem weightedPhase (clock lambda initial : ℂ) (t : ℝ) :
    laplaceWeight lambda t*(Complex.exp (clock*(t:ℂ))*initial)=
      Complex.exp ((clock-lambda)*(t:ℂ))*initial :=by
  unfold laplaceWeight
  rw [←mul_assoc,←Complex.exp_add]
  congr 1
  congr 1
  ring

theorem sourcePoleCurrent_weighted_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (t : ℝ) (future : 0 ≤ t) (i : Fin 289) :
    ‖laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t i‖ ≤
      sourcePoleCurrentDecay q pL pR left right lambda i*Real.exp (-(lambda.re/2)*t) :=by
  rw [sourcePoleActionEuler_generated,mul_add,weightedPhase]
  have original : ‖Complex.exp ((sourcePhysicalClock pL pR left right-lambda)*(t:ℂ))*
      sourcePoleEulerInitial q pL pR left right i‖ ≤
    ‖sourcePoleEulerInitial q pL pR left right i‖*Real.exp (-(lambda.re/2)*t) :=by
    rw [norm_mul,Complex.norm_exp]
    have realpart : ((sourcePhysicalClock pL pR left right-lambda)*(t:ℂ)).re= -lambda.re*t :=by
      simp only [Complex.mul_re,Complex.sub_re,sourcePhysicalClock_re,Complex.ofReal_re,
        Complex.ofReal_im,mul_zero,sub_zero,zero_sub]
    rw [realpart]
    have exponential : Real.exp (-lambda.re*t) ≤ Real.exp (-(lambda.re/2)*t):=
      Real.exp_le_exp.mpr (by nlinarith)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left exponential
      (norm_nonneg (sourcePoleEulerInitial q pL pR left right i))
  refine (norm_add_le _ _).trans ((add_le_add original
    (sourcePoleCorrection_weighted_price q pL pR left right lambda off t future i)).trans_eq ?_)
  unfold sourcePoleCurrentDecay
  ring

private theorem pricedIntegrable (f : ℝ→ℂ) (C rate : ℝ) (positive : 0 < rate)
    (continuous : Continuous f) (bound : ∀t : ℝ,0 ≤ t→‖f t‖ ≤ C*Real.exp (-rate*t)) :
    IntegrableOn f (Ioi (0:ℝ)) :=by
  have majorant : IntegrableOn (fun t : ℝ=>C*Real.exp (-rate*t)) (Ioi (0:ℝ)):=
    (integrableOn_exp_mul_Ioi (a:=-rate) (by linarith) 0).const_mul C
  apply majorant.mono' continuous.aestronglyMeasurable.restrict
  apply (ae_restrict_mem measurableSet_Ioi).mono
  intro t ht
  exact bound t ht.le

theorem sourcePoleCorrection_integrable (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (i : Fin 289) :
    IntegrableOn (fun t=>laplaceWeight lambda t*sourcePoleEulerCorrection q pL pR left right t i)
      (Ioi (0:ℝ)) :=by
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  exact pricedIntegrable _ _ (lambda.re/2) (by positivity)
    (weight.mul (sourcePoleEulerCorrection_continuous q pL pR left right i))
    (fun t ht=>sourcePoleCorrection_weighted_price q pL pR left right lambda off t ht i)

theorem sourcePoleCurrent_integrable (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (i : Fin 289) :
    IntegrableOn (fun t=>laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t i)
      (Ioi (0:ℝ)) :=by
  have weight : Continuous (laplaceWeight lambda):=by unfold laplaceWeight;fun_prop
  exact pricedIntegrable _ _ (lambda.re/2) (by positivity)
    (weight.mul (sourcePoleActionEuler_continuous q pL pR left right i))
    (fun t ht=>sourcePoleCurrent_weighted_price q pL pR left right lambda off t ht i)

def sourcePoleCurrentWindow (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) : SignalAmplitude:=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t i

def sourcePoleCorrectionWindow (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) : SignalAmplitude:=
  fun i=>∫t in (0:ℝ)..T,laplaceWeight lambda t*sourcePoleEulerCorrection q pL pR left right t i

def sourcePoleCurrentHalf (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) : SignalAmplitude:=
  fun i=>∫t in Ioi (0:ℝ),laplaceWeight lambda t*sourcePoleActionEuler q pL pR left right 0 t i

def sourcePoleCorrectionHalf (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) : SignalAmplitude:=
  fun i=>∫t in Ioi (0:ℝ),laplaceWeight lambda t*sourcePoleEulerCorrection q pL pR left right t i

theorem sourcePoleCurrentHalf_generated (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) :
    sourcePoleCurrentHalf q pL pR left right lambda=
      (lambda-sourcePhysicalClock pL pR left right)⁻¹ • sourcePoleEulerInitial q pL pR left right+
        sourcePoleCorrectionHalf q pL pR left right lambda :=by
  have phase : IntegrableOn (fun t : ℝ=>Complex.exp ((sourcePhysicalClock pL pR left right-lambda)*(t:ℂ)))
      (Ioi (0:ℝ)):=
    integrableOn_exp_mul_complex_Ioi (by simp only [Complex.sub_re,sourcePhysicalClock_re,zero_sub];linarith) 0
  funext i
  unfold sourcePoleCurrentHalf sourcePoleCorrectionHalf
  simp_rw [sourcePoleActionEuler_generated,mul_add,weightedPhase]
  rw [integral_add (phase.mul_const _) (sourcePoleCorrection_integrable q pL pR left right lambda off i),
    integral_mul_const]
  have domain : (sourcePhysicalClock pL pR left right).re < lambda.re:=by
    rw [sourcePhysicalClock_re]
    exact off
  change sourcePlaneHalfScalar (sourcePhysicalClock pL pR left right) lambda*
    sourcePoleEulerInitial q pL pR left right i+_= _
  rw [sourcePlaneHalfScalar_actual _ _ domain]
  rfl

theorem sourcePoleCurrentHalf_initial (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) :
    (lambda-sourcePhysicalClock pL pR left right) • sourcePoleCurrentHalf q pL pR left right lambda=
      sourcePoleEulerInitial q pL pR left right+
        (lambda-sourcePhysicalClock pL pR left right) • sourcePoleCorrectionHalf q pL pR left right lambda :=by
  have different : lambda-sourcePhysicalClock pL pR left right≠0 :=by
    intro equal
    have real:=congrArg Complex.re equal
    simp only [Complex.sub_re,sourcePhysicalClock_re,Complex.zero_re,sub_zero] at real
    linarith
  rw [sourcePoleCurrentHalf_generated q pL pR left right lambda off,smul_add,smul_smul,
    mul_inv_cancel₀ different,one_smul]

private theorem pricedTail (f : ℝ→ℂ) (C rate T : ℝ) (positive : 0 < rate) (future : 0 ≤ T)
    (integrable : IntegrableOn f (Ioi (0:ℝ))) (bound : ∀t : ℝ,0 ≤ t→‖f t‖ ≤ C*Real.exp (-rate*t)) :
    ‖(∫t in Ioi (0:ℝ),f t)-(∫t in (0:ℝ)..T,f t)‖ ≤ (C/rate)*Real.exp (-rate*T) :=by
  have tail:=integrable.mono_set (Ioi_subset_Ioi future)
  have equation:=intervalIntegral.integral_interval_add_Ioi integrable tail
  have difference : (∫t in Ioi (0:ℝ),f t)-(∫t in (0:ℝ)..T,f t)=∫t in Ioi T,f t :=by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using equation.symm
  have majorant : IntegrableOn (fun t : ℝ=>C*Real.exp (-rate*t)) (Ioi T):=
    (integrableOn_exp_mul_Ioi (a:=-rate) (by linarith) T).const_mul C
  have majorized : ∀ᵐt ∂volume.restrict (Ioi T),‖f t‖ ≤ C*Real.exp (-rate*t) :=by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    exact bound t (future.trans ht.le)
  rw [difference]
  refine (norm_integral_le_integral_norm _).trans ((integral_mono_ae tail.norm majorant majorized).trans_eq ?_)
  rw [integral_const_mul,integral_exp_mul_Ioi (show -rate < 0 by linarith) T]
  ring

def sourcePoleCorrectionTail (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) (i : Fin 289) : ℝ:=
  (2/lambda.re)*sourcePoleCorrectionDecay q pL pR left right lambda i*Real.exp (-(lambda.re/2)*T)

def sourcePoleCurrentTail (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (T : ℝ) (i : Fin 289) : ℝ:=
  (2/lambda.re)*sourcePoleCurrentDecay q pL pR left right lambda i*Real.exp (-(lambda.re/2)*T)

theorem sourcePoleCorrectionHalf_tail_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (T : ℝ) (future : 0 ≤ T) (i : Fin 289) :
    ‖sourcePoleCorrectionHalf q pL pR left right lambda i-sourcePoleCorrectionWindow q pL pR left right lambda T i‖ ≤
      sourcePoleCorrectionTail q pL pR left right lambda T i :=by
  convert! pricedTail _ _ (lambda.re/2) T (by positivity) future
    (sourcePoleCorrection_integrable q pL pR left right lambda off i)
    (fun t ht=>sourcePoleCorrection_weighted_price q pL pR left right lambda off t ht i) using 1
  unfold sourcePoleCorrectionTail
  ring

theorem sourcePoleCurrentHalf_tail_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (T : ℝ) (future : 0 ≤ T) (i : Fin 289) :
    ‖sourcePoleCurrentHalf q pL pR left right lambda i-sourcePoleCurrentWindow q pL pR left right lambda T i‖ ≤
      sourcePoleCurrentTail q pL pR left right lambda T i :=by
  convert! pricedTail _ _ (lambda.re/2) T (by positivity) future
    (sourcePoleCurrent_integrable q pL pR left right lambda off i)
    (fun t ht=>sourcePoleCurrent_weighted_price q pL pR left right lambda off t ht i) using 1
  unfold sourcePoleCurrentTail
  ring

theorem sourcePoleCorrectionHalf_price (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (i : Fin 289) :
    ‖sourcePoleCorrectionHalf q pL pR left right lambda i‖ ≤
      (2/lambda.re)*sourcePoleCorrectionDecay q pL pR left right lambda i :=by
  have price:=sourcePoleCorrectionHalf_tail_price q pL pR left right lambda off 0 (le_refl _) i
  simpa only [sourcePoleCorrectionWindow,intervalIntegral.integral_same,sub_zero,sourcePoleCorrectionTail,
    mul_zero,neg_zero,Real.exp_zero,mul_one] using price

theorem sourcePoleCurrentWindow_halfAxis (q : PhysicalResponsePoint) (pL pR : PhysicalMomentum)
    (left right : RestStateIndex) (lambda : ℂ) (off : 0 < lambda.re) (i : Fin 289) :
    Tendsto (fun T=>sourcePoleCurrentWindow q pL pR left right lambda T i) atTop
      (𝓝 (sourcePoleCurrentHalf q pL pR left right lambda i)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (sourcePoleCurrent_integrable q pL pR left right lambda off i) tendsto_id

end LowEnergy.PreparationVacuumPhysicalPoleHalfResponse

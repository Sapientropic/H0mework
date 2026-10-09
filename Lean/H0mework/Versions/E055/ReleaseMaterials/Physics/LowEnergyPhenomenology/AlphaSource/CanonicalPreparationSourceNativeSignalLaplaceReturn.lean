import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeTemporalPencil

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentNativeLaplaceBridge
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open SourcePropagationMotherResidualDirections SourcePropagationNoetherTime
open PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumOriginalGreenFeedback PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open Filter MeasureTheory Set
open scoped BigOperators ContDiff Topology Matrix Interval
attribute [local irreducible] nativeHessian nativeJetBasis originalJacobi actualPreparedRawMotherEuler
  sourceCurrentOperator sourceQuadratureCurrent sourceCompatibility

private def planeWeight (clock lambda : ℂ) (t : ℝ) : ℂ:=Complex.exp ((clock-lambda)*(t : ℂ))

private theorem planeWeight_continuous (clock lambda : ℂ) : Continuous (planeWeight clock lambda) :=by
  unfold planeWeight
  fun_prop

private theorem planeWeight_derivative (clock lambda : ℂ) (t : ℝ) :
    HasDerivAt (planeWeight clock lambda) ((clock-lambda)*planeWeight clock lambda t) t :=by
  have actual:=((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)).const_mul (clock-lambda)).cexp
  change HasDerivAt (fun x : ℝ=>Complex.exp ((clock-lambda)*(x : ℂ))) _ t
  simpa only [planeWeight,Function.comp_apply,id_eq,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,mul_comm] using actual

def sourcePlaneWindowScalar (clock lambda : ℂ) (T : ℝ) : ℂ:=∫t in (0 : ℝ)..T,planeWeight clock lambda t

def sourceNativePlaneWindow (clock lambda : ℂ) (T : ℝ) (a : SignalAmplitude) : SignalAmplitude:=
  sourcePlaneWindowScalar clock lambda T • a

def sourceNativeBoundary (spatial : Fin 3→ℂ) (clock lambda : ℂ) (a : SignalAmplitude) (t : ℝ) : SignalAmplitude:=
  planeWeight clock lambda t • ((sourceTemporalFirst spatial+(clock+lambda) • sourceTemporalSecond)*ᵥa)

theorem sourcePlaneWindowScalar_derivative (clock lambda : ℂ) (T : ℝ) :
    (clock-lambda)*sourcePlaneWindowScalar clock lambda T=planeWeight clock lambda T-1 :=by
  have integral:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _=>planeWeight_derivative clock lambda t)
    (((planeWeight_continuous clock lambda).const_mul (clock-lambda)).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_const_mul] at integral
  simpa only [sourcePlaneWindowScalar,planeWeight,Complex.ofReal_zero,mul_zero,Complex.exp_zero] using integral

theorem sourceNativeBoundary_initial (spatial : Fin 3→ℂ) (clock lambda : ℂ) (a : SignalAmplitude) :
    sourceNativeBoundary spatial clock lambda a 0=
      (sourceTemporalFirst spatial+(clock+lambda) • sourceTemporalSecond)*ᵥa :=by
  simp only [sourceNativeBoundary,planeWeight,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_smul]

theorem sourceNativePlaneWindow_ordinary (spatial : Fin 3→ℂ) (clock lambda : ℂ) (T : ℝ) (a : SignalAmplitude) :
    originalJacobi (fullMomentum spatial lambda)*ᵥsourceNativePlaneWindow clock lambda T a=
      originalJacobi (fullMomentum spatial clock)*ᵥsourceNativePlaneWindow clock lambda T a-
        (sourceNativeBoundary spatial clock lambda a T-sourceNativeBoundary spatial clock lambda a 0) :=by
  have matrix:=congrArg (fun A : Matrix (Fin 289) (Fin 289) ℂ=>A*ᵥa)
    (sourceTemporalPencil_difference spatial lambda clock)
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec] at matrix
  have coefficient : (lambda-clock)*sourcePlaneWindowScalar clock lambda T=1-planeWeight clock lambda T :=by
    have paid:=sourcePlaneWindowScalar_derivative clock lambda T
    linear_combination -paid
  rw [sourceNativePlaneWindow,Matrix.mulVec_smul,Matrix.mulVec_smul,sourceNativeBoundary_initial]
  ext i
  have row:=congrFun matrix i
  simp only [sourceNativeBoundary,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,add_comm clock lambda] at row ⊢
  linear_combination sourcePlaneWindowScalar clock lambda T * row +
    ((sourceTemporalFirst spatial+(lambda+clock) • sourceTemporalSecond)*ᵥa) i * coefficient

theorem sourceNativeSignal_weighted (spatial : Fin 3→ℂ) (clock lambda : ℂ) (a : SignalAmplitude) (t : ℝ) :
    laplaceWeight lambda t • sourceSignalAmplitude (fullMomentum spatial clock) a (nativeTimePoint t)=
      planeWeight clock lambda t • a :=by
  ext i
  simp only [sourceSignalAmplitude,sourcePhase_time,fullMomentum,Fin.cases_zero,Pi.smul_apply,smul_eq_mul]
  unfold laplaceWeight planeWeight
  rw [←mul_assoc,←Complex.exp_add]
  congr 2
  ring

def sourceNativeEulerWindow (spatial : Fin 3→ℂ) (clock lambda : ℂ) (a : SignalAmplitude) (T : ℝ) : SignalAmplitude:=
  fun i=>∫t in (0 : ℝ)..T,laplaceWeight lambda t*
    ((nativeEulerLinearJet (signalSecondJet (sourceRealSignal (fullMomentum spatial clock) a) (nativeTimePoint t)) i : ℂ)+
      Complex.I*(nativeEulerLinearJet (signalSecondJet
        (sourceRealSignal (fullMomentum spatial clock) (sourceQuadrature a)) (nativeTimePoint t)) i : ℂ))

theorem sourceNativeEulerWindow_actual (spatial : Fin 3→ℂ) (clock lambda : ℂ) (a : SignalAmplitude) (T : ℝ) :
    sourceNativeEulerWindow spatial clock lambda a T=
      originalJacobi (fullMomentum spatial clock)*ᵥsourceNativePlaneWindow clock lambda T a :=by
  ext i
  unfold sourceNativeEulerWindow
  have same (t : ℝ) : laplaceWeight lambda t*
      ((nativeEulerLinearJet (signalSecondJet (sourceRealSignal (fullMomentum spatial clock) a) (nativeTimePoint t)) i : ℂ)+
        Complex.I*(nativeEulerLinearJet (signalSecondJet
          (sourceRealSignal (fullMomentum spatial clock) (sourceQuadrature a)) (nativeTimePoint t)) i : ℂ))=
      planeWeight clock lambda t*(originalJacobi (fullMomentum spatial clock)*ᵥa) i :=by
    rw [sourceEuler_quadrature,←nativeActionFourierHessian_original]
    change (laplaceWeight lambda t •
      (nativeFourierHessian nativeHessian (fullMomentum spatial clock)*ᵥ
        sourceSignalAmplitude (fullMomentum spatial clock) a (nativeTimePoint t))) i=_
    rw [←Matrix.mulVec_smul,sourceNativeSignal_weighted,Matrix.mulVec_smul,nativeActionFourierHessian_original]
    rfl
  simp_rw [same]
  rw [intervalIntegral.integral_mul_const]
  simp only [sourceNativePlaneWindow,Matrix.mulVec_smul,Pi.smul_apply,smul_eq_mul,sourcePlaneWindowScalar]

/-- This window consumes the amplitude derivative of both original nonlinear prepared source families. -/
def sourcePreparedEulerWindow (q : PhysicalResponsePoint) (spatial : Fin 3→ℂ) (clock lambda : ℂ)
    (a : SignalAmplitude) (T : ℝ) : SignalAmplitude:=fun i=>
  ∫t in (0 : ℝ)..T,laplaceWeight lambda t*deriv (fun r : ℝ=>
    actualPreparedRawMotherEuler q (sourceRealSignal (fullMomentum spatial clock) a)
      (sourceRealSignal_smooth _ a) r t i+
    Complex.I*actualPreparedRawMotherEuler q (sourceRealSignal (fullMomentum spatial clock) (sourceQuadrature a))
      (sourceRealSignal_smooth _ (sourceQuadrature a)) r t i) 0

theorem sourcePreparedEulerWindow_generated (q : PhysicalResponsePoint) (spatial : Fin 3→ℂ)
    (clock lambda : ℂ) (a : SignalAmplitude) (T : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (future : 0 ≤ T) (inside : T<sourceSignalDuration q (fullMomentum spatial clock) a) :
    sourcePreparedEulerWindow q spatial clock lambda a T=
      sourceNativeEulerWindow spatial clock lambda a T-sourceCausalWindow q (fullMomentum spatial clock) lambda T a :=by
  ext i
  have paid (t : ℝ) (ht : t∈uIcc (0 : ℝ) T) :
      deriv (fun r : ℝ=>
        actualPreparedRawMotherEuler q (sourceRealSignal (fullMomentum spatial clock) a) (sourceRealSignal_smooth _ a) r t i+
        Complex.I*actualPreparedRawMotherEuler q (sourceRealSignal (fullMomentum spatial clock) (sourceQuadrature a))
          (sourceRealSignal_smooth _ (sourceQuadrature a)) r t i) 0=
      (nativeFourierHessian nativeHessian (fullMomentum spatial clock)*ᵥ
        sourceSignalAmplitude (fullMomentum spatial clock) a (nativeTimePoint t)) i-
          sourceSignalCurrent q (fullMomentum spatial clock) a t i :=by
    rw [uIcc_of_le future] at ht
    exact (sourcePreparedQuadrature_generated q _ a hz hw t ht.1 (ht.2.trans_lt inside) i).deriv
  have first : IntervalIntegrable (fun t=>planeWeight clock lambda t*
      (originalJacobi (fullMomentum spatial clock)*ᵥa) i) volume 0 T:=
    ((planeWeight_continuous clock lambda).mul_const _).intervalIntegrable 0 T
  have second : IntervalIntegrable (fun t=>laplaceWeight lambda t*sourceSignalCurrent q (fullMomentum spatial clock) a t i) volume 0 T:=by
    have continuous : Continuous (fun t=>laplaceWeight lambda t*sourceSignalCurrent q (fullMomentum spatial clock) a t i):=by
      unfold sourceSignalCurrent laplaceWeight
      exact (by fun_prop : Continuous (fun t : ℝ=>Complex.exp (-lambda*(t : ℂ)))).mul
        (((noetherHistorySourceJet_continuous q _ (sourceTimeSignal_continuous (fullMomentum spatial clock) a) i).1).add
          (((noetherHistorySourceJet_continuous q _ (sourceTimeSignal_continuous (fullMomentum spatial clock) (sourceQuadrature a)) i).1).const_mul Complex.I))
    exact continuous.intervalIntegrable 0 T
  rw [sourceCausalWindow_actual]
  simp only [sourcePreparedEulerWindow,Pi.sub_apply]
  change (∫t in (0 : ℝ)..T,_)=_-_
  rw [intervalIntegral.integral_congr (fun t ht=>by rw [paid t ht,mul_sub]),
    intervalIntegral.integral_sub]
  · congr 1
    unfold sourceNativeEulerWindow
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [sourceEuler_quadrature]
  · have weighted : (fun t=>laplaceWeight lambda t*
        (nativeFourierHessian nativeHessian (fullMomentum spatial clock)*ᵥ
          sourceSignalAmplitude (fullMomentum spatial clock) a (nativeTimePoint t)) i)=
        (fun t=>planeWeight clock lambda t*(originalJacobi (fullMomentum spatial clock)*ᵥa) i) :=by
      funext t
      change (laplaceWeight lambda t • (nativeFourierHessian nativeHessian (fullMomentum spatial clock)*ᵥ
        sourceSignalAmplitude (fullMomentum spatial clock) a (nativeTimePoint t))) i=_
      rw [←Matrix.mulVec_smul,sourceNativeSignal_weighted,Matrix.mulVec_smul,nativeActionFourierHessian_original]
      rfl
    rw [weighted]
    exact first
  · exact second

theorem sourcePreparedEulerWindow_native (q : PhysicalResponsePoint) (spatial : Fin 3→ℂ)
    (clock lambda : ℂ) (a : SignalAmplitude) (T : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (future : 0 ≤ T) (inside : T<sourceSignalDuration q (fullMomentum spatial clock) a) :
    originalJacobi (fullMomentum spatial lambda)*ᵥsourceNativePlaneWindow clock lambda T a=
      sourcePreparedEulerWindow q spatial clock lambda a T+
        sourceCausalWindow q (fullMomentum spatial clock) lambda T a-
          (sourceNativeBoundary spatial clock lambda a T-sourceNativeBoundary spatial clock lambda a 0) :=by
  rw [sourcePreparedEulerWindow_generated q spatial clock lambda a T hz hw future inside,
    sourceNativeEulerWindow_actual,sourceNativePlaneWindow_ordinary]
  abel



def sourceNativeTimeValue (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) : SignalAmplitude:=fun i=>
  ((nativeTimeSignal (sourceRealSignal p a) t).value i : ℂ)+
    Complex.I*((nativeTimeSignal (sourceRealSignal p (sourceQuadrature a)) t).value i : ℂ)

def sourceNativeTimeFirst (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) : SignalAmplitude:=fun i=>
  ((nativeTimeSignal (sourceRealSignal p a) t).first i : ℂ)+
    Complex.I*((nativeTimeSignal (sourceRealSignal p (sourceQuadrature a)) t).first i : ℂ)

private theorem scalar_reconstruct (z : ℂ) : (z.re : ℂ)+Complex.I*((-Complex.I*z).re : ℂ)=z :=by
  have imaginary : (-Complex.I*z).re=z.im :=by simp
  rw [imaginary,mul_comm Complex.I]
  exact Complex.re_add_im z

theorem sourceNativeTimeValue_actual (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) :
    sourceNativeTimeValue p a t=sourceSignalAmplitude p a (nativeTimePoint t) :=by
  ext i
  simp only [sourceNativeTimeValue,sourceTimeSignal_actual,sourceTimeHistory_actual,
    sourceSignalAmplitude,sourcePhase_time,sourceQuadrature]
  have order : Complex.exp ((t : ℂ)*p 0)*(-Complex.I*a i)=
      -Complex.I*(Complex.exp ((t : ℂ)*p 0)*a i) :=by ring
  rw [order]
  exact scalar_reconstruct _

theorem sourceNativeTimeFirst_actual (p : Fin 4→ℂ) (a : SignalAmplitude) (t : ℝ) :
    sourceNativeTimeFirst p a t=p 0 • sourceSignalAmplitude p a (nativeTimePoint t) :=by
  ext i
  simp only [sourceNativeTimeFirst,sourceTimeSignal_actual,sourceTimeHistory_actual,
    sourceSignalAmplitude,sourcePhase_time,sourceQuadrature,Pi.smul_apply,smul_eq_mul]
  have order : Complex.exp ((t : ℂ)*p 0)*(p 0*(-Complex.I*a i))=
      -Complex.I*(Complex.exp ((t : ℂ)*p 0)*(p 0*a i)) :=by ring
  rw [order,scalar_reconstruct]
  ring

theorem sourceNativeBoundary_history (spatial : Fin 3→ℂ) (clock lambda : ℂ) (a : SignalAmplitude) (t : ℝ) :
    sourceNativeBoundary spatial clock lambda a t=
      laplaceWeight lambda t •
        (sourceTemporalSecond*ᵥsourceNativeTimeFirst (fullMomentum spatial clock) a t+
          (sourceTemporalFirst spatial+lambda • sourceTemporalSecond)*ᵥ
            sourceNativeTimeValue (fullMomentum spatial clock) a t) :=by
  rw [sourceNativeTimeFirst_actual,sourceNativeTimeValue_actual]
  have combine (v : SignalAmplitude) : sourceTemporalSecond*ᵥ(clock • v)+
      (sourceTemporalFirst spatial+lambda • sourceTemporalSecond)*ᵥv=
        (sourceTemporalFirst spatial+(clock+lambda) • sourceTemporalSecond)*ᵥv :=by
    rw [Matrix.mulVec_smul,Matrix.add_mulVec,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.smul_mulVec]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  simp only [fullMomentum,Fin.cases_zero]
  rw [combine,←Matrix.mulVec_smul,sourceNativeSignal_weighted,Matrix.mulVec_smul]
  rfl

def sourcePlaneHalfScalar (clock lambda : ℂ) : ℂ:=∫t in Ioi (0 : ℝ),planeWeight clock lambda t

theorem sourcePlaneHalfScalar_actual (clock lambda : ℂ) (off : clock.re<lambda.re) :
    sourcePlaneHalfScalar clock lambda=(lambda-clock)⁻¹ :=by
  have negative : (clock-lambda).re<0 :=by simp only [Complex.sub_re];linarith
  change (∫t in Ioi (0 : ℝ),Complex.exp ((clock-lambda)*(t : ℂ)))=_
  rw [integral_exp_mul_complex_Ioi negative]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  rw [div_eq_mul_inv,←neg_sub clock lambda,inv_neg]
  ring

theorem sourcePlaneWindowScalar_limit (clock lambda : ℂ) (off : clock.re<lambda.re) :
    Tendsto (sourcePlaneWindowScalar clock lambda) atTop (𝓝 ((lambda-clock)⁻¹)) :=by
  have negative : (clock-lambda).re<0 :=by simp only [Complex.sub_re];linarith
  have actual:=intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (integrableOn_exp_mul_complex_Ioi negative 0) tendsto_id
  change Tendsto (fun T : ℝ=>∫t in (0 : ℝ)..T,Complex.exp ((clock-lambda)*(t : ℂ))) atTop (𝓝 ((lambda-clock)⁻¹))
  rw [←sourcePlaneHalfScalar_actual clock lambda off]
  exact actual

end LowEnergy.PreparationVacuumCurrentNativeLaplaceBridge

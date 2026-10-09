import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceNativeRealFourierSignal

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentSignalRealization
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open PreparationVacuumGaugeSourceInjection SourcePropagationNoetherTime
open scoped BigOperators ContDiff Topology Matrix
attribute [local irreducible] nativeHessian nativeJetDensity nativeConfiguration nativeJetBasis

def sourceSignalOperator (p : Fin 4→ℂ) (point : BasePoint) : (Fin 289→ℂ)→L[ℝ] Field289:=
  ContinuousLinearMap.pi (fun i=>Complex.reCLM.comp
    (Complex.exp (sourcePhase p point) • (ContinuousLinearMap.proj i : (Fin 289→ℂ)→L[ℝ] ℂ)))

theorem sourceSignalOperator_actual (p : Fin 4→ℂ) (point : BasePoint) (a : Fin 289→ℂ) :
    sourceSignalOperator p point a=sourceRealSignal p a point :=by
  funext i
  simp only [sourceSignalOperator,ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,
    smul_apply,ContinuousLinearMap.proj_apply,Complex.reCLM_apply,smul_eq_mul,sourceRealSignal]

theorem sourcePhase_time (p : Fin 4→ℂ) (t : ℝ) :
    sourcePhase p (nativeTimePoint t)=(t : ℂ)*p 0 :=by
  rw [nativeTimePoint,map_smul,sourcePhase_coordinate]
  rfl

theorem sourceTimeHistory_actual (p : Fin 4→ℂ) (a : Fin 289→ℂ) (t : ℝ) :
    nativeTimeHistory (sourceRealSignal p a) t=fun i=>(Complex.exp ((t : ℂ)*p 0)*a i).re :=by
  funext i
  simp only [nativeTimeHistory,sourceRealSignal,sourcePhase_time]

private theorem timeHistory_derivative (p : Fin 4→ℂ) (a : Fin 289→ℂ) (t : ℝ) :
    HasDerivAt (nativeTimeHistory (sourceRealSignal p a))
      (nativeTimeHistory (sourceRealSignal p (fun i=>p 0*a i)) t) t :=by
  have derivative (i : Fin 289):=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      ((((Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_id t)).mul_const (p 0)).cexp).mul_const (a i))
  have whole:=hasDerivAt_pi.2 derivative
  convert! whole using 1
  · funext s i
    simp only [sourceTimeHistory_actual,Function.comp_apply,id_eq,Complex.ofRealCLM_apply,Complex.reCLM_apply]
  · funext i
    simp only [sourceTimeHistory_actual,Complex.reCLM_apply,Function.comp_apply,id_eq,
      Complex.ofRealCLM_apply,Complex.ofReal_one,one_mul]
    congr 1
    ring

theorem sourceTimeSignal_actual (p : Fin 4→ℂ) (a : Fin 289→ℂ) (t : ℝ) :
    nativeTimeSignal (sourceRealSignal p a) t=
      ⟨nativeTimeHistory (sourceRealSignal p a) t,
        nativeTimeHistory (sourceRealSignal p (fun i=>p 0*a i)) t,
        nativeTimeHistory (sourceRealSignal p (fun i=>p 0*(p 0*a i))) t⟩ :=by
  have first : deriv (nativeTimeHistory (sourceRealSignal p a))=
      nativeTimeHistory (sourceRealSignal p (fun i=>p 0*a i)) :=by
    funext s
    exact (timeHistory_derivative p a s).deriv
  simp only [nativeTimeSignal,first,(timeHistory_derivative p (fun i=>p 0*a i) t).deriv]

theorem sourceTimeSignal_initial (p : Fin 4→ℂ) (a : Fin 289→ℂ) :
    nativeTimeSignal (sourceRealSignal p a) 0=
      ⟨fun i=>(a i).re,fun i=>(p 0*a i).re,fun i=>(p 0*(p 0*a i)).re⟩ :=by
  rw [sourceTimeSignal_actual]
  simp only [sourceTimeHistory_actual,Complex.ofReal_zero,zero_mul,Complex.exp_zero,one_mul]

def sourceQuadrature (a : Fin 289→ℂ) : Fin 289→ℂ:=fun i=>-Complex.I*a i

theorem sourceSignal_quadrature (p : Fin 4→ℂ) (a : Fin 289→ℂ) (point : BasePoint) :
    sourceRealSignal p (sourceQuadrature a) point=
      fun i=>(sourceSignalAmplitude p a point i).im :=by
  funext i
  unfold sourceRealSignal sourceQuadrature sourceSignalAmplitude
  have order : Complex.exp (sourcePhase p point)*(-Complex.I*a i)=
      -Complex.I*(Complex.exp (sourcePhase p point)*a i) :=by ring
  rw [order]
  simp

/-- Both quadratures are derivatives of actual real native fields; their source matrix is recovered without an extension premise. -/
theorem sourceEuler_quadrature (p : Fin 4→ℂ) (a : Fin 289→ℂ) (point : BasePoint) (i : Fin 289) :
    (nativeEulerLinearJet (signalSecondJet (sourceRealSignal p a) point) i : ℂ)+
      Complex.I*(nativeEulerLinearJet (signalSecondJet (sourceRealSignal p (sourceQuadrature a)) point) i : ℂ)=
        (nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a point) i :=by
  rw [sourceRealSignal_secondJet,sourceRealSignal_secondJet,sourceRealEuler_Fourier,sourceRealEuler_Fourier]
  have amplitude : sourceSignalAmplitude p (sourceQuadrature a) point=
      (-Complex.I) • sourceSignalAmplitude p a point :=by
    funext j
    dsimp only [sourceSignalAmplitude,sourceQuadrature,Pi.smul_apply,smul_eq_mul]
    ring
  rw [amplitude,Matrix.mulVec_smul]
  change (Complex.ofReal _)+Complex.I*Complex.ofReal ((-Complex.I*
    (nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a point) i).re)=_
  have imaginary (z : ℂ) : (-Complex.I*z).re=z.im :=by simp
  rw [imaginary,mul_comm Complex.I]
  exact Complex.re_add_im _

theorem sourceTimeSignal_generated (p : Fin 4→ℂ) (a : Fin 289→ℂ) (t : ℝ) :
    HasSourceJets (nativeTimeSignal (sourceRealSignal p a)) t :=
  nativeTimeSignal_generated _ (sourceRealSignal_smooth p a) t

theorem sourceTimeSignal_continuous (p : Fin 4→ℂ) (a : Fin 289→ℂ) :
    ContinuousJets (nativeTimeSignal (sourceRealSignal p a)) :=
  nativeTimeSignal_continuous _ (sourceRealSignal_smooth p a)

end LowEnergy.PreparationVacuumCurrentSignalRealization

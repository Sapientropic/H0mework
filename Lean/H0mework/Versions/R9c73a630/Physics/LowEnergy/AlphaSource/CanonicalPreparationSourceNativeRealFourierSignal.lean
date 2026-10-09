import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceHalfAxisFieldOperator
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedMotherEulerReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentSignalRealization
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback
open scoped BigOperators ContDiff Topology Matrix
attribute [local irreducible] nativeHessian nativeJetDensity nativeConfiguration nativeJetBasis

def sourcePhase (p : Fin 4→ℂ) : BasePoint→L[ℝ] ℂ:=
  ∑mu : Fin 4,p mu • Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 4=>ℝ) mu)

theorem sourcePhase_apply (p : Fin 4→ℂ) (point : BasePoint) :
    sourcePhase p point=∑mu : Fin 4,p mu*(point mu : ℂ) :=by
  simp only [sourcePhase,sum_apply,smul_apply,ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply,PiLp.proj_apply,smul_eq_mul]

theorem sourcePhase_coordinate (p : Fin 4→ℂ) (mu : Fin 4) :
    sourcePhase p (coordinateDirection mu)=p mu :=by
  rw [sourcePhase_apply]
  simp only [coordinateDirection,PiLp.single_apply]
  simp only [apply_ite,Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- A complex Fourier amplitude is represented by a genuine real field on the original spacetime. -/
def sourceRealSignal (p : Fin 4→ℂ) (a : Fin 289→ℂ) (point : BasePoint) : Field289:=
  fun i=>(Complex.exp (sourcePhase p point)*a i).re

def sourceSignalAmplitude (p : Fin 4→ℂ) (a : Fin 289→ℂ) (point : BasePoint) : Fin 289→ℂ:=
  fun i=>Complex.exp (sourcePhase p point)*a i

theorem sourceRealSignal_smooth (p : Fin 4→ℂ) (a : Fin 289→ℂ) :
    ContDiff ℝ ∞ (sourceRealSignal p a) :=by
  apply contDiff_pi.2
  intro i
  exact Complex.reCLM.contDiff.comp (((sourcePhase p).contDiff.cexp).mul contDiff_const)

private theorem signal_coordinate_derivative (p : Fin 4→ℂ) (a : Fin 289→ℂ)
    (point : BasePoint) (mu : Fin 4) :
    fieldDirectionalDerivative (sourceRealSignal p a) point mu=
      sourceRealSignal p (fun i=>p mu*a i) point :=by
  have derivative (i : Fin 289) :=
    Complex.reCLM.hasFDerivAt.comp point
      (((sourcePhase p).hasFDerivAt.cexp).mul_const (a i))
  have whole:=hasFDerivAt_pi.2 derivative
  change HasFDerivAt (sourceRealSignal p a) _ point at whole
  rw [fieldDirectionalDerivative,whole.fderiv]
  funext i
  simp only [ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,
    smul_apply,Complex.reCLM_apply,sourcePhase_coordinate,
    sourceRealSignal,smul_eq_mul]
  congr 1
  ring

def sourceRealFirstJet (p : Fin 4→ℂ) (v : Fin 289→ℂ) : NativeFirstJet:=
  (fun i=>(v i).re,fun mu i=>(p mu*v i).re)

def sourceRealSecondJet (p : Fin 4→ℂ) (v : Fin 289→ℂ) : NativeSecondJet:=
  (sourceRealFirstJet p v,fun mu=>sourceRealFirstJet p (fun i=>p mu*v i))

theorem sourceRealSignal_firstJet (p : Fin 4→ℂ) (a : Fin 289→ℂ) (point : BasePoint) :
    signalFirstJet (sourceRealSignal p a) point=
      sourceRealFirstJet p (sourceSignalAmplitude p a point) :=by
  apply Prod.ext
  · rfl
  · funext mu i
    change fieldDirectionalDerivative (sourceRealSignal p a) point mu i=_
    rw [signal_coordinate_derivative]
    dsimp only [sourceRealSignal,sourceRealFirstJet,sourceSignalAmplitude]
    congr 1
    ring

theorem sourceRealSignal_secondJet (p : Fin 4→ℂ) (a : Fin 289→ℂ) (point : BasePoint) :
    signalSecondJet (sourceRealSignal p a) point=
      sourceRealSecondJet p (sourceSignalAmplitude p a point) :=by
  apply Prod.ext
  · exact sourceRealSignal_firstJet p a point
  · funext mu
    have germ : signalFirstJet (sourceRealSignal p a)=fun x=>
        (sourceRealSignal p a x,fun nu=>sourceRealSignal p (fun i=>p nu*a i) x) :=by
      funext x
      simp only [signalFirstJet,signal_coordinate_derivative]
    change fieldDirectionalDerivative (signalFirstJet (sourceRealSignal p a)) point mu=_
    rw [germ]
    have first : DifferentiableAt ℝ (sourceRealSignal p a) point:=
      (sourceRealSignal_smooth p a).differentiable (by simp) |>.differentiableAt
    have other (nu : Fin 4) : DifferentiableAt ℝ (sourceRealSignal p (fun i=>p nu*a i)) point:=
      (sourceRealSignal_smooth p (fun i=>p nu*a i)).differentiable (by simp) |>.differentiableAt
    have generated:=first.hasFDerivAt.prodMk (hasFDerivAt_pi.2 (fun nu=> (other nu).hasFDerivAt))
    rw [fieldDirectionalDerivative,generated.fderiv]
    apply Prod.ext
    · change fieldDirectionalDerivative (sourceRealSignal p a) point mu=_
      rw [signal_coordinate_derivative]
      funext i
      dsimp only [sourceRealSignal,sourceRealFirstJet,sourceRealSecondJet,sourceSignalAmplitude]
      congr 1
      ring
    · funext nu i
      change fieldDirectionalDerivative (sourceRealSignal p (fun j=>p nu*a j)) point mu i=_
      rw [signal_coordinate_derivative]
      dsimp only [sourceRealSignal,sourceRealFirstJet,sourceRealSecondJet,sourceSignalAmplitude]
      congr 1
      ring

theorem sourceRealJet_coefficient (p : Fin 4→ℂ) (v : Fin 289→ℂ) (index : NativeJetIndex) :
    nativeJetCoefficient (sourceRealFirstJet p v) index=(jetSymbol index.1 p*v index.2).re :=by
  rcases index with ⟨part,i⟩
  cases part <;> simp only [nativeJetCoefficient,sourceRealFirstJet,jetSymbol,one_mul]

private theorem sourceFourierSum (p : Fin 4→ℂ) (v : Fin 289→ℂ) (i : Fin 289) :
    (nativeFourierHessian nativeHessian p*ᵥv) i=
      ∑left : Option (Fin 4),∑right : NativeJetIndex,
        (nativeHessianCoefficient (left,i) right : ℂ)*jetSymbol left (-p)*
          jetSymbol right.1 p*v right.2 :=by
  unfold nativeFourierHessian Matrix.mulVec dotProduct
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  rfl

theorem sourceRealEuler_Fourier (p : Fin 4→ℂ) (v : Fin 289→ℂ) (i : Fin 289) :
    nativeEulerLinearJet (sourceRealSecondJet p v) i=
      ((nativeFourierHessian nativeHessian p*ᵥv) i).re :=by
  have scalarRead (r : ℝ) (z : ℂ) : ((r : ℂ)*z).re=r*z.re :=by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [nativeEulerLinear_coefficients,sourceFourierSum,Fintype.sum_option]
  simp only [sourceRealSecondJet,sourceRealJet_coefficient,jetSymbol,Pi.neg_apply]
  simp only [Complex.add_re,Complex.re_sum,mul_one,sub_eq_add_neg,←Finset.sum_neg_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro right _
    change (jetSymbol right.1 p*v right.2).re*nativeHessianCoefficient (none,i) right=
      ((nativeHessianCoefficient (none,i) right : ℂ)*jetSymbol right.1 p*v right.2).re
    rw [mul_assoc,scalarRead]
    exact mul_comm _ _
  · apply Finset.sum_congr rfl
    intro mu _
    apply Finset.sum_congr rfl
    intro right _
    change -((jetSymbol right.1 p*(p mu*v right.2)).re*
      nativeHessianCoefficient (some mu,i) right)=
        ((nativeHessianCoefficient (some mu,i) right : ℂ)*(-p mu)*
          jetSymbol right.1 p*v right.2).re
    have algebra : (nativeHessianCoefficient (some mu,i) right : ℂ)*(-p mu)*
        jetSymbol right.1 p*v right.2=
          -((nativeHessianCoefficient (some mu,i) right : ℂ)*
            (jetSymbol right.1 p*(p mu*v right.2))) :=by ring
    rw [algebra,Complex.neg_re,scalarRead]
    ring

theorem sourceRealSignal_originalDensity (p : Fin 4→ℂ) (a : Fin 289→ℂ) (point : BasePoint) :
    nativeDensity (sourceRealSignal p a) point=
      nativeJetDensity (sourceRealFirstJet p (sourceSignalAmplitude p a point)) :=by
  rw [nativeDensity_signalFirstJet _ point
    ((sourceRealSignal_smooth p a).differentiable (by simp) |>.differentiableAt),sourceRealSignal_firstJet]

theorem sourceRealSignal_originalEuler (p : Fin 4→ℂ) (a : Fin 289→ℂ) (point : BasePoint) (i : Fin 289) :
    HasDerivAt (fun r : ℝ=>nativeHolonomicEuler
      (fun x=>r • sourceRealSignal p a x) point i)
      ((nativeFourierHessian nativeHessian p*ᵥsourceSignalAmplitude p a point) i).re 0 :=by
  have source:=nativeHolonomicEuler_source_linear (sourceRealSignal p a) point
    ((sourceRealSignal_smooth p a).contDiffAt.of_le (by
      change ((2 : ℕ∞):ℕ∞ω)≤((⊤:ℕ∞):ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)) i
  rwa [sourceRealSignal_secondJet,sourceRealEuler_Fourier] at source

end LowEnergy.PreparationVacuumCurrentSignalRealization

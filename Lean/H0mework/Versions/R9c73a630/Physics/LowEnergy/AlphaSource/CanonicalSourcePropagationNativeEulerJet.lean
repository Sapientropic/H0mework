import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationOriginalHessianReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationNativeEulerHistory
open SourcePropagationNativeActionHessian
open Filter
open scoped BigOperators Topology ContDiff
attribute [local irreducible] nativeJetDensity nativeHessian nativeJetBasis

abbrev NativeSecondJet := NativeFirstJet × (Fin 4 → NativeFirstJet)

/-- Value derivative minus divergence of the first-jet momentum, from the same mother density. -/
def nativeEulerDensityJet (jet : NativeSecondJet) (field : Fin 289) : ℝ :=
  fderiv ℝ nativeJetDensity jet.1 (nativeJetBasis (none,field)) -
    ∑ mu : Fin 4,
      fderiv ℝ (fun x : NativeFirstJet =>
        fderiv ℝ nativeJetDensity x (nativeJetBasis (some mu,field))) jet.1 (jet.2 mu)

/-- The source-produced first Euler coefficient retains every holonomic derivative leg. -/
def nativeEulerLinearJet (jet : NativeSecondJet) (field : Fin 289) : ℝ :=
  nativeHessian jet.1 (nativeJetBasis (none,field)) -
    ∑ mu : Fin 4, nativeHessian (jet.2 mu) (nativeJetBasis (some mu,field))

theorem nativeDensityMomentum_fderiv (field : Fin 289) (direction : Option (Fin 4)) :
    fderiv ℝ (fun x : NativeFirstJet => fderiv ℝ nativeJetDensity x
      (nativeJetBasis (direction,field))) 0 =
        nativeHessian.flip (nativeJetBasis (direction,field)) := by
  have generated := nativeHessian_generated.clm_apply
    (hasFDerivAt_const (nativeJetBasis (direction,field)) (0 : NativeFirstJet))
  simpa only [ContinuousLinearMap.comp_zero,zero_add] using generated.fderiv

def nativeEulerBackground (field : Fin 289) : ℝ :=
  fderiv ℝ nativeJetDensity 0 (nativeJetBasis (none,field))

theorem nativeEulerLinear_density (jet : NativeSecondJet) (field : Fin 289) :
    nativeEulerLinearJet jet field =
      nativeHessian jet.1 (nativeJetBasis (none,field)) -
        ∑ mu : Fin 4,
          fderiv ℝ (fun x : NativeFirstJet => fderiv ℝ nativeJetDensity x
            (nativeJetBasis (some mu,field))) 0 (jet.2 mu) := by
  simp only [nativeEulerLinearJet,nativeDensityMomentum_fderiv,
    ContinuousLinearMap.flip_apply]

theorem nativeDensityMomentum_smooth (field : Fin 289) (direction : Option (Fin 4)) :
    ContDiffAt ℝ ∞ (fun x : NativeFirstJet => fderiv ℝ nativeJetDensity x
      (nativeJetBasis (direction,field))) 0 :=
  (nativeJetDensity_smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

theorem nativeEulerDensity_zero (field : Fin 289) :
    nativeEulerDensityJet 0 field = nativeEulerBackground field := by
  simp only [nativeEulerDensityJet,nativeEulerBackground,Prod.fst_zero,Prod.snd_zero,
    Pi.zero_apply,map_zero,Finset.sum_const_zero,sub_zero]

theorem nativeEulerDensity_linear (jet : NativeSecondJet) (field : Fin 289) :
    HasDerivAt (fun r : ℝ => nativeEulerDensityJet (r • jet) field)
      (nativeEulerLinearJet jet field) 0 := by
  have line (v : NativeFirstJet) : HasDerivAt (fun r : ℝ => r • v) v 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v
  have first := nativeHessian_generated.comp_hasDerivAt_of_eq 0 (line jet.1) (by simp)
  have value := first.clm_apply (hasDerivAt_const (0 : ℝ) (nativeJetBasis (none,field)))
  have divergence (mu : Fin 4) : HasDerivAt
      (fun r : ℝ => fderiv ℝ (fun x : NativeFirstJet => fderiv ℝ nativeJetDensity x
        (nativeJetBasis (some mu,field))) (r • jet.1) (r • jet.2 mu))
      (nativeHessian (jet.2 mu) (nativeJetBasis (some mu,field))) 0 := by
    have source := ((nativeDensityMomentum_smooth field (some mu)).fderiv_right
      (m := ∞) (by simp)).differentiableAt (by simp) |>.hasFDerivAt
    have differentiated := source.comp_hasDerivAt_of_eq 0 (line jet.1) (by simp)
    have multiplied := differentiated.clm_apply (line (jet.2 mu))
    convert! multiplied using 1
    simp only [Function.comp_apply,zero_smul,map_zero,zero_add,nativeDensityMomentum_fderiv,
      ContinuousLinearMap.flip_apply]
  have all := HasDerivAt.sum (u := Finset.univ) (fun mu _ => divergence mu)
  convert! value.sub all using 1
  simp only [nativeEulerLinearJet,Function.comp_apply,zero_smul,map_zero,add_zero]

theorem nativeHessian_single_coefficients (jet : NativeFirstJet) (index : NativeJetIndex) :
    nativeHessian jet (nativeJetBasis index) = ∑ right : NativeJetIndex,
      nativeJetCoefficient jet right * nativeHessianCoefficient index right := by
  conv_lhs => rw [nativeJet_reconstruction jet]
  simp only [map_sum,map_smul,sum_apply,smul_apply,smul_eq_mul,nativeHessianCoefficient]
  apply Finset.sum_congr rfl
  intro right _
  rw [nativeHessian_symmetric]

theorem nativeEulerLinear_coefficients (jet : NativeSecondJet) (field : Fin 289) :
    nativeEulerLinearJet jet field =
      (∑ right : NativeJetIndex, nativeJetCoefficient jet.1 right *
        nativeHessianCoefficient (none,field) right) -
      ∑ mu : Fin 4, ∑ right : NativeJetIndex, nativeJetCoefficient (jet.2 mu) right *
        nativeHessianCoefficient (some mu,field) right := by
  simp only [nativeEulerLinearJet,nativeHessian_single_coefficients]

end LowEnergy.SourcePropagationNativeEulerHistory

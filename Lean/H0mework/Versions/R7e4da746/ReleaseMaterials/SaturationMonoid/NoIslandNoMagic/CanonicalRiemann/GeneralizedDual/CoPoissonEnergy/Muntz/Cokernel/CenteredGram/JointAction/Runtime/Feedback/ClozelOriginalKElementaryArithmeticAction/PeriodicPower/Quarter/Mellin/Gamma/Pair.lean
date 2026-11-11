import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Moment

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Pair
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalKElementaryArithmeticAction.PeriodicPower.Resolved OriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source
open private resolved_fourier_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Alias.Source
open scoped Topology InnerProductSpace
local notation "F"=>fourierL2

private theorem weighted_integrable (value:BurnolL2):
    Integrable (fun x:ℝ=>value x*burnolGaussianRaw 1 x):=by
  apply (L2.integrable_inner (burnolGaussianL2 1 (by norm_num)) value).congr
  filter_upwards [burnolGaussianL2_coeFn 1 (by norm_num)] with x gaussian
  rw [gaussian,RCLike.inner_apply,starRingEnd_apply,star_burnolGaussianRaw]

private theorem dilation_read (value:BurnolL2) (raw:ℝ→ℂ)
    (read:(value:ℝ→ℂ)=ᵐ[volume]raw) (h:ℝ):
    (burnolMultiplicativeDilation h value:ℝ→ℂ)=ᵐ[volume]
      fun x:ℝ=>(Real.exp (h/2):ℂ)*raw (Real.exp h*x):=by
  have scale:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp h*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp h) (Real.exp_ne_zero h))
  filter_upwards [burnolMultiplicativeDilation_coeFn h value,scale.ae read]
    with x actual moved
  change (burnolMultiplicativeDilation h value) x=
    (Real.exp (h/2):ℂ)*value (Real.exp h*x) at actual
  rw [actual,moved]

private theorem scaled_integrable (value:BurnolL2) (raw:ℝ→ℂ)
    (read:(value:ℝ→ℂ)=ᵐ[volume]raw) (h:ℝ):
    Integrable (fun x:ℝ=>raw (Real.exp h*x)*burnolGaussianRaw 1 x):=by
  have weighted:=weighted_integrable (burnolMultiplicativeDilation h value)
  have actual:Integrable (fun x:ℝ=>(Real.exp (h/2):ℂ)*
      (raw (Real.exp h*x)*burnolGaussianRaw 1 x)):=by
    apply weighted.congr
    filter_upwards [dilation_read value raw read h] with x source
    rw [source]
    ring
  have normalized:=actual.const_mul ((Real.exp (h/2):ℂ)⁻¹)
  apply normalized.congr
  filter_upwards with x
  change (Real.exp (h/2):ℂ)⁻¹*((Real.exp (h/2):ℂ)*
    (raw (Real.exp h*x)*burnolGaussianRaw 1 x))=_
  rw [←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),one_mul]

private theorem even_integral (raw:ℝ→ℂ) (domain:Integrable raw)
    (even:∀x:ℝ,raw (-x)=raw x):
    (∫x:ℝ,raw x)=2*(∫x:ℝ in Ioi 0,raw x):=by
  have negative:(∫x:ℝ in Iic 0,raw x)=∫x:ℝ in Ioi 0,raw x:=by
    calc
      _=∫x:ℝ in Iic 0,raw (-x):=by simp only [even]
      _=_:=by simpa only [neg_zero] using integral_comp_neg_Iic 0 raw
  rw [←intervalIntegral.integral_Iic_add_Ioi (b:=(0:ℝ))
    domain.integrableOn domain.integrableOn,negative]
  ring

def positionReading (c:BurnolCompletedMellinCoordinate) (h x:ℝ):ℂ:=
  Complex.exp ((h:ℂ)*star c.value)*resolvedRaw c (Real.exp h*x)*burnolGaussianRaw 1 x

def fourierReading (c:BurnolCompletedMellinCoordinate) (h x:ℝ):ℂ:=
  Complex.exp ((h:ℂ)*(star c.value-1))*resolvedFourierRaw c (Real.exp (-h)*x)*
    burnolGaussianRaw 1 x

theorem actual_position_integrable (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    IntegrableOn (positionReading c h) (Ioi 0):=by
  have source:=(scaled_integrable (resolvedSource c) (resolvedRaw c) (actual_resolved_raw c) h).const_mul
    (Complex.exp ((h:ℂ)*star c.value))
  apply source.integrableOn.congr
  filter_upwards with x
  exact (mul_assoc _ _ _).symm

theorem actual_fourier_integrable (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    IntegrableOn (fourierReading c h) (Ioi 0):=by
  have source:=(scaled_integrable (F (resolvedSource c)) (resolvedFourierRaw c)
    (actual_resolved_fourier_raw c) (-h)).const_mul (Complex.exp ((h:ℂ)*(star c.value-1)))
  apply source.integrableOn.congr
  filter_upwards with x
  exact (mul_assoc _ _ _).symm

/-- The original L² Fourier action and the self-dual Gaussian generate this pair at every clock. -/
theorem actual_scaled_pair (c:BurnolCompletedMellinCoordinate) (h:ℝ):
    (∫x:ℝ in Ioi 0,positionReading c h x)=
      ∫x:ℝ in Ioi 0,fourierReading c h x:=by
  let pos:ℝ→ℂ:=fun x=>resolvedRaw c (Real.exp h*x)*burnolGaussianRaw 1 x
  let freq:ℝ→ℂ:=fun x=>resolvedFourierRaw c (Real.exp (-h)*x)*burnolGaussianRaw 1 x
  have posDomain:Integrable pos:=
    scaled_integrable (resolvedSource c) (resolvedRaw c) (actual_resolved_raw c) h
  have freqDomain:Integrable freq:=scaled_integrable (F (resolvedSource c))
    (resolvedFourierRaw c) (actual_resolved_fourier_raw c) (-h)
  have posEven:∀x:ℝ,pos (-x)=pos x:=by
    intro x
    simp only [pos,mul_neg,resolvedRaw,abs_neg,burnolGaussianRaw,neg_sq]
  have freqEven:∀x:ℝ,freq (-x)=freq x:=by
    intro x
    simp only [freq,mul_neg,resolved_fourier_even,burnolGaussianRaw,neg_sq]
  have pair:=burnolGaussian_fourierL2_pairing (burnolMultiplicativeDilation h (resolvedSource c))
    (by norm_num : (0:ℝ)<1)
  simp only [burnolGaussianReciprocalScale,Real.one_rpow,Complex.ofReal_one,one_mul,inv_one] at pair
  rw [fourierL2_burnolMultiplicativeDilation] at pair
  have left:(∫x:ℝ,F (burnolMultiplicativeDilation h (resolvedSource c)) x*burnolGaussianRaw 1 x)=
      (Real.exp (-h/2):ℂ)*(∫x:ℝ,freq x):=by
    rw [fourierL2_burnolMultiplicativeDilation,←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [dilation_read (F (resolvedSource c)) (resolvedFourierRaw c)
      (actual_resolved_fourier_raw c) (-h)] with x actual
    rw [actual]
    exact mul_assoc _ _ _
  have right:(∫x:ℝ,(burnolMultiplicativeDilation h (resolvedSource c)) x*burnolGaussianRaw 1 x)=
      (Real.exp (h/2):ℂ)*(∫x:ℝ,pos x):=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [dilation_read (resolvedSource c) (resolvedRaw c) (actual_resolved_raw c) h]
      with x actual
    rw [actual]
    exact mul_assoc _ _ _
  rw [←fourierL2_burnolMultiplicativeDilation,left,right,
    even_integral freq freqDomain freqEven,even_integral pos posDomain posEven] at pair
  have minus:Complex.exp ((h:ℂ)*(star c.value-1/2))*(Real.exp (-h/2):ℂ)=
      Complex.exp ((h:ℂ)*(star c.value-1)):=by
    rw [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    ring
  have plus:Complex.exp ((h:ℂ)*(star c.value-1/2))*(Real.exp (h/2):ℂ)=
      Complex.exp ((h:ℂ)*star c.value):=by
    rw [Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [positionReading,fourierReading,mul_assoc,integral_const_mul]
  have combined:=congrArg (fun z:ℂ=>Complex.exp ((h:ℂ)*(star c.value-1/2))*z/2) pair
  simp only [←mul_assoc,minus,plus] at combined
  have equality:(Complex.exp ((h:ℂ)*star c.value))*(∫x:ℝ in Ioi 0,pos x)=
      Complex.exp ((h:ℂ)*(star c.value-1))*(∫x:ℝ in Ioi 0,freq x):=by
    linear_combination -combined
  exact equality

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.Gamma.Pair
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

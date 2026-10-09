import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileFirstMoment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.GaussianProfileFirstMoment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiCoframeForwardCore ClockPhiConservativeHeatSource ClockPhiHeatCovariancePhase
open SourceClockPhiHeatLocalNativeGaussian SourceClockPhiCorrectedGaussianPair FirstCurrentWholeVariance
open MeasureTheory ProbabilityTheory
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev G(t:ℝ):End:=SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)
private abbrev W(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ):End:=correctedProfileWeight t ht p q x.1 x.2
private abbrev γ:=gaussianReal 0 1
private abbrev γ₂:=γ.prod γ
attribute [local irreducible] sourcePair embed

/-- The output multiplier keeps the literal corrected phase and logarithmic source variance. -/
theorem actual_first_moment_action_point(t:ℝ)(ht:0<t)(axis:Bool)(p q:ℝ)(g:QuantumTest)(z:SourceCoordinateSlice):
    firstMomentAction t ht axis p q g z=
      Complex.ofReal (q*Real.sqrt (heatVariance t z)*
        (if axis then Real.sin (clockPhase (heatLog t z)) else Real.cos (clockPhase (heatLog t z)))*
        (forwardRatio t z)^(p+q*(q-3)/18)) • g z:=by
  change ((q*sourceNoiseSlope t axis z:ℝ):ℂ) • ((((forwardRatio t z)^(p+q*(q-3)/18):ℝ):ℂ) • g z)=_
  rw [actual_source_noise_slope,smul_smul]
  push_cast
  congr 1
  ring
private theorem moment_zero(t:ℝ)(ht:0<t)(axis:Bool)(p:ℝ):firstMomentAction t ht axis p 0=0:=by
  apply LinearMap.ext
  intro g
  apply DFunLike.ext
  intro z
  simp only [actual_first_moment_action_point,zero_mul,Complex.ofReal_zero,zero_smul,LinearMap.zero_apply,zero_apply]
private theorem weight_zero(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f:QuantumTest):W t ht 0 0 x f=f:=by
  apply DFunLike.ext
  intro z
  change (((forwardRatio t z)^0*Real.exp (0*ClockPhiHeatCorrectedCovarianceSource.correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • f z=f z
  simp

/-- This is the exact native-profile/linear-coframe supplier with both original gain legs. -/
theorem actual_gained_single_profile_first_moment(t:ℝ)(ht:0<t)(axis:Bool)(p q:ℝ)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>(noiseCoordinate axis x:ℂ)*sourcePair (G t (W t ht p q x f)) (G t g)) γ₂ ∧
    (∫x:ℝ×ℝ,(noiseCoordinate axis x:ℂ)*sourcePair (G t (W t ht p q x f)) (G t g) ∂γ₂)=
      sourcePair f (firstMomentAction t ht axis (p+1/3) q g):=by
  simpa only [weight_zero,add_zero] using actual_gained_profile_first_moment t ht axis p q 0 0 f g
private theorem constant_first_moment(t:ℝ)(ht:0<t)(axis:Bool)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>(noiseCoordinate axis x:ℂ)*sourcePair (G t f) (G t g)) γ₂ ∧
    (∫x:ℝ×ℝ,(noiseCoordinate axis x:ℂ)*sourcePair (G t f) (G t g) ∂γ₂)=0:=by
  simpa only [weight_zero,moment_zero,LinearMap.zero_apply,sourcePair,map_zero,inner_zero_right] using
    actual_gained_single_profile_first_moment t ht axis 0 0 f g

/-- The deterministic subtraction in the native increment has zero first moment. Both ordered cross terms with the complete two-noise coframe linear row are source-integrable and their exact means retain the original phase/gain factor. -/
theorem actual_profile_increment_linear_noise(t:ℝ)(ht:0<t)(p q:ℝ)(f g h:QuantumTest):
    let a:=fun x:ℝ×ℝ=>G t (W t ht p q x f-f)
    let b:=fun x:ℝ×ℝ=>G t ((x.1:ℂ) • g+(x.2:ℂ) • h)
    let m:=sourcePair f (firstMomentAction t ht false (p+1/3) q g)+
      sourcePair f (firstMomentAction t ht true (p+1/3) q h)
    Integrable (fun x:ℝ×ℝ=>sourcePair (a x) (b x)) γ₂ ∧
    Integrable (fun x:ℝ×ℝ=>sourcePair (b x) (a x)) γ₂ ∧
    (∫x:ℝ×ℝ,sourcePair (a x) (b x) ∂γ₂)=m ∧
    (∫x:ℝ×ℝ,sourcePair (b x) (a x) ∂γ₂)=star m:=by
  dsimp only
  have hξ:=actual_gained_single_profile_first_moment t ht false p q f g
  have hη:=actual_gained_single_profile_first_moment t ht true p q f h
  have h0ξ:=constant_first_moment t ht false f g
  have h0η:=constant_first_moment t ht true f h
  have he(x:ℝ×ℝ):sourcePair (G t (W t ht p q x f-f)) (G t ((x.1:ℂ) • g+(x.2:ℂ) • h))=
      ((noiseCoordinate false x:ℂ)*sourcePair (G t (W t ht p q x f)) (G t g)-
        (noiseCoordinate false x:ℂ)*sourcePair (G t f) (G t g))+
      ((noiseCoordinate true x:ℂ)*sourcePair (G t (W t ht p q x f)) (G t h)-
        (noiseCoordinate true x:ℂ)*sourcePair (G t f) (G t h)):=by
    simp only [map_sub,map_add,map_smul,sourcePair,inner_sub_left,inner_add_right,inner_smul_right,
      noiseCoordinate,Bool.false_eq_true,ite_false,ite_true]
    ring
  have hi:=((hξ.1.sub h0ξ.1).add (hη.1.sub h0η.1)).congr (Filter.Eventually.of_forall (fun x=>(he x).symm))
  have hm:(∫x:ℝ×ℝ,sourcePair (G t (W t ht p q x f-f)) (G t ((x.1:ℂ) • g+(x.2:ℂ) • h)) ∂γ₂)=
      sourcePair f (firstMomentAction t ht false (p+1/3) q g)+sourcePair f (firstMomentAction t ht true (p+1/3) q h):=by
    simp_rw [he]
    erw [integral_add (hξ.1.sub h0ξ.1) (hη.1.sub h0η.1),integral_sub hξ.1 h0ξ.1,integral_sub hη.1 h0η.1,
      hξ.2,hη.2,h0ξ.2,h0η.2,sub_zero,sub_zero]
  have hs(x:ℝ×ℝ):sourcePair (G t ((x.1:ℂ) • g+(x.2:ℂ) • h)) (G t (W t ht p q x f-f))=
      star (sourcePair (G t (W t ht p q x f-f)) (G t ((x.1:ℂ) • g+(x.2:ℂ) • h))):=by
    exact (GaussNativeForm.pair_conjugate _ _).symm
  refine ⟨hi,(Complex.conjCLE.toContinuousLinearMap.integrable_comp hi).congr
    (Filter.Eventually.of_forall (fun x=>(hs x).symm)),hm,?_⟩
  simp_rw [hs]
  have hc:=Complex.conjCLE.toContinuousLinearMap.integral_comp_comm hi
  change (∫x:ℝ×ℝ,star (sourcePair (G t (W t ht p q x f-f)) (G t ((x.1:ℂ) • g+(x.2:ℂ) • h))) ∂γ₂)=
    star (∫x:ℝ×ℝ,sourcePair (G t (W t ht p q x f-f)) (G t ((x.1:ℂ) • g+(x.2:ℂ) • h)) ∂γ₂) at hc
  exact hc.trans (congrArg (fun z:ℂ=>star z) hm)
end LowEnergy.GaussianProfileFirstMoment

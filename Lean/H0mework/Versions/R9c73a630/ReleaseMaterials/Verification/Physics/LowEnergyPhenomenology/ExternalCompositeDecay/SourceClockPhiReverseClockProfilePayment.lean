import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteClockReverseReturn
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileFirstMoment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceScalarDoubleCurrent
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiForwardNativeReturn
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource ClockPhiHeatComparisonWork ClockPhiHeatCovariancePhase
open SourceClockPhiCorrectedGaussianPair SourceClockPhiHeatLocalNativeGaussian GaussianProfileFirstMoment
open MeasureTheory
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev D:End:=combinedGenerator
private abbrev U:End:=inverseVolumeAction
private abbrev M:End:=matchedTester
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev W(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ):End:=correctedProfileWeight t ht p q x.1 x.2
attribute [local irreducible] sourcePair embed matchedTester
private theorem noise_slope(t:ℝ)(ht:0<t)(z:physicalChart):
    covarianceNoise t 1 0 z.val*sourceNoiseSlope t false z.val+
      covarianceNoise t 0 1 z.val*sourceNoiseSlope t true z.val=
        (reciprocalVolume z.val-forwardU t z.val)/3:=by
  let L:=heatLog t z.val
  have hL:0<L:=by
    apply Real.log_pos
    change 1<1+18*t*reciprocalVolume z.val
    have hu:0<reciprocalVolume z.val:=inv_pos.mpr (volume_pos z)
    have hp:0<18*t*reciprocalVolume z.val:=by positivity
    linarith
  let c:=Real.cos (clockPhase L)
  let d:=Real.sin (clockPhase L)
  let k:=heatKappa t z.val
  let e:=2*Real.sqrt L*(reciprocalVolume z.val-forwardU t z.val)*phaseSpeed L
  have htrig:c^2+d^2=1:=by dsimp [c,d];nlinarith [Real.sin_sq_add_cos_sq (clockPhase L)]
  have hk:k*Real.sqrt (L/9)=(reciprocalVolume z.val-forwardU t z.val)/3:=by
    change ((reciprocalVolume z.val-forwardU t z.val)/Real.sqrt L)*Real.sqrt (L/9)=_
    rw [Real.sqrt_div hL.le]
    norm_num
    field_simp [(Real.sqrt_pos.mpr hL).ne']
  rw [actual_source_noise_slope,actual_source_noise_slope]
  change (k*(1*c+0*d)+e*(-1*d+0*c))*(Real.sqrt (L/9)*c)+
    (k*(0*c+1*d)+e*(-0*d+1*c))*(Real.sqrt (L/9)*d)=_
  calc
    _=k*Real.sqrt (L/9)*(c^2+d^2):=by ring
    _=_:=by rw [htrig,mul_one,hk]
private theorem volume_noise_slope(t:ℝ)(ht:0<t)(z:physicalChart):
    3*(volume z.val+18*t)*(covarianceNoise t 1 0 z.val*sourceNoiseSlope t false z.val+
      covarianceNoise t 0 1 z.val*sourceNoiseSlope t true z.val)=18*t*reciprocalVolume z.val:=by
  rw [noise_slope t ht z]
  unfold reciprocalVolume forwardU
  have hV:volume z.val+18*t≠0:=ne_of_gt (by linarith [volume_pos z])
  field_simp [(volume_pos z).ne',hV]
  ring
private theorem moment_operator(t:ℝ)(ht:0<t)(p q:ℝ):
    (3:ℂ) • (noiseAction t ht 1 0*advancedVolume t*firstMomentAction t ht false p q)+
      (3:ℂ) • (noiseAction t ht 0 1*advancedVolume t*firstMomentAction t ht true p q)=
        (18*t*q:ℂ) • (U*gaussianProfileWeight t ht (p+q*(q-3)/18)):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · let v:=gaussianProfileWeight t ht (p+q*(q-3)/18) f z
    change (3:ℂ) • ((covarianceNoise t 1 0 z:ℂ) •
      ((volume z:ℂ) • ((q*sourceNoiseSlope t false z:ℝ):ℂ) • v+
        (18*t:ℂ) • ((q*sourceNoiseSlope t false z:ℝ):ℂ) • v))+
      (3:ℂ) • ((covarianceNoise t 0 1 z:ℂ) •
      ((volume z:ℂ) • ((q*sourceNoiseSlope t true z:ℝ):ℂ) • v+
        (18*t:ℂ) • ((q*sourceNoiseSlope t true z:ℝ):ℂ) • v))=
        (18*t*q:ℂ) • ((reciprocalVolume z:ℂ) • v)
    simp only [smul_smul,←add_smul]
    have h:=congrArg (fun a:ℝ=>(a:ℂ)) (volume_noise_slope t ht ⟨z,hz⟩)
    push_cast at h ⊢
    congr 1
    linear_combination q*h
  · have hzero(g:QuantumTest):g z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (g.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=(starRingEnd ℂ) c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_left]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem row_moment_pair(t:ℝ)(ht:0<t)(p q:ℝ)(f g:QuantumTest):
    sourcePair (reverseClockRow t ht false f) (firstMomentAction t ht false p q g)+
      sourcePair (reverseClockRow t ht true f) (firstMomentAction t ht true p q g)=
        (18*t*q:ℂ)*sourcePair (D f) (U (gaussianProfileWeight t ht (p+q*(q-3)/18) g)):=by
  have hV(f g:QuantumTest):sourcePair (advancedVolume t f) g=sourcePair f (advancedVolume t g):=by
    change sourcePair (volumeAction f+(18*t:ℂ) • f) g=sourcePair f (volumeAction g+(18*t:ℂ) • g)
    simp only [pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,map_mul,Complex.conj_ofReal,Complex.conj_ofNat]
    change sourcePair (volumeAction f) g+(18*t:ℂ)*sourcePair f g=
      sourcePair f (volumeAction g)+(18*t:ℂ)*sourcePair f g
    have hv:=multiply_pair volume (fun z:physicalChart=>volume_smooth.contDiffAt) f g
    change sourcePair f (volumeAction g)=sourcePair (volumeAction f) g at hv
    rw [hv]
  have hn(ξ η:ℝ)(f g:QuantumTest):sourcePair (noiseAction t ht ξ η f) g=
      sourcePair f (noiseAction t ht ξ η g):=(multiply_pair _ _ _ _).symm
  have he:=LinearMap.congr_fun (moment_operator t ht p q) g
  change sourcePair ((3:ℂ) • advancedVolume t (noiseAction t ht 1 0 (D f))) (firstMomentAction t ht false p q g)+
    sourcePair ((3:ℂ) • advancedVolume t (noiseAction t ht 0 1 (D f))) (firstMomentAction t ht true p q g)=_
  simp only [pair_smul_l,Complex.conj_ofNat]
  change (3:ℂ)*sourcePair (advancedVolume t (noiseAction t ht 1 0 (D f))) (firstMomentAction t ht false p q g)+
    (3:ℂ)*sourcePair (advancedVolume t (noiseAction t ht 0 1 (D f))) (firstMomentAction t ht true p q g)=_
  rw [hV,hV,hn,hn]
  have h:=congrArg (sourcePair (D f)) he
  simpa only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,sourcePair,map_add,map_smul,
    inner_add_right,inner_smul_right] using h

/-- The two covariance noises cancel their phase cross term against the original profile moment. The full weighted clock current is paid by a literal factor t, with its original M and D words retained. -/
theorem actual_reverse_clock_profile_payment(t:ℝ)(ht:0<t)(p q:ℝ)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (reverseClockReturn t ht x.1 x.2 f) (W t ht p q x g)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (reverseClockReturn t ht x.1 x.2 f) (W t ht p q x g) ∂γ.prod γ)=
      (-54*t:ℂ)*sourcePair (M f) (gaussianProfileWeight t ht (p+q*(q-3)/18) g)+
        (18*t*q:ℂ)*sourcePair (D f) (U (gaussianProfileWeight t ht (p+q*(q-3)/18) g)):=by
  have h0:=(actual_corrected_gaussian_weighted_source_pair t ht p q (M f) g)
  have h1:=actual_profile_first_moment t ht false p q (reverseClockRow t ht false f) g
  have h2:=actual_profile_first_moment t ht true p q (reverseClockRow t ht true f) g
  have he(x:ℝ×ℝ):sourcePair (reverseClockReturn t ht x.1 x.2 f) (W t ht p q x g)=
    (-54*t:ℂ)*sourcePair (M f) (W t ht p q x g)+
      (x.1:ℂ)*sourcePair (reverseClockRow t ht false f) (W t ht p q x g)+
      (x.2:ℂ)*sourcePair (reverseClockRow t ht true f) (W t ht p q x g):=by
    simp only [reverseClockReturn,LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,
      inner_add_left,inner_smul_left,map_mul,map_neg,Complex.conj_ofNat,Complex.conj_ofReal]
  change Integrable (fun x:ℝ×ℝ=>(x.1:ℂ)*sourcePair (reverseClockRow t ht false f) (W t ht p q x g)) (γ.prod γ) ∧ _ at h1
  change Integrable (fun x:ℝ×ℝ=>(x.2:ℂ)*sourcePair (reverseClockRow t ht true f) (W t ht p q x g)) (γ.prod γ) ∧ _ at h2
  simp_rw [he]
  refine ⟨((h0.1.const_mul _).add h1.1).add h2.1,?_⟩
  erw [integral_add ((h0.1.const_mul (-54*t:ℂ)).add h1.1) h2.1]
  erw [integral_add (h0.1.const_mul (-54*t:ℂ)) h1.1]
  erw [integral_const_mul,h0.2,h1.2,h2.2]
  rw [add_assoc,row_moment_pair]
end LowEnergy.ReverseNativeClock

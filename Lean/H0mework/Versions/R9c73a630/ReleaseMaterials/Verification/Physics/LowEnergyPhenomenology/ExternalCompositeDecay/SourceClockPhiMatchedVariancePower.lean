import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompletedNormalizerGaussian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalGaussianH0FirstJet
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRMatchedVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure
open SourceClockPhiCoframeForwardCore SourceClockPhiForwardNativeReturn SourceClockPhiActualCovarianceStep
open SourceClockPhiHeatLocalNativeGaussian ClockPhiHeatCorrectedCovarianceSource
open SourceClockPhiOriginalGaussianH0FirstJet OriginalRCommutatorSource MeasureTheory Filter
open scoped Topology InnerProductSpace ContDiff
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev G(s:ℝ):End:=sourceGain (Real.sqrt s)
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ₂:=γ.prod γ
attribute [local irreducible] sourcePair embed combinedGenerator
private theorem gain_square(s:ℝ)(hs:0<s)(z:physicalChart):
    gainProfile (Real.sqrt s) z.val^2=forwardRatio s z.val^(1/3:ℝ):=by
  have hr:=forward_ratio_pos s hs.le z
  unfold gainProfile
  rw [Real.sq_sqrt hs.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
  congr 1
  norm_num

private theorem noise_power_source(s:ℝ)(hs:0<s):
    noiseAction s hs 1 0*(G s*G s)*noiseAction s hs 1 0+
      noiseAction s hs 0 1*(G s*G s)*noiseAction s hs 0 1=
      (1/2:ℂ) • (U*(gaussianProfileWeight s hs (1/3)-gaussianProfileWeight s hs (-5/3))*U):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (covarianceNoise s 1 0 z:ℂ) • ((gainProfile (Real.sqrt s) z:ℂ) •
    ((gainProfile (Real.sqrt s) z:ℂ) • ((covarianceNoise s 1 0 z:ℂ) • f z)))+
    (covarianceNoise s 0 1 z:ℂ) • ((gainProfile (Real.sqrt s) z:ℂ) •
      ((gainProfile (Real.sqrt s) z:ℂ) • ((covarianceNoise s 0 1 z:ℂ) • f z)))=
    (1/2:ℂ) • ((reciprocalVolume z:ℂ) •
      (((forwardRatio s z^(1/3:ℝ):ℝ):ℂ) • ((reciprocalVolume z:ℂ) • f z)-
        ((forwardRatio s z^(-5/3:ℝ):ℝ):ℂ) • ((reciprocalVolume z:ℂ) • f z)))
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos s hs.le ⟨z,hz⟩
    have hv:=volume_pos ⟨z,hz⟩
    have hu:forwardU s z=reciprocalVolume z/forwardRatio s z:=by
      unfold forwardU reciprocalVolume forwardRatio
      field_simp [hv.ne']
    have hp:forwardRatio s z^(1/3:ℝ)/(forwardRatio s z)^2=forwardRatio s z^(-5/3:ℝ):=by
      rw [←Real.rpow_natCast,←Real.rpow_sub hr]
      congr 1
      norm_num
    have hn:=actual_covariance_noise_square s hs ⟨z,hz⟩
    have hg:=gain_square s hs ⟨z,hz⟩
    have he:(covarianceNoise s 1 0 z^2+covarianceNoise s 0 1 z^2)*gainProfile (Real.sqrt s) z^2=
        (1/2)*reciprocalVolume z*((forwardRatio s z^(1/3:ℝ)-forwardRatio s z^(-5/3:ℝ))*reciprocalVolume z):=by
      rw [hn,hg,hu,←hp]
      field_simp [hr.ne']
    have hh:=congrArg (fun r:ℝ=>(r:ℂ) • f z) he
    push_cast at hh
    simp only [smul_smul,smul_sub] at hh ⊢
    linear_combination (norm:=module) hh
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [hf,smul_zero,zero_add,sub_zero]


private theorem gain_noise_pair(s:ℝ)(hs:0<s)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (G s (noiseAction s hs ξ η f)) (G s (noiseAction s hs ξ η g))=
      sourcePair f ((noiseAction s hs ξ η*(G s*G s)*noiseAction s hs ξ η) g):=by
  have hG:sourcePair (G s (noiseAction s hs ξ η f)) (G s (noiseAction s hs ξ η g))=
      sourcePair (noiseAction s hs ξ η f) (G s (G s (noiseAction s hs ξ η g))):=(multiply_pair _ _ _ _).symm
  rw [hG]
  exact (multiply_pair _ _ _ _).symm
private theorem pair_neg(f g:QuantumTest):sourcePair (-f) (-g)=sourcePair f g:=by
  simp only [sourcePair,map_neg,inner_neg_left,inner_neg_right,neg_neg]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]

/-- The full matched-clock variance is exactly two original source powers. The original phase cancels through its generated covariance identity, without selecting a new Gaussian law. -/
theorem actual_matched_variance_finite_power(s:ℝ)(hs:0<s)(f g:QuantumTest):
    matchedDefectMean s hs f g=(1/2:ℂ)*(sourcePair (U (D f)) (gaussianProfileWeight s hs (1/3) (U (D g)))-
      sourcePair (U (D f)) (gaussianProfileWeight s hs (-5/3) (U (D g)))):=by
  simp only [matchedDefectMean,matchedNoiseRow,Bool.false_eq_true,ite_false,ite_true,map_neg,pair_neg,gain_noise_pair]
  rw [←pair_add_r,←LinearMap.add_apply,noise_power_source]
  simp only [LinearMap.smul_apply,Module.End.mul_apply,pair_smul_r,LinearMap.sub_apply,map_sub,pair_sub_r]
  have h1:sourcePair (D f) (U (gaussianProfileWeight s hs (1/3) (U (D g))))=
      sourcePair (U (D f)) (gaussianProfileWeight s hs (1/3) (U (D g))):=multiply_pair _ _ _ _
  have h2:sourcePair (D f) (U (gaussianProfileWeight s hs (-5/3) (U (D g))))=
      sourcePair (U (D f)) (gaussianProfileWeight s hs (-5/3) (U (D g))):=multiply_pair _ _ _ _
  rw [h1,h2]

/-- The negative matched variance in the original completed-square price has an endogenous first jet: its full covariance is 18 times the original U-cubed D Gram. -/
theorem actual_matched_variance_first_jet(f g:QuantumTest):
    Tendsto (fun s:ℝ=>if hs:0<s then (s:ℂ)⁻¹*matchedDefectMean s hs f g else 0)
      (𝓝[>] (0:ℝ)) (𝓝 ((18:ℂ)*sourcePair (U (D f)) (U (U (D g))))):=by
  have h1:=actual_gaussian_weighted_source_pair_first_jet (1/3) (U (D f)) (U (D g))
  have h2:=actual_gaussian_weighted_source_pair_first_jet (-5/3) (U (D f)) (U (D g))
  have h:=((h1.sub h2).const_mul (1/2:ℂ))
  have he:(1/2:ℂ)*((18:ℂ)*((1/3:ℝ):ℂ)*sourcePair (U (D f)) (U (U (D g)))-
      (18:ℂ)*((-5/3:ℝ):ℂ)*sourcePair (U (D f)) (U (U (D g))))=(18:ℂ)*sourcePair (U (D f)) (U (U (D g))):=by
    push_cast
    ring
  rw [he] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs':0<s:=hs
  simp only [dif_pos hs',actual_matched_variance_finite_power]
  ring

private abbrev radialHalf(s:ℝ)(hs:0<s):End:=gaussianProfileWeight s hs (-5/6)
private theorem radial_power_split(s:ℝ)(hs:0<s):
    gaussianProfileWeight s hs (1/3)-gaussianProfileWeight s hs (-5/3)=
      (36*s:ℂ) • (inverseRootAction*(radialHalf s hs*radialHalf s hs)*inverseRootAction)+
      (324*s^2:ℂ) • (U*(radialHalf s hs*radialHalf s hs)*U):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((forwardRatio s z^(1/3:ℝ):ℝ):ℂ) • f z-((forwardRatio s z^(-5/3:ℝ):ℝ):ℂ) • f z=
    (36*s:ℂ) • ((inverseRootVolume z:ℂ) • (((forwardRatio s z^(-5/6:ℝ):ℝ):ℂ) •
      (((forwardRatio s z^(-5/6:ℝ):ℝ):ℂ) • ((inverseRootVolume z:ℂ) • f z))))+
    (324*s^2:ℂ) • ((reciprocalVolume z:ℂ) • (((forwardRatio s z^(-5/6:ℝ):ℝ):ℂ) •
      (((forwardRatio s z^(-5/6:ℝ):ℝ):ℂ) • ((reciprocalVolume z:ℂ) • f z))))
  by_cases hz:z∈physicalChart
  · have hr:=forward_ratio_pos s hs.le ⟨z,hz⟩
    have hp:forwardRatio s z^(-5/6:ℝ)*forwardRatio s z^(-5/6:ℝ)=forwardRatio s z^(-5/3:ℝ):=by
      rw [←Real.rpow_add hr]
      congr 1
      norm_num
    have hp':forwardRatio s z^(1/3:ℝ)=forwardRatio s z^(-5/3:ℝ)*forwardRatio s z^2:=by
      rw [←Real.rpow_natCast,←Real.rpow_add hr]
      congr 1
      norm_num
    have hroot:inverseRootVolume z*inverseRootVolume z=reciprocalVolume z:=by
      unfold inverseRootVolume reciprocalVolume
      rw [←mul_inv,Real.mul_self_sqrt (volume_pos ⟨z,hz⟩).le]
    have hR:forwardRatio s z=1+18*s*reciprocalVolume z:=by
      unfold forwardRatio reciprocalVolume
      field_simp [(volume_pos ⟨z,hz⟩).ne']
    have he:forwardRatio s z^(1/3:ℝ)-forwardRatio s z^(-5/3:ℝ)=
        36*s*(inverseRootVolume z*(forwardRatio s z^(-5/6:ℝ)*forwardRatio s z^(-5/6:ℝ))*inverseRootVolume z)+
        324*s^2*(reciprocalVolume z*(forwardRatio s z^(-5/6:ℝ)*forwardRatio s z^(-5/6:ℝ))*reciprocalVolume z):=by
      rw [hp,hp']
      calc
        _=forwardRatio s z^(-5/3:ℝ)*((1+18*s*reciprocalVolume z)^2-1):=by rw [hR];ring
        _=_:=by linear_combination (norm:=ring) -(36*s*forwardRatio s z^(-5/3:ℝ))*hroot
    have hh:=congrArg (fun r:ℝ=>(r:ℂ) • f z) he
    push_cast at hh
    simp only [smul_smul] at hh ⊢
    linear_combination (norm:=module) hh
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [hf,smul_zero,sub_zero,zero_add]
private theorem radial_sandwich_pair(s:ℝ)(hs:0<s)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f g:QuantumTest):
    sourcePair f ((multiply c hc*(radialHalf s hs*radialHalf s hs)*multiply c hc) g)=
      sourcePair (radialHalf s hs (multiply c hc f)) (radialHalf s hs (multiply c hc g)):=by
  change sourcePair f (multiply c hc (radialHalf s hs (radialHalf s hs (multiply c hc g))))=_
  rw [multiply_pair]
  exact multiply_pair _ _ _ _

/-- The actual variance is a sum of two generated radial squares at every positive clock time. -/
theorem actual_matched_variance_radial_squares(s:ℝ)(hs:0<s)(f g:QuantumTest):
    matchedDefectMean s hs f g=(18*s:ℂ)*sourcePair
      (radialHalf s hs (inverseRootAction (U (D f)))) (radialHalf s hs (inverseRootAction (U (D g))))+
      (162*s^2:ℂ)*sourcePair (radialHalf s hs (U (U (D f)))) (radialHalf s hs (U (U (D g)))):=by
  rw [actual_matched_variance_finite_power,←pair_sub_r,←LinearMap.sub_apply,radial_power_split]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_r,pair_smul_r]
  have h1:sourcePair (U (D f)) ((inverseRootAction*(radialHalf s hs*radialHalf s hs)*inverseRootAction) (U (D g)))=
      sourcePair (radialHalf s hs (inverseRootAction (U (D f)))) (radialHalf s hs (inverseRootAction (U (D g)))):=
    radial_sandwich_pair s hs inverseRootVolume inverse_root_volume_smooth (U (D f)) (U (D g))
  have h2:sourcePair (U (D f)) ((U*(radialHalf s hs*radialHalf s hs)*U) (U (D g)))=
      sourcePair (radialHalf s hs (U (U (D f)))) (radialHalf s hs (U (U (D g)))):=
    radial_sandwich_pair s hs reciprocalVolume reciprocal_volume_smooth (U (D f)) (U (D g))
  refine (congrArg₂ (fun x y:ℂ=>(1/2:ℂ)*((36*s:ℂ)*x+(324*s^2:ℂ)*y)) h1 h2).trans ?_
  ring
end LowEnergy.OriginalRMatchedVariance

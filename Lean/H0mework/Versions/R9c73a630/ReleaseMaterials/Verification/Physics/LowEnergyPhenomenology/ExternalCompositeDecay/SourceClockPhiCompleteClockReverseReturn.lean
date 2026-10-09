import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteClockHomogeneity
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedWeightTransport
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaussianPlaneSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceScalarDoubleCurrent
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiCorrectedWeightTransport
open SourceClockPhiForwardNativeReturn SourceClockPhiActualCovarianceStep SourceClockPhiGaussianPlaneSource
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource MeasureTheory
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev D:End:=combinedGenerator
private abbrev U:End:=inverseVolumeAction
private abbrev V:End:=volumeAction
private abbrev M:End:=matchedTester
private abbrev Dc:End:=dilation
private abbrev Z:End:=reverseNativeClock
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] sourcePair embed correctedCompleteCore matchedTester reverseNativeClock

def advancedVolume(t:ℝ):End:=V+(18*t:ℂ) • (1:End)
def reverseClockRow(t:ℝ)(ht:0<t)(axis:Bool):End:=
  (3:ℂ) • (advancedVolume t*noiseAction t ht (if axis then 0 else 1) (if axis then 1 else 0)*D)
def reverseClockReturn(t:ℝ)(ht:0<t)(ξ η:ℝ):End:=
  (-54*t:ℂ) • M+(ξ:ℂ) • reverseClockRow t ht false+(η:ℂ) • reverseClockRow t ht true

private theorem inverse_dilation:Dc*U-U*Dc=(2*Complex.I) • U:=by
  have h:=congrArg (fun A:End=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=(1:ℂ):=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring
private theorem volume_inverse_end:V*U=(1:End):=LinearMap.ext volume_inverse
private theorem reverse_matched:Z=(6:ℂ) • D-(3:ℂ) • (V*M)-(12:ℂ) • (1:End):=by
  have h:Dc*U=U*Dc+(2*Complex.I) • U:=by
    linear_combination (norm:=module) inverse_dilation
  have h6:(3*Complex.I)*(2*Complex.I)=(-6:ℂ):=by
    calc _=6*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  unfold M matchedTester matchedColumn Z reverseNativeClock
  rw [h]
  simp only [mul_add,mul_smul_comm,smul_add,smul_smul,h6,←mul_assoc,volume_inverse_end,one_mul]
  module
private theorem forward_inverse(t:ℝ)(ht:0<t):
    forwardUAction t ht.le*advancedVolume t=(1:End):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (forwardU t z:ℂ) • ((volume z:ℂ) • f z+(18*t:ℂ) • f z)=f z
  by_cases hz:z∈physicalChart
  · have hv:volume z+18*t≠0:=ne_of_gt (by linarith [volume_pos ⟨z,hz⟩])
    rw [←add_smul,smul_smul]
    have hr:forwardU t z*(volume z+18*t)=1:=inv_mul_cancel₀ hv
    have hc:=congrArg (fun r:ℝ=>(r:ℂ)) hr
    norm_num only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_ofNat,Complex.ofReal_one] at hc
    rw [hc,one_smul]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [hf,smul_zero,add_zero]
private theorem complete_volume(t:ℝ)(ht:0<t)(ξ η:ℝ):
    V*correctedCompleteCore t ht ξ η=correctedCompleteCore t ht ξ η*advancedVolume t:=by
  have h:=actual_corrected_complete_inverse_volume t ht ξ η
  change U*correctedCompleteCore t ht ξ η=correctedCompleteCore t ht ξ η*forwardUAction t ht.le at h
  have he:=congrArg (fun A:End=>V*A*advancedVolume t) h
  simp only [←mul_assoc,volume_inverse_end,one_mul] at he
  simpa only [mul_assoc,forward_inverse t ht,mul_one] using he.symm
private theorem noise_affine(t:ℝ)(ht:0<t)(ξ η:ℝ):
    noiseAction t ht ξ η=(ξ:ℂ) • noiseAction t ht 1 0+(η:ℂ) • noiseAction t ht 0 1:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (covarianceNoise t ξ η z:ℂ) • f z=
    (ξ:ℂ) • ((covarianceNoise t 1 0 z:ℂ) • f z)+(η:ℂ) • ((covarianceNoise t 0 1 z:ℂ) • f z)
  rw [actual_covariance_noise_affine]
  simp only [Complex.ofReal_add,Complex.ofReal_mul,add_smul,mul_smul]
private theorem returned_word(t:ℝ)(ht:0<t)(ξ η:ℝ):
    reverseClockReturn t ht ξ η=(-54*t:ℂ) • M+
      (3:ℂ) • (advancedVolume t*noiseAction t ht ξ η*D):=by
  rw [noise_affine]
  simp only [reverseClockReturn,reverseClockRow,Bool.false_eq_true,if_false,if_true,
    mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_add,smul_smul]
  module

/-- The exact reverse-clock commutator returns to three original input rows. Its volume shift, matched drift and both rotated covariance noises are generated by the same complete clock. -/
theorem actual_complete_reverse_clock_return(t:ℝ)(ht:0<t)(ξ η:ℝ):
    bracket Z (correctedCompleteCore t ht ξ η)=
      correctedCompleteCore t ht ξ η*reverseClockReturn t ht ξ η:=by
  let C:End:=correctedCompleteCore t ht ξ η
  have hd:D*C=C*D:=(actual_corrected_complete_generator_commute t ht ξ η).eq
  have hv:V*C=C*advancedVolume t:=complete_volume t ht ξ η
  have hm:M*C=C*(M-noiseAction t ht ξ η*D):=by
    apply LinearMap.ext;intro f
    exact actual_corrected_complete_matched_tester t ht ξ η f
  have hleft:Z*C=C*((6:ℂ) • D-(3:ℂ) • (advancedVolume t*(M-noiseAction t ht ξ η*D))-(12:ℂ) • (1:End)):=by
    rw [reverse_matched]
    apply LinearMap.ext;intro f
    change (6:ℂ) • D (C f)-(3:ℂ) • V (M (C f))-(12:ℂ) • C f=
      C ((6:ℂ) • D f-(3:ℂ) • advancedVolume t (M f-noiseAction t ht ξ η (D f))-(12:ℂ) • f)
    have hd':D (C f)=C (D f):=LinearMap.congr_fun hd f
    have hm':M (C f)=C (M f-noiseAction t ht ξ η (D f)):=LinearMap.congr_fun hm f
    have hv':V (C (M f-noiseAction t ht ξ η (D f)))=
        C (advancedVolume t (M f-noiseAction t ht ξ η (D f))):=
      LinearMap.congr_fun hv (M f-noiseAction t ht ξ η (D f))
    rw [hd',hm',hv']
    simp only [map_sub,map_smul]
  rw [returned_word]
  change Z*C-C*Z=C*((-54*t:ℂ) • M+(3:ℂ) • (advancedVolume t*noiseAction t ht ξ η*D))
  rw [hleft,reverse_matched]
  unfold advancedVolume
  simp only [mul_sub,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,one_mul,mul_one,smul_add,smul_sub,smul_smul]
  module

private theorem complete_pair(t:ℝ)(ht:0<t)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore t ht ξ η f) (correctedCompleteCore t ht ξ η g)=
      sourcePair (sourceGain (Real.sqrt t) f) (sourceGain (Real.sqrt t) g):=by
  unfold correctedCompleteCore correctedHeatCore
  change sourcePair (SourceClockPhiCoframeForwardCore.sourceForwardCore t ht.le
    (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) f)))
    (SourceClockPhiCoframeForwardCore.sourceForwardCore t ht.le
    (correctedProfileCore t ht ξ η (sourceGain (Real.sqrt t) g)))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _

/-- Gaussian centering consumes both actual noise rows; no norm or moment budget is supplied. -/
theorem actual_complete_reverse_clock_mean(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (bracket Z (correctedCompleteCore t ht x.1 x.2) g)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (bracket Z (correctedCompleteCore t ht x.1 x.2) g) ∂γ.prod γ)=
      (-54*t:ℂ)*sourcePair (sourceGain (Real.sqrt t) f) (sourceGain (Real.sqrt t) (M g)):=by
  let G:=sourceGain (Real.sqrt t)
  have h:=actual_gaussian_affine_source_pair (G f) 0 0 (G ((-54*t:ℂ) • M g))
    (G (reverseClockRow t ht false g)) (G (reverseClockRow t ht true g)) (1:End)
  have he(x:ℝ×ℝ):sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (bracket Z (correctedCompleteCore t ht x.1 x.2) g)=
    sourcePair (G f) (G ((-54*t:ℂ) • M g)+(x.1:ℂ) • G (reverseClockRow t ht false g)+
      (x.2:ℂ) • G (reverseClockRow t ht true g)):=by
    rw [actual_complete_reverse_clock_return]
    change sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (correctedCompleteCore t ht x.1 x.2 (reverseClockReturn t ht x.1 x.2 g))=_
    rw [complete_pair]
    dsimp only [G]
    simp only [reverseClockReturn,LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]
  simp only [smul_zero,add_zero,Module.End.one_apply,sourcePair,map_zero,inner_zero_left,
    map_smul,inner_smul_right] at h
  simpa only [he,sourcePair,map_smul,G] using h
end LowEnergy.ReverseNativeClock

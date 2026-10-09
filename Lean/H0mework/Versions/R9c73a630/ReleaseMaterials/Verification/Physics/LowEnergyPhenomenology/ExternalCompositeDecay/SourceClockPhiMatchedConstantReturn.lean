import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiNativeComplementGaussian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NativePointReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiCoframeForwardCore ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource
open SourceClockPhiCorrectedWeightTransport SourceClockPhiProfileCoframeRemainingWork
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceClockPhiForwardNativeReturn
open SourceClockReflectedForm SourceCoframeCovariantSquare GaussCoframeForm
open MeasureTheory
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] sourcePair embed

private theorem coeff_first(s ξ η:ℝ)(x y:SourceCoordinateSlice)(h:x.1=y.1):
    correctedCoefficient s ξ η x=correctedCoefficient s ξ η y:=by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  dsimp at h
  subst y₁
  rfl

private theorem complete_pair(s:ℝ)(hs:0<s)(ξ η:ℝ)(f g:QuantumTest):
    sourcePair (correctedCompleteCore s hs ξ η f) (correctedCompleteCore s hs ξ η g)=
      sourcePair (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) f)
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) g):=by
  change sourcePair (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) f)))
    (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) g)))=_
  rw [SourceClockPhiCoframeForwardPair.actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _

private theorem current_return(s:ℝ)(hs:0<s)(ξ η:ℝ)(a:Fin 7)(f:QuantumTest):
    GaussCoframeSpin.current a (correctedCompleteCore s hs ξ η f)=
      correctedCompleteCore s hs ξ η (GaussCoframeSpin.current a f):=by
  have h:=LinearMap.congr_fun (actual_profile_complete_current_commute s hs
    (correctedCoefficient s ξ η) (coefficient_smooth s hs ξ η) (coeff_first s ξ η) a).eq f
  exact h.symm

private theorem number_forward(s:ℝ)(hs : 0 ≤ s)(f:QuantumTest):
    number (sourceForwardCore s hs f)=sourceForwardCore s hs (number f):=by
  apply DFunLike.ext
  intro z
  by_cases hz:18*s<volume z
  · apply PiLp.ext
    intro word
    rw [number_apply]
    change (word.card:ℂ)*forwardValue s f z word=forwardValue s (number f) z word
    simp only [forwardValue,if_pos hz,number_apply]
    ring
  · change number (sourceForwardCore s hs f) z=forwardValue s (number f) z
    have hzero:sourceForwardCore s hs f z=0:=by
      change forwardValue s f z=0
      simp only [forwardValue,if_neg hz]
    change GaussQuantumMultiplier.quantized _ (sourceForwardCore s hs f z)=_
    rw [hzero,map_zero]
    simp only [forwardValue,if_neg hz]

private theorem number_profile(s:ℝ)(hs:0<s)(ξ η:ℝ)(f:QuantumTest):
    number (correctedProfileCore s hs ξ η f)=correctedProfileCore s hs ξ η (number f):=by
  apply DFunLike.ext
  intro z
  change GaussQuantumMultiplier.quantized _
    ((Real.exp ((25/2:ℝ)*(1*correctedCoefficient s ξ η z)):ℂ) •
      f (ClockPhiMatchedNoiseCore.combinedMap (1*correctedCoefficient s ξ η z) z))=
    (Real.exp ((25/2:ℝ)*(1*correctedCoefficient s ξ η z)):ℂ) •
      GaussQuantumMultiplier.quantized _
        (f (ClockPhiMatchedNoiseCore.combinedMap (1*correctedCoefficient s ξ η z) z))
  exact map_smul _ _ _

private theorem number_gain(s:ℝ)(f:QuantumTest):
    number (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) f)=
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (number f):=by
  apply DFunLike.ext
  intro z
  change GaussQuantumMultiplier.quantized _ ((_ :ℂ) • f z)=
    (_ :ℂ) • GaussQuantumMultiplier.quantized _ (f z)
  exact map_smul _ _ _

private theorem number_return(s:ℝ)(hs:0<s)(ξ η:ℝ)(f:QuantumTest):
    number (correctedCompleteCore s hs ξ η f)=correctedCompleteCore s hs ξ η (number f):=by
  change number (sourceForwardCore s hs.le (correctedProfileCore s hs ξ η
    (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) f)))=_
  rw [number_forward,number_profile,number_gain]
  rfl

private theorem norm_pair(f:QuantumTest):‖embed f‖^2=(sourcePair f f).re:=by
  simpa only [sourcePair,RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜:=ℂ) (embed f))

/-- The actual complete source retains its gain and returns the signed spin and Number density together. -/
theorem actual_matched_constant_return(s:ℝ)(hs:0<s)(ξ η:ℝ)(f:QuantumTest):
    spinForm (inverseVolumeAction (correctedCompleteCore s hs ξ η f))=
      spinForm (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (forwardUAction s hs.le f)) ∧
    densityForm (inverseVolumeAction (correctedCompleteCore s hs ξ η f))=
      densityForm (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (forwardUAction s hs.le f)):=by
  have hU:=LinearMap.congr_fun (actual_corrected_complete_inverse_volume s hs ξ η) f
  change inverseVolumeAction (correctedCompleteCore s hs ξ η f)=
    correctedCompleteCore s hs ξ η (forwardUAction s hs.le f) at hU
  rw [hU]
  constructor
  · unfold spinForm
    apply Finset.sum_congr rfl
    intro a _
    rw [current_return,norm_pair,complete_pair]
    have hc : GaussCoframeSpin.current a (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (forwardUAction s hs.le f)) = SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (GaussCoframeSpin.current a (forwardUAction s hs.le f)) := by
      apply DFunLike.ext
      intro z
      exact map_smul (GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)) _ _
    rw [hc,norm_pair]
  · let u:=forwardUAction s hs.le f
    let G:=SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)
    have hn : ‖embed (number (correctedCompleteCore s hs ξ η u))‖^2=‖embed (number (G u))‖^2 := by
      rw [number_return,norm_pair,complete_pair]
      have hh:=number_gain s u
      exact congrArg (fun q:QuantumTest=>(sourcePair q q).re) hh.symm |>.trans (norm_pair _).symm
    have hp : (sourcePair (correctedCompleteCore s hs ξ η u) (number (correctedCompleteCore s hs ξ η u))).re=(sourcePair (G u) (number (G u))).re := by
      rw [number_return,complete_pair]
      exact congrArg (fun q:QuantumTest=>(sourcePair (G u) q).re) (number_gain s u).symm
    have hw : ‖embed (correctedCompleteCore s hs ξ η u)‖^2=‖embed (G u)‖^2 := by
      rw [norm_pair,complete_pair,←norm_pair]
    change (9/16:ℝ)*‖embed (number (correctedCompleteCore s hs ξ η u))‖^2+3*(sourcePair (correctedCompleteCore s hs ξ η u) (number (correctedCompleteCore s hs ξ η u))).re+(15/2:ℝ)*‖embed (correctedCompleteCore s hs ξ η u)‖^2=_
    rw [hn,hp,hw]
    rfl

theorem actual_matched_constant_gaussian(s:ℝ)(hs:0<s)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>spinForm (inverseVolumeAction (correctedCompleteCore s hs x.1 x.2 f))+
      densityForm (inverseVolumeAction (correctedCompleteCore s hs x.1 x.2 f))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,spinForm (inverseVolumeAction (correctedCompleteCore s hs x.1 x.2 f))+
      densityForm (inverseVolumeAction (correctedCompleteCore s hs x.1 x.2 f)) ∂γ.prod γ)=
      spinForm (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (forwardUAction s hs.le f))+
      densityForm (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (forwardUAction s hs.le f)):=by
  simp_rw [(actual_matched_constant_return s hs _ _ f).1,
    (actual_matched_constant_return s hs _ _ f).2]
  exact ⟨integrable_const _,by simp only [integral_const,probReal_univ,one_smul]⟩
end LowEnergy.NativePointReturn

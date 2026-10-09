import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiConservativeHeatSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiActualCovarianceStep
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatCorrectedCovarianceSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForwardDriftTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiCorrectedWorkComposition
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open ClockPhiMatchedNoiseCore ClockPhiConservativeHeatSource SourceClockPhiCoframeForwardCore
open scoped Topology ContDiff
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev profile(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀u z,c (combinedMap u z)=c z):End:=clockProfileAction c hc hi 1
private theorem profile_point(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀u z,c (combinedMap u z)=c z)(f:QuantumTest)(z:SourceCoordinateSlice):
    profile c hc hi f z=(Real.exp ((25/2:ℝ)*c z):ℂ) • f (combinedMap (c z) z):=by
  change (Real.exp ((25/2:ℝ)*(1*c z)):ℂ) • f (combinedMap (1*c z) z)=_
  simp only [one_mul]
private theorem combined_add(a b:ℝ)(z:SourceCoordinateSlice):
    combinedMap a (combinedMap b z)=combinedMap (a+b) z:=by
  simp only [combinedMap_apply,sub_add_cancel,smul_smul,←Real.exp_add]
  congr 2
  congr 1
  ring
private theorem profile_add(c d:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hi:∀u z,c (combinedMap u z)=c z)(hj:∀u z,d (combinedMap u z)=d z):
    profile c hc hi*profile d hd hj=
      profile (fun z=>c z+d z) (fun z=>(hc z).add (hd z)) (fun u z=>by rw [hi,hj]):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change profile c hc hi (profile d hd hj f) z=_
  rw [profile_point,profile_point,profile_point,hj,combined_add]
  rw [add_comm (d z) (c z)]
  rw [smul_smul,←Complex.ofReal_mul,←Real.exp_add]
  congr 2
  ring
private def shiftedProfile(t:ℝ)(c:SourceCoordinateSlice→ℝ)(z:SourceCoordinateSlice):ℝ:=c (forwardPoint t z)
private theorem shiftedProfile_smooth(t:ℝ)(ht:0 ≤ t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(z:physicalChart):
    ContDiffAt ℝ ∞ (shiftedProfile t c) z.val:=
  (hc ⟨forwardPoint t z.val,forward_chart t ht z⟩).comp z.val (forward_smooth t ht z)
private theorem forward_combined(t u:ℝ)(z:SourceCoordinateSlice):
    forwardPoint t (combinedMap u z)=combinedMap u (forwardPoint t z):=rfl
private theorem backward_combined(t u:ℝ)(z:SourceCoordinateSlice):
    backwardPoint t (combinedMap u z)=combinedMap u (backwardPoint t z):=rfl
private theorem shiftedProfile_invariant(t:ℝ)(c:SourceCoordinateSlice→ℝ)
    (hi:∀u z,c (combinedMap u z)=c z)(u:ℝ)(z:SourceCoordinateSlice):
    shiftedProfile t c (combinedMap u z)=shiftedProfile t c z:=by
  unfold shiftedProfile
  rw [forward_combined,hi]
private theorem profile_forward(t:ℝ)(ht:0 ≤ t)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hi:∀u z,c (combinedMap u z)=c z):
    profile c hc hi*sourceForwardCore t ht=
      sourceForwardCore t ht*profile (shiftedProfile t c) (shiftedProfile_smooth t ht c hc) (shiftedProfile_invariant t c hi):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change profile c hc hi (sourceForwardCore t ht f) z=
    sourceForwardCore t ht (profile (shiftedProfile t c) (shiftedProfile_smooth t ht c hc) (shiftedProfile_invariant t c hi) f) z
  rw [profile_point]
  by_cases ha:18*t<volume z
  · have hav:18*t<volume (combinedMap (c z) z):=ha
    have hr:backwardRatio t (combinedMap (c z) z)=backwardRatio t z:=rfl
    have hs:shiftedProfile t c (backwardPoint t z)=c z:=by
      unfold shiftedProfile
      rw [forward_backward t ht z ha]
    apply PiLp.ext
    intro word
    change (Real.exp ((25/2:ℝ)*c z):ℂ)*forwardValue t f (combinedMap (c z) z) word=
      forwardValue t (profile (shiftedProfile t c) (shiftedProfile_smooth t ht c hc) (shiftedProfile_invariant t c hi) f) z word
    rw [forwardValue,if_pos hav,forwardValue,if_pos ha]
    change (Real.exp ((25/2:ℝ)*c z):ℂ)*
      ((Real.rpow (backwardRatio t (combinedMap (c z) z)) ((word.card+3:ℝ)/2):ℂ)*
        f (backwardPoint t (combinedMap (c z) z)) word)=
      (Real.rpow (backwardRatio t z) ((word.card+3:ℝ)/2):ℂ)*
        profile (shiftedProfile t c) (shiftedProfile_smooth t ht c hc) (shiftedProfile_invariant t c hi) f (backwardPoint t z) word
    rw [hr,backward_combined,profile_point,hs]
    simp only [PiLp.smul_apply,smul_eq_mul]
    ring
  · have hav:¬18*t<volume (combinedMap (c z) z):=ha
    change (_:ℂ) • forwardValue t f (combinedMap (c z) z)=forwardValue t _ z
    rw [forwardValue,if_neg hav,forwardValue,if_neg ha,smul_zero]
private theorem gain_smooth(ε:ℝ)(z:physicalChart):ContDiffAt ℝ ∞ (SourceClockPhiActualCovarianceStep.gainProfile ε) z.val:=by
  have hr:ContDiffAt ℝ ∞ (forwardRatio (ε^2)) z.val:=
    (volume_smooth.contDiffAt.add contDiffAt_const).div volume_smooth.contDiffAt (volume_pos z).ne'
  exact hr.rpow_const_of_ne (p:=(1/6:ℝ)) (forward_ratio_pos (ε^2) (sq_nonneg _) z).ne'
private def shiftGain(s t:ℝ)(ht:0 ≤ t):End:=
  GaussNativeForm.multiply (fun z=>SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) (forwardPoint t z))
    (fun z=>by
      simpa only [Function.comp_def] using!
        (gain_smooth (Real.sqrt s) ⟨forwardPoint t z.val,forward_chart t ht z⟩).comp z.val (forward_smooth t ht z))
private theorem gain_forward(s t:ℝ)(ht:0 ≤ t):
    SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)*sourceForwardCore t ht=
      sourceForwardCore t ht*shiftGain s t ht:=
  SourceClockPhiForwardGeneratorTransport.actual_forward_multiplier_transport t ht
    (SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s)) (gain_smooth (Real.sqrt s))
private theorem profile_multiply(c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hi:∀u z,c (combinedMap u z)=c z)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(hiB:∀u z,b (combinedMap u z)=b z):
    Commute (profile c hc hi) (GaussNativeForm.multiply b hb):=by
  change profile c hc hi*GaussNativeForm.multiply b hb=GaussNativeForm.multiply b hb*profile c hc hi
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change profile c hc hi (GaussNativeForm.multiply b hb f) z=(b z:ℂ) • profile c hc hi f z
  rw [profile_point,profile_point]
  change (Real.exp ((25/2:ℝ)*c z):ℂ) • ((b (combinedMap (c z) z):ℂ) • f (combinedMap (c z) z))=_
  rw [hiB]
  exact smul_comm _ _ _
private theorem gain_cocycle(s t:ℝ)(hs:0 ≤ s)(ht:0 ≤ t):
    shiftGain s t ht*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)=
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt (s+t)):=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · have hr0:0<forwardRatio t z:=forward_ratio_pos t ht ⟨z,hz⟩
    have hr1:0<forwardRatio s (forwardPoint t z):=forward_ratio_pos s hs ⟨_,forward_chart t ht ⟨z,hz⟩⟩
    have hr:forwardRatio s (forwardPoint t z)*forwardRatio t z=forwardRatio (s+t) z:=by
      unfold forwardRatio
      rw [forward_volume t ht ⟨z,hz⟩]
      field_simp [(volume_pos ⟨z,hz⟩).ne',show volume z+18*t≠0 by linarith [volume_pos ⟨z,hz⟩]]
      ring
    have hg:SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt s) (forwardPoint t z)*
        SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt t) z=
        SourceClockPhiActualCovarianceStep.gainProfile (Real.sqrt (s+t)) z:=by
      unfold SourceClockPhiActualCovarianceStep.gainProfile
      rw [Real.sq_sqrt hs,Real.sq_sqrt ht,Real.sq_sqrt (add_nonneg hs ht),←Real.mul_rpow hr1.le hr0.le,hr]
    change (_:ℂ) • ((_ :ℂ) • f z)=(_ :ℂ) • f z
    rw [smul_smul,←Complex.ofReal_mul,hg]
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    change (_:ℂ) • ((_ :ℂ) • f z)=(_ :ℂ) • f z
    rw [hf,smul_zero,smul_zero,smul_zero]
private theorem complete_profile_add(s t:ℝ)(hs0:0 ≤ s)(ht:0 ≤ t)
    (c d:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val)
    (hi:∀u z,c (combinedMap u z)=c z)(hj:∀u z,d (combinedMap u z)=d z):
    (sourceForwardCore s hs0*profile c hc hi*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s))*
      (sourceForwardCore t ht*profile d hd hj*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t))=
      sourceForwardCore (s+t) (add_nonneg hs0 ht)*
      profile (fun z=>shiftedProfile t c z+d z)
        (fun z=>(shiftedProfile_smooth t ht c hc z).add (hd z))
        (fun u z=>by rw [shiftedProfile_invariant t c hi,hj])*
      SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt (s+t)):=by
  have hG:=gain_forward s t ht
  have hN:=profile_forward t ht c hc hi
  have hcomm:shiftGain s t ht*profile d hd hj=profile d hd hj*shiftGain s t ht:=
    (profile_multiply d hd hj _ _ (fun _ _=>rfl)).eq.symm
  have hJ:=SourceClockPhiForwardDriftTransport.actual_forward_add s t hs0 ht
  have hP:=profile_add (shiftedProfile t c) d (shiftedProfile_smooth t ht c hc) hd
    (shiftedProfile_invariant t c hi) hj
  calc
    _=sourceForwardCore s hs0*profile c hc hi*
        (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s)*sourceForwardCore t ht)*
          profile d hd hj*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by noncomm_ring
    _=sourceForwardCore s hs0*(profile c hc hi*sourceForwardCore t ht)*
        shiftGain s t ht*profile d hd hj*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by rw [hG];noncomm_ring
    _=(sourceForwardCore s hs0*sourceForwardCore t ht)*
        profile (shiftedProfile t c) (shiftedProfile_smooth t ht c hc) (shiftedProfile_invariant t c hi)*
        (shiftGain s t ht*profile d hd hj)*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t):=by rw [hN];noncomm_ring
    _=sourceForwardCore (s+t) (add_nonneg hs0 ht)*
        (profile (shiftedProfile t c) (shiftedProfile_smooth t ht c hc) (shiftedProfile_invariant t c hi)*profile d hd hj)*
        (shiftGain s t ht*SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t)):=by rw [hJ,hcomm];noncomm_ring
    _=_:=by rw [hP,gain_cocycle s t hs0 ht]

open ClockPhiHeatCorrectedCovarianceSource

def composedCoefficient(s t:ℝ)(x:(ℝ×ℝ)×(ℝ×ℝ))(z:SourceCoordinateSlice):ℝ:=
  correctedCoefficient s x.2.1 x.2.2 (forwardPoint t z)+correctedCoefficient t x.1.1 x.1.2 z
private theorem composed_smooth(s t:ℝ)(hs:0<s)(ht:0<t)(x:(ℝ×ℝ)×(ℝ×ℝ))(z:physicalChart):
    ContDiffAt ℝ ∞ (composedCoefficient s t x) z.val:=by
  simpa only [composedCoefficient,Function.comp_def] using!
    ((coefficient_smooth s hs x.2.1 x.2.2 ⟨forwardPoint t z.val,forward_chart t ht.le z⟩).comp z.val
      (forward_smooth t ht.le z)).add (coefficient_smooth t ht x.1.1 x.1.2 z)
private theorem composed_invariant(s t:ℝ)(x:(ℝ×ℝ)×(ℝ×ℝ))(u:ℝ)(z:SourceCoordinateSlice):
    composedCoefficient s t x (combinedMap u z)=composedCoefficient s t x z:=rfl

def composedCompleteCore(s t:ℝ)(hs:0<s)(ht:0<t)(x:(ℝ×ℝ)×(ℝ×ℝ)):End:=
  sourceForwardCore (s+t) (by linarith)*
    profile (composedCoefficient s t x) (composed_smooth s t hs ht x) (composed_invariant s t x)*
    SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt (s+t))

theorem actual_corrected_complete_composition(s t:ℝ)(hs:0<s)(ht:0<t)(x:(ℝ×ℝ)×(ℝ×ℝ)):
    correctedCompleteCore s hs x.2.1 x.2.2*correctedCompleteCore t ht x.1.1 x.1.2=
      composedCompleteCore s t hs ht x:=by
  exact complete_profile_add s t hs.le ht.le
    (correctedCoefficient s x.2.1 x.2.2) (correctedCoefficient t x.1.1 x.1.2)
    (coefficient_smooth s hs x.2.1 x.2.2) (coefficient_smooth t ht x.1.1 x.1.2)
    (fun _ _=>rfl) (fun _ _=>rfl)

def composedNoise(s t:ℝ)(x:(ℝ×ℝ)×(ℝ×ℝ))(z:SourceCoordinateSlice):ℝ:=
  covarianceNoise s x.2.1 x.2.2 (forwardPoint t z)+covarianceNoise t x.1.1 x.1.2 z
private theorem forward_volume_differential(t:ℝ)(ht:0 ≤ t)(z:physicalChart)(v:SourceCoordinateSlice):
    fderiv ℝ volume (forwardPoint t z.val) (fderiv ℝ (forwardPoint t) z.val v)=fderiv ℝ volume z.val v:=by
  have he:(fun x:SourceCoordinateSlice=>volume (forwardPoint t x))=ᶠ[nhds z.val]
      (fun x=>volume x+18*t):=by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    exact forward_volume t ht ⟨x,hx⟩
  have hv:HasFDerivAt volume (fderiv ℝ volume z.val) z.val:=
    (volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hId:HasFDerivAt (fun x:SourceCoordinateSlice=>volume (forwardPoint t x))
      (fderiv ℝ volume z.val) z.val:=(hv.add_const (18*t)).congr_of_eventuallyEq he
  have hc:=((volume_smooth.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z.val
    ((forward_smooth t ht z).differentiableAt (by simp)).hasFDerivAt
  have hu:=hc.unique hId
  exact congrArg (fun L:SourceCoordinateSlice→L[ℝ]ℝ=>L v) hu

theorem actual_composed_profile_gradient(s t:ℝ)(hs:0<s)(ht:0<t)(x:(ℝ×ℝ)×(ℝ×ℝ))
    (z:physicalChart)(v:SourceCoordinateSlice):
    fderiv ℝ (composedCoefficient s t x) z.val v=
      ((SourcePhysicalKineticSquare.reciprocalVolume z.val-SourceClockPhiForwardNativeReturn.forwardU (s+t) z.val-
        composedNoise s t x z.val)/6)*fderiv ℝ volume z.val v:=by
  have hF:=((forward_smooth t ht.le z).differentiableAt (by simp)).hasFDerivAt
  have hS:=((coefficient_smooth s hs x.2.1 x.2.2 ⟨_,forward_chart t ht.le z⟩).differentiableAt (by simp)).hasFDerivAt
  have hT:=((coefficient_smooth t ht x.1.1 x.1.2 z).differentiableAt (by simp)).hasFDerivAt
  have h:=(hS.comp z.val hF).add hT
  have hv:=congrArg (fun L:SourceCoordinateSlice→L[ℝ]ℝ=>L v) h.fderiv
  change fderiv ℝ (composedCoefficient s t x) z.val v=
    fderiv ℝ (correctedCoefficient s x.2.1 x.2.2) (forwardPoint t z.val) (fderiv ℝ (forwardPoint t) z.val v)+
    fderiv ℝ (correctedCoefficient t x.1.1 x.1.2) z.val v at hv
  rw [actual_corrected_profile_gradient s hs x.2.1 x.2.2 ⟨_,forward_chart t ht.le z⟩,
    actual_corrected_profile_gradient t ht x.1.1 x.1.2 z,forward_volume_differential t ht.le z v] at hv
  have hU:SourcePhysicalKineticSquare.reciprocalVolume (forwardPoint t z.val)=
      SourceClockPhiForwardNativeReturn.forwardU t z.val:=by
    unfold SourcePhysicalKineticSquare.reciprocalVolume SourceClockPhiForwardNativeReturn.forwardU
    rw [forward_volume t ht.le z]
  have hu:SourceClockPhiForwardNativeReturn.forwardU s (forwardPoint t z.val)=
      SourceClockPhiForwardNativeReturn.forwardU (s+t) z.val:=by
    unfold SourceClockPhiForwardNativeReturn.forwardU
    rw [forward_volume t ht.le z]
    congr 1
    ring
  rw [hv,hU,hu]
  unfold composedNoise
  ring

end LowEnergy.ClockPhiCorrectedWorkComposition

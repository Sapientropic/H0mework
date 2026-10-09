import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedResolventWard
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualScalarCompressionJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ActualMixedCovarianceGram
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk GaussCoframeForm
open SourceResolventBandLimit FullYSourceResolventGraphSplice
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] compressionCore resolventCore defectAction

private theorem flow_skew (flow : ℝ → End) (G : End)
    (hzero : ∀ f,flow 0 f=f)
    (hpair : ∀ t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv : ∀ f,HasDerivAt (fun t : ℝ => embed (flow t f)) (embed (G f)) 0)
    (f g : QuantumTest) : sourcePair f (G g)= -sourcePair (G f) g := by
  have h := (hderiv f).inner ℂ (hderiv g)
  have he : (fun t : ℝ => inner ℂ (embed (flow t f)) (embed (flow t g)))=
      fun _ => sourcePair f g := funext (fun t => hpair t f g)
  rw [he] at h
  have hh:=h.unique (hasDerivAt_const (0:ℝ) (sourcePair f g))
  change sourcePair (flow 0 f) (G g)+sourcePair (G f) (flow 0 g)=0 at hh
  rw [hzero,hzero] at hh
  exact eq_neg_of_add_eq_zero_left hh

private theorem phi_skew (f g : QuantumTest) : sourcePair f (Phi g)= -sourcePair (Phi f) g :=
  flow_skew SourceScalarAffineScaleTransport.coreFlow Phi
    SourceScalarAffineScaleTransport.coreFlow_zero SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem gauge_skew (f g : QuantumTest) : sourcePair f (Gauge g)= -sourcePair (Gauge f) g :=
  flow_skew SourceGaugeScaleTransport.coreFlow Gauge
    SourceGaugeScaleTransport.coreFlow_zero SourceGaugeScaleTransport.coreFlow_pair
    (fun q => by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g

private theorem paired_sub (A B C D : End) (hA : Paired A B) (hC : Paired C D) :
    Paired (A-C) (B-D) := by
  intro f g
  simp only [Paired,LinearMap.sub_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right] at hA hC ⊢
  rw [hA,hC]

private theorem paired_comm (G A B : End)
    (hG : ∀ f g,sourcePair f (G g)= -sourcePair (G f) g) (hA : Paired A B) :
    Paired (G*A-A*G) (G*B-B*G) := by
  intro f g
  change sourcePair f (G (A g)-A (G g))=sourcePair (G (B f)-B (G f)) g
  simp only [Paired,sourcePair,map_sub,inner_sub_left,inner_sub_right] at hG hA ⊢
  rw [hG,hA,hA,hG]
  ring

private theorem paired_phi (A B : End) (h : Paired A B) : Paired (deltaPhi A) (deltaPhi B) := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator,←SourceScalarAffineScaleTransport.generator_commutator]
  exact paired_comm Phi A B phi_skew h
private theorem paired_gauge (A B : End) (h : Paired A B) : Paired (deltaGauge A) (deltaGauge B) := by
  rw [←SourceGaugeScaleTransport.generator_commutator,←SourceGaugeScaleTransport.generator_commutator]
  exact paired_comm Gauge A B gauge_skew h
private theorem paired_difference (A B : End) (h : Paired A B) :
    Paired (deltaPhi A-deltaGauge A) (deltaPhi B-deltaGauge B) :=
  paired_sub _ _ _ _ (paired_phi A B h) (paired_gauge A B h)
private theorem paired_second (A B : End) (h : Paired A B) : Paired (secondJet A) (secondJet B) :=
  paired_sub _ _ _ _ (paired_difference A B h) (paired_gauge _ _ (paired_difference A B h))

private theorem star_nonreal (z : ℂ) (hz : z.im≠0) : (star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz
private theorem core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem resolvent_pair (F : Index) (z : ℂ) (hz : z.im≠0) :
    Paired (resolventCore F (star z) (star_nonreal z hz)) (resolventCore F z hz) := by
  intro f g
  have h : finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
    unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
    rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
    congr 1
    simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
  simp only [sourcePair,core_embed,h]
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

private theorem second_product (A B : End) :
    secondJet (A*B)=secondJet A*B+A*secondJet B-
      deltaGauge A*(deltaPhi B-deltaGauge B)-(deltaPhi A-deltaGauge A)*deltaGauge B := by
  change ((deltaPhi (A*B)-deltaGauge (A*B))-deltaGauge (deltaPhi (A*B)-deltaGauge (A*B)))=_
  simp only [secondJet,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,deltaPhi,deltaGauge,
    LinearMap.coe_mk,AddHom.coe_mk]
  noncomm_ring

def covariance (F : Index) (z : ℂ) (hz : z.im≠0) : End :=
  resolventCore F (star z) (star_nonreal z hz)*resolventCore F z hz

/-- The original advanced-left/retarded-right covariance retains every mixed source
leg. No independent replacement covariance or prescribed Gram is supplied. -/
theorem actual_mixed_covariance_pair (F : Index) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    let R:=resolventCore F z hz
    sourcePair g (secondJet (covariance F z hz) g)=
      sourcePair (secondJet R g) (R g)+sourcePair (R g) (secondJet R g)-
      sourcePair (deltaGauge R g) ((deltaPhi R-deltaGauge R) g)-
      sourcePair ((deltaPhi R-deltaGauge R) g) (deltaGauge R g) := by
  dsimp only
  rw [covariance,second_product]
  have h:=resolvent_pair F z hz
  have hG:=paired_gauge _ _ h
  have hP:=paired_phi _ _ h
  have hS:=paired_second _ _ h
  simp only [Paired,sourcePair] at h hG hP hS
  simp only [LinearMap.add_apply,LinearMap.sub_apply,Module.End.mul_apply,
    sourcePair,map_add,map_sub,inner_add_right,inner_sub_right,inner_sub_left,h,hG,hP,hS]

/-- The two ordered complex cross terms form one exact real Gram. Their sign is not
replaced by a pointwise positivity assumption. -/
theorem actual_mixed_covariance_gram (F : Index) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    let R:=resolventCore F z hz
    ‖embed (deltaGauge R g)‖^2+‖embed ((deltaPhi R-deltaGauge R) g)‖^2=
      ‖embed (deltaPhi R g)‖^2-2*(sourcePair (R g) (secondJet R g)).re+
        (sourcePair g (secondJet (covariance F z hz) g)).re := by
  dsimp only
  have h:=congrArg Complex.re (actual_mixed_covariance_pair F z hz g)
  have swap (f k:QuantumTest) : (sourcePair f k).re=(sourcePair k f).re := by
    simpa only [sourcePair,Complex.star_def,Complex.conj_re] using
      congrArg Complex.re (inner_conj_symm (𝕜:=ℂ) (embed k) (embed f))
  simp only [Complex.add_re,Complex.sub_re] at h
  rw [swap (secondJet (resolventCore F z hz) g),
    swap ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g)] at h
  have hn:=norm_add_sq (𝕜:=ℂ) (embed (deltaGauge (resolventCore F z hz) g))
    (embed ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g))
  have he : embed (deltaGauge (resolventCore F z hz) g)+
      embed ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g)=
        embed (deltaPhi (resolventCore F z hz) g) := by
    simp only [LinearMap.sub_apply,map_sub]
    abel
  rw [he] at hn
  change ‖embed (deltaPhi (resolventCore F z hz) g)‖^2=_+
    2*(sourcePair (deltaGauge (resolventCore F z hz) g)
      ((deltaPhi (resolventCore F z hz)-deltaGauge (resolventCore F z hz)) g)).re+_ at hn
  linarith only [h,hn]

end LowEnergy.ActualMixedCovarianceGram

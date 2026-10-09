import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedWardPolarization
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedFrequencyJet
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterCore
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualMixedWardFrequencyReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarGaugeScale SourceClockPhiSecondBulk SourceNativeCutoffContact
open SourceScalarAffineCutoffTail ActualAffineCutoffCausalTail ActualMixedWindowGram ActualMixedWardTail
open ActualMixedWardPolarization ActualMixedFrequencyJet FullYSourceResolventGraphSplice
open SourceJointResidualEnergy SourceFourPoleEnergyClosed ActualSylvesterCore ActualSylvesterChannels
open ActualVectorJointCost MeasureTheory Filter Lean Meta Elab Term
open scoped InnerProductSpace BigOperators
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] resolventCore compressionCore

elab "paid_original_resolvent_rank%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceMovingJetFlux 0) "LowEnergy") "SourceMovingJetFlux") "actual_resolvent_rank")
elab "paid_same_pole_difference%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFourPoleEnergyClosed 0) "LowEnergy") "SourceFourPoleEnergyClosed") "pole_difference")

elab "paid_frequency_second_one%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedFrequencyJet 0) "LowEnergy") "ActualMixedFrequencyJet") "second_one")

elab "paid_frequency_right_return%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedFrequencyJet 0) "LowEnergy") "ActualMixedFrequencyJet") "actual_resolvent_return")

private theorem pair_add_right (f g h : QuantumTest) :
    sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_right (f g h : QuantumTest) :
    sourcePair f (g-h)=sourcePair f g-sourcePair f h := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_sub_left (f g h : QuantumTest) :
    sourcePair (f-g) h=sourcePair f h-sourcePair g h := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_smul_right (c : ℂ) (f g : QuantumTest) :
    sourcePair f (c • g)=c*sourcePair f g := by
  simp only [sourcePair,map_smul,inner_smul_right]

private def relative (A : End) : End := deltaPhi A-deltaGauge A
private abbrev K : End := Phi-Gauge
private theorem relative_comm (A : End) : relative A=K*A-A*K := by
  rw [relative,←SourceScalarAffineScaleTransport.generator_commutator,
    ←SourceGaugeScaleTransport.generator_commutator]
  noncomm_ring
private theorem gauge_comm (A : End) : deltaGauge A=Gauge*A-A*Gauge :=
  (SourceGaugeScaleTransport.generator_commutator A).symm

private theorem theta_gauge_commute (m ell : ℕ) : Gauge*thetaAction m ell=thetaAction m ell*Gauge := by
  have h := actual_gauge_cutoff_zero m ell
  rw [←SourceGaugeScaleTransport.generator_commutator] at h
  exact sub_eq_zero.mp h

private theorem theta_relative_commutator (m ell : ℕ) :
    K*thetaAction m ell-thetaAction m ell*K=affineCutoff m ell := by
  rw [←relative_comm,relative,actual_gauge_cutoff_zero,sub_zero]
  rfl

private theorem resolvent_right (F : Index) (z : ℂ) (hz : z.im≠0) :
    resolventCore F z hz*compressionCore F=1+z • resolventCore F z hz := by
  exact (paid_frequency_right_return%) F z hz

private theorem comm_right_frequency (F : Index) (z : ℂ) (hz : z.im≠0) (G : End) :
    z • (G*resolventCore F z hz-resolventCore F z hz*G)=
      (G*resolventCore F z hz-resolventCore F z hz*G)*compressionCore F+
        resolventCore F z hz*(G*compressionCore F-compressionCore F*G) := by
  have h : (G*resolventCore F z hz-resolventCore F z hz*G)*compressionCore F+
      resolventCore F z hz*(G*compressionCore F-compressionCore F*G)=
      G*(resolventCore F z hz*compressionCore F)-(resolventCore F z hz*compressionCore F)*G := by
    noncomm_ring
  rw [resolvent_right,mul_add,add_mul,mul_one,one_mul,mul_smul_comm,smul_mul_assoc] at h
  symm
  exact h.trans (by module)

private theorem pair_reduced (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g h : QuantumTest) :
    let R := resolventCore F z hz
    let W := thetaAction m ell*R
    let X := thetaAction m ell*deltaGauge R
    let Y := thetaAction m ell*relative R
    let S := thetaAction m ell*secondJet R
    wardPair m ell F z hz g h=
      -sourcePair (X g) (Y h)-sourcePair (Y g) (X h)+sourcePair (W g) (S h)+sourcePair (S g) (W h) := by
  dsimp only
  simp only [wardPair,relative,coreWindow,Module.End.mul_apply,LinearMap.sub_apply,
    map_sub,pair_sub_right,pair_sub_left]
  ring

private theorem gauge_pair_return (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g h : QuantumTest) :
    let R := resolventCore F z hz
    let W := thetaAction m ell*R
    let X := thetaAction m ell*deltaGauge R;
    -sourcePair (X g) (W h)-sourcePair (W g) (X h)=
      sourcePair (W (Gauge g)) (W h)+sourcePair (W g) (W (Gauge h)) := by
  dsimp only
  have hx : thetaAction m ell*deltaGauge (resolventCore F z hz)=
      Gauge*(thetaAction m ell*resolventCore F z hz)-(thetaAction m ell*resolventCore F z hz)*Gauge := by
    rw [gauge_comm]
    have ht := congrArg (fun T : End => T*resolventCore F z hz) (theta_gauge_commute m ell)
    linear_combination (norm := noncomm_ring) -ht
  rw [hx]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub_left,pair_sub_right]
  rw [(paid_mixed_gram% gauge_skew)]
  ring

private theorem relative_pair_return (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g h : QuantumTest) :
    let R := resolventCore F z hz
    let W := thetaAction m ell*R
    let Y := thetaAction m ell*relative R;
    -sourcePair (Y g) (W h)-sourcePair (W g) (Y h)=
      sourcePair (W (K g)) (W h)+sourcePair (W g) (W (K h))+
      sourcePair (affineCutoff m ell (R g)) (W h)+sourcePair (W g) (affineCutoff m ell (R h)) := by
  dsimp only
  have hy : thetaAction m ell*relative (resolventCore F z hz)=
      K*(thetaAction m ell*resolventCore F z hz)-(thetaAction m ell*resolventCore F z hz)*K-
        affineCutoff m ell*resolventCore F z hz := by
    rw [relative_comm,←theta_relative_commutator]
    noncomm_ring
  rw [hy]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub_left,pair_sub_right]
  rw [(paid_mixed_gram% phi_skew),(paid_mixed_gram% gauge_skew)]
  ring

/-- The same complex frequency returns the complete actual Ward pair through CF.
Both ordered contacts and the single-pole endpoint remain explicit. -/
theorem actual_whole_frequency_return (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : QuantumTest) :
    let R := resolventCore F z hz
    let C := compressionCore F
    let W := thetaAction m ell*R
    let S := thetaAction m ell*secondJet R
    let A := affineCutoff m ell
    let G0 := deltaGauge C
    let K0 := deltaPhi C-deltaGauge C
    let K := Phi-Gauge
    z*(wardCurrent m ell F z hz g : ℂ)=
      wardPair m ell F z hz g (C g)+sourcePair (W g) (W (secondJet C g))+
      sourcePair (W (Gauge g)) (W (K0 g))+sourcePair (W g) (W (Gauge (K0 g)))+
      sourcePair (W (K g)) (W (G0 g))+sourcePair (W g) (W (K (G0 g)))+
      sourcePair (W g) (A (R (G0 g)))+sourcePair (A (R g)) (W (G0 g))-
      sourcePair (S g) (thetaAction m ell g) := by
  dsimp only
  let R := resolventCore F z hz
  let C := compressionCore F
  let W := thetaAction m ell*R
  let X := thetaAction m ell*deltaGauge R
  let Y := thetaAction m ell*relative R
  let S := thetaAction m ell*secondJet R
  have hw (q : QuantumTest) : z • W q=W (C q)-thetaAction m ell q := by
    have h := congrArg (fun T : End => thetaAction m ell (T q)) (resolvent_right F z hz)
    simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_add,map_smul] at h
    change W (C q)=thetaAction m ell q+z • W q at h
    exact (eq_sub_iff_add_eq.mpr (by rw [h]; abel))
  have hx (q : QuantumTest) : z • X q=X (C q)+W (deltaGauge C q) := by
    have h := comm_right_frequency F z hz Gauge
    rw [←gauge_comm,←gauge_comm] at h
    simpa only [X,Y,W,S,R,C,relative,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
      Module.End.mul_apply,map_smul,map_add,map_sub] using congrArg (fun T : End => thetaAction m ell (T q)) h
  have hy (q : QuantumTest) : z • Y q=Y (C q)+W (relative C q) := by
    have h := comm_right_frequency F z hz K
    rw [←relative_comm,←relative_comm] at h
    simpa only [X,Y,W,S,R,C,relative,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
      Module.End.mul_apply,map_smul,map_add,map_sub] using congrArg (fun T : End => thetaAction m ell (T q)) h
  have hs (q : QuantumTest) : z • S q=
      S (C q)+W (secondJet C q)-X (relative C q)-Y (deltaGauge C q) := by
    have h := actual_right_frequency_jet F z hz
    dsimp only at h
    simpa only [X,Y,W,S,R,C,relative,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.sub_apply,
      Module.End.mul_apply,map_smul,map_add,map_sub] using congrArg (fun T : End => thetaAction m ell (T q)) h
  have hf : z*wardPair m ell F z hz g g=
      wardPair m ell F z hz g (C g)+sourcePair (W g) (W (secondJet C g))-
      sourcePair (X g) (W (relative C g))-sourcePair (W g) (X (relative C g))-
      sourcePair (Y g) (W (deltaGauge C g))-sourcePair (W g) (Y (deltaGauge C g))-
      sourcePair (S g) (thetaAction m ell g) := by
    rw [pair_reduced,pair_reduced]
    change z*(-sourcePair (X g) (Y g)-sourcePair (Y g) (X g)+
      sourcePair (W g) (S g)+sourcePair (S g) (W g))=_
    simp only [mul_add,mul_sub,mul_neg,←pair_smul_right,hx,hy,hs,hw,pair_add_right,pair_sub_right]
    ring
  have hg := gauge_pair_return m ell F z hz g (relative C g)
  have hk := relative_pair_return m ell F z hz g (deltaGauge C g)
  dsimp only at hg hk
  rw [←actual_pair_diagonal]
  change z*wardPair m ell F z hz g g=_
  change z*wardPair m ell F z hz g g=
      wardPair m ell F z hz g (C g)+sourcePair (W g) (W (secondJet C g))+
      sourcePair (W (Gauge g)) (W (relative C g))+sourcePair (W g) (W (Gauge (relative C g)))+
      sourcePair (W (K g)) (W (deltaGauge C g))+sourcePair (W g) (W (K (deltaGauge C g)))+
      sourcePair (W g) (affineCutoff m ell (R (deltaGauge C g)))+
      sourcePair (affineCutoff m ell (R g)) (W (deltaGauge C g))-
      sourcePair (S g) (thetaAction m ell g)
  linear_combination (norm := ring) hf+hg+hk

private theorem core_resolvent_spectral (F : Index) (z : ℂ) (hz : z.im≠0) :
    resolventCore F z hz= -z⁻¹ • (1 : End)+
      ∑ i : SpectralIndex F, (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) • channelCore F (some i) := by
  classical
  apply LinearMap.ext
  intro q
  apply embed_injective
  have hr : embed (resolventCore F z hz q)=finiteResolvent F z (embed q) := by
    unfold resolventCore state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  rw [hr]
  have h := congrArg (fun T : H →L[ℂ] H => T (embed q)) ((paid_original_resolvent_rank%) F z hz)
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,Module.End.one_apply,
    map_add,map_sum,map_smul,actual_channel_core,channel_some,sum_apply,add_apply,smul_apply,
    one_apply_eq_self,InnerProductSpace.rankOne_apply] at h ⊢
  exact h

/-- The escape pole is subtracted inside each entire spectral coefficient before integration. -/
theorem actual_second_resolvent_spectral (F : Index) (z : ℂ) (hz : z.im≠0) :
    secondJet (resolventCore F z hz)=
      ∑ i : SpectralIndex F, (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
        secondJet (channelCore F (some i)) := by
  rw [core_resolvent_spectral,map_add,map_smul,map_sum]
  have ho : secondJet (1 : End)=0 := (paid_frequency_second_one%)
  rw [ho,smul_zero,zero_add]
  simp only [map_smul]

private def poleReturn (advanced : Bool) (μ a w : ℝ) : ℂ :=
  ((a : ℂ)-causalFrequency advanced μ w)⁻¹+(causalFrequency advanced μ w)⁻¹

private theorem pole_return_upper (μ a w : ℝ) :
    poleReturn false μ a w=pole μ a w-pole μ 0 w := by
  simp only [poleReturn,causalFrequency,Bool.false_eq_true,ite_false,pole,Complex.ofReal_zero,
    zero_sub,inv_neg,sub_neg_eq_add]

private theorem pole_return_lower (μ a w : ℝ) :
    poleReturn true μ a w=star (poleReturn false μ a w) := by
  have hz : causalFrequency true μ w=star (causalFrequency false μ w) := by
    apply Complex.ext <;> simp [causalFrequency,SourceResolventBandLimit.line]
  unfold poleReturn
  rw [hz]
  simp only [star_add,star_inv₀,star_sub,Complex.star_def,Complex.conj_ofReal]

private theorem upper_return_integrable (μ a : ℝ) (hμ : 0 < μ) :
    Integrable (fun w : ℝ => poleReturn false μ a w) := by
  simp_rw [pole_return_upper,(paid_same_pole_difference%) μ a 0 _ hμ]
  exact (same_half_integrable μ a 0 hμ).const_mul _

private theorem causal_star_return_integrable (advanced : Bool) (μ a : ℝ) (hμ : 0 < μ) :
    Integrable (fun w : ℝ => star (poleReturn advanced μ a w)) := by
  cases advanced
  · exact (@RCLike.conjLIE ℂ _).toLinearIsometry.toContinuousLinearMap.integrable_comp
      (upper_return_integrable μ a hμ)
  · simp_rw [pole_return_lower,star_star]
    exact upper_return_integrable μ a hμ

private theorem causal_star_return_integral (advanced : Bool) (μ a : ℝ) (hμ : 0 < μ) :
    (∫ w : ℝ, star (poleReturn advanced μ a w))=0 := by
  have hz : (∫ w : ℝ, poleReturn false μ a w)=0 := by
    simp_rw [pole_return_upper]
    exact pole_difference_integral μ a 0 hμ
  cases advanced
  · change (∫ w : ℝ, (starRingEnd ℂ) (poleReturn false μ a w))=0
    rw [integral_conj,hz,map_zero]
  · simp_rw [pole_return_lower,star_star]
    exact hz

private theorem causal_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0 < μ) (w : ℝ) :
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using hμ.ne'

/-- The full complex endpoint is integrable and returns zero on each actual F and either cause. -/
theorem actual_whole_endpoint_integral (advanced : Bool) (μ : ℝ) (hμ : 0 < μ)
    (m ell : ℕ) (F : Index) (g : QuantumTest) :
    let endpoint := fun w : ℝ => sourcePair
      (thetaAction m ell (secondJet (resolventCore F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w)) g)) (thetaAction m ell g)
    Integrable endpoint ∧ (∫ w : ℝ, endpoint w)=0 := by
  classical
  dsimp only
  let c (i : SpectralIndex F) : ℂ := sourcePair
    (thetaAction m ell (secondJet (channelCore F (some i)) g)) (thetaAction m ell g)
  have he (w : ℝ) : sourcePair
      (thetaAction m ell (secondJet (resolventCore F (causalFrequency advanced μ w)
        (causal_nonreal advanced μ hμ w)) g)) (thetaAction m ell g)=
      ∑ i : SpectralIndex F, star (poleReturn advanced μ (channelValue F (some i)) w)*c i := by
    rw [actual_second_resolvent_spectral]
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,sourcePair,
      sum_inner,inner_smul_left,starRingEnd_apply]
    rfl
  have hi (i : SpectralIndex F) : Integrable (fun w : ℝ =>
      star (poleReturn advanced μ (channelValue F (some i)) w)*c i) :=
    (causal_star_return_integrable advanced μ _ hμ).mul_const _
  constructor
  · simp_rw [he]
    exact integrable_finsetSum _ (fun i _ => hi i)
  · simp_rw [he]
    rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
    simp only [integral_mul_const,causal_star_return_integral advanced μ _ hμ,zero_mul,Finset.sum_const_zero]

end LowEnergy.ActualMixedWardFrequencyReturn

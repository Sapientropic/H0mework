import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteHeatGainPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeSignedWorkIntegrable
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiZeroSeedEndpointTail
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiMatchedGainFrequencyPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockYukawaCubicCurrent
open SourceClockPhiRadiusResponsePositiveSource SourceClockPhiNormalizedScalarBudget
open SourceClockPhiMatchedDiffusionSource SourceClockPhiWholeSignedWorkIntegrable
open SourceScalarDoubleCurrent SourceScalarPositiveBulkWard SourceClockPhiRadiusResponseNativeBudget
open SourceMixedNativeReturn SourceInverseJetEnergy SourceLocalizedInverseFormPayment
open SourcePhysicalKineticSquare FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev U:End:=inverseVolumeAction
attribute [local irreducible] resolventCore finiteResolvent sourcePair embed diagonalAction

private theorem inverse_radius:S*r=(1:End):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro x
  change (phiReciprocal x:ℂ) • ((phiRadius x:ℂ) • f x)=f x
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem inverse_theta(m ell:ℕ):Commute S (phiThetaAction m ell):=by
  have hQ:Commute (S:End) ((1:End)-S):=by
    apply LinearMap.ext
    intro f
    change S (f-S f)=S f-S (S f)
    exact map_sub S f (S f)
  have hm:Commute (S:End) (((1:End)-S)^(m+1)):=hQ.pow_right (m+1)
  have he:Commute (S:End) (((1:End)-S)^(ell+1)):=hQ.pow_right (ell+1)
  apply LinearMap.ext
  intro f
  have hmf:=LinearMap.congr_fun hm.eq f
  have hef:=LinearMap.congr_fun he.eq f
  change S ((((1:End)-S)^(m+1)) f-(((1:End)-S)^(ell+1)) f)=
    (((1:End)-S)^(m+1)) (S f)-(((1:End)-S)^(ell+1)) (S f)
  rw [map_sub]
  exact congrArg₂ (·-·) hmf hef
private theorem normalized_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    normalizedState m ell F z hz g=phiThetaAction m ell (state F z hz g)-
      S (phiThetaAction m ell (state F z hz (phiRadiusSource g))):=by
  have hR:resolventCore F z hz (coreEquiv.symm g)=state F z hz g:=by
    simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
  have hρ:resolventCore F z hz (r (coreEquiv.symm g))=state F z hz (phiRadiusSource g):=by
    unfold resolventCore;rfl
  unfold normalizedState
  simp only [hR,hρ,Module.End.mul_apply]

def shiftedState(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):QuantumTest:=
  phiThetaAction m ell (state F z hz (GaussAdjointHistory.coreStep g))-
    S (phiThetaAction m ell (state F z hz (GaussAdjointHistory.coreStep (phiRadiusSource g))))
def gainFrequency(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):ℝ:=
  6*z.re*(sourcePair (normalizedState m ell F z hz g) (U (normalizedState m ell F z hz g))).re

private theorem normalized_source_step(g:diagonal.domain):
    ∀ᶠ F in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      z • normalizedState m ell F z hz g=shiftedState m ell F z hz g:=by
  filter_upwards [actual_source_step g,actual_source_step (phiRadiusSource g)] with F hg hh
  intro m ell z hz
  have h1:=congrArg (fun f:QuantumTest=>phiThetaAction m ell f) (hg z hz)
  have h2:=congrArg (fun f:QuantumTest=>S (phiThetaAction m ell f)) (hh z hz)
  have hS(f:QuantumTest):S (phiThetaAction m ell f)=phiThetaAction m ell (S f):=
    LinearMap.congr_fun (inverse_theta m ell).eq f
  have hf:S (coreEquiv.symm (phiRadiusSource g))=coreEquiv.symm g:=by
    unfold phiRadiusSource
    rw [coreEquiv.symm_apply_apply]
    exact LinearMap.congr_fun inverse_radius _
  rw [normalized_source]
  unfold shiftedState
  simp only [map_sub,map_smul,hS,hf] at h1 h2 ⊢
  linear_combination (norm:=module) h1-h2
private theorem inverse_real(f:QuantumTest):(sourcePair f (U f)).im=0:=by
  have hp:sourcePair f (U f)=sourcePair (U f) f:=multiply_pair _ _ f f
  have hs:star (sourcePair f (U f))=sourcePair (U f) f:=by
    unfold sourcePair
    exact inner_conj_symm _ _
  rw [←hp] at hs
  have h:=congrArg Complex.im hs
  change -(sourcePair f (U f)).im=(sourcePair f (U f)).im at h
  linarith

/-- The same source event shifts both original seeds before every cutoff and frequency. -/
theorem actual_gain_frequency_source(g:diagonal.domain):
    ∀ᶠ F in (sourceFilter:Filter Index),∀m ell:ℕ,∀z:ℂ,∀hz:z.im≠0,
      z • normalizedState m ell F z hz g=shiftedState m ell F z hz g ∧
      gainFrequency m ell F z hz g=6*(sourcePair (U (normalizedState m ell F z hz g))
        (shiftedState m ell F z hz g)).re:=by
  filter_upwards [normalized_source_step g] with F hF
  intro m ell z hz
  refine ⟨hF m ell z hz,?_⟩
  rw [gainFrequency,←hF m ell z hz]
  have hp:sourcePair (U (normalizedState m ell F z hz g)) (normalizedState m ell F z hz g)=
      sourcePair (normalizedState m ell F z hz g) (U (normalizedState m ell F z hz g)):=
    (multiply_pair _ _ _ _).symm
  have hs:sourcePair (U (normalizedState m ell F z hz g)) (z • normalizedState m ell F z hz g)=
      z*sourcePair (U (normalizedState m ell F z hz g)) (normalizedState m ell F z hz g):=by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [hs,hp,Complex.mul_re,inverse_real,mul_zero,sub_zero]
  ring

private theorem inverse_contraction(f:QuantumTest):‖embed (S f)‖≤‖embed f‖:=by
  have hc:phiInverseBounded (embed f)=embed (S f):=GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
  have hn:‖phiInverseBounded‖≤1:=GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
  rw [←hc]
  exact ((phiInverseBounded.le_opNorm (embed f)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))).trans_eq (one_mul _)
private theorem inverse_sub_bound(x y:QuantumTest):
    ‖embed (x-S y)‖^2≤2*‖embed x‖^2+2*‖embed y‖^2:=by
  have h:‖embed x-embed (S y)‖≤‖embed x‖+‖embed y‖:=
    (norm_sub_le (embed x) (embed (S y))).trans
      (add_le_add (le_refl ‖embed x‖) (inverse_contraction y))
  have hs:=pow_le_pow_left₀ (norm_nonneg (embed x-embed (S y))) h 2
  rw [map_sub]
  nlinarith only [hs,sq_nonneg (‖embed x‖-‖embed y‖)]
private theorem shifted_bound(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    ‖embed (shiftedState m ell F z hz g)‖^2≤
      2*‖embed (phiThetaAction m ell (state F z hz (GaussAdjointHistory.coreStep g)))‖^2+
      2*‖embed (phiThetaAction m ell (state F z hz (GaussAdjointHistory.coreStep (phiRadiusSource g))))‖^2:=
  inverse_sub_bound _ _
private theorem frequency_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    (actualFrequency advanced μ w).im≠0:=by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem finite_star(F:Index)(z:ℂ):
    finiteResolvent F (star z)=(finiteResolvent F z).adjoint:=by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous(advanced:Bool)(μ:ℝ)(hμ:0<μ)(F:Index):
    Continuous (fun w:ℝ=>finiteResolvent F (actualFrequency advanced μ w)):=by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have h:(fun w:ℝ=>finiteResolvent F (actualFrequency true μ w))=
        fun w:ℝ=>(finiteResolvent F (line μ w)).adjoint:=by
      funext w;exact finite_star F _
    exact h ▸ (ContinuousLinearMap.adjoint.continuous.comp
      (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))
private theorem theta_measurable(m ell:ℕ)(F:Index)(μ:ℝ)(hμ:0<μ)(g:diagonal.domain)(advanced:Bool):
    Measurable (fun w:ℝ=>ENNReal.ofReal (‖embed (phiThetaAction m ell
      (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)):=by
  have hr(w:ℝ):sourceRead F g (phiThetaAction m ell) (finiteResolvent F (actualFrequency advanced μ w) (g:H))=
      embed (phiThetaAction m ell (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)):=by
    simpa only [state] using source_read_resolvent F g (phiThetaAction m ell)
      (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w)
  simp_rw [←hr]
  exact (((sourceRead F g (phiThetaAction m ell)).continuous.comp
    ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
private theorem ofReal_two_sum(a b:ℝ)(ha:0≤a)(hb:0≤b):
    ENNReal.ofReal (2*a+2*b)=(2:ENNReal)*ENNReal.ofReal a+(2:ENNReal)*ENNReal.ofReal b:=by
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  norm_num
private theorem lintegral_two_sum (f g : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ x, (2:ENNReal)*f x + 2*g x) = 2*(∫⁻ x,f x)+2*(∫⁻ x,g x) := by
  have hh : Measurable (fun x => (2:ENNReal)*f x) := measurable_const.mul hf
  calc
    _ = (∫⁻ x,(2:ENNReal)*f x)+(∫⁻ x,(2:ENNReal)*g x) := lintegral_add_left hh _
    _ = _ := by rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
theorem shifted_common_tail(μ:ℝ)(hμ:0<μ)(g:diagonal.domain):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (‖embed (shiftedState m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)‖^2))≤ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N0,h0⟩:=actual_phi_theta_common_tail μ hμ (GaussAdjointHistory.coreStep g) (ε/4) (by positivity)
  obtain ⟨N1,h1⟩:=actual_phi_theta_common_tail μ hμ (GaussAdjointHistory.coreStep (phiRadiusSource g)) (ε/4) (by positivity)
  refine ⟨max N0 N1,fun m hm ell hml=>?_⟩
  filter_upwards [h0 m (le_trans (le_max_left _ _) hm) ell hml,h1 m (le_trans (le_max_right _ _) hm) ell hml] with F hf0 hf1
  intro advanced
  have hm0:=theta_measurable m ell F μ hμ (GaussAdjointHistory.coreStep g) advanced
  calc
    _≤∫⁻w:ℝ,(2:ENNReal)*ENNReal.ofReal (‖embed (phiThetaAction m ell
        (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (GaussAdjointHistory.coreStep g)))‖^2)+
        (2:ENNReal)*ENNReal.ofReal (‖embed (phiThetaAction m ell
        (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (GaussAdjointHistory.coreStep (phiRadiusSource g))))‖^2):=by
      apply lintegral_mono
      intro w
      have hp:=ENNReal.ofReal_le_ofReal (shifted_bound m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)
      rw [ofReal_two_sum _ _ (sq_nonneg _) (sq_nonneg _)] at hp
      exact hp
    _=(2:ENNReal)*(∫⁻w:ℝ,ENNReal.ofReal (‖embed (phiThetaAction m ell
        (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (GaussAdjointHistory.coreStep g)))‖^2))+
        (2:ENNReal)*(∫⁻w:ℝ,ENNReal.ofReal (‖embed (phiThetaAction m ell
        (state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) (GaussAdjointHistory.coreStep (phiRadiusSource g))))‖^2)):=by
      exact lintegral_two_sum _ _ hm0
    _≤(2:ENNReal)*ENNReal.ofReal (ε/4)+(2:ENNReal)*ENNReal.ofReal (ε/4):=
      add_le_add (mul_le_mul_of_nonneg_left (hf0 advanced) (show (0:ENNReal) ≤ 2 from zero_le)) (mul_le_mul_of_nonneg_left (hf1 advanced) (show (0:ENNReal) ≤ 2 from zero_le))
    _=ENNReal.ofReal ε:=by
      rw [←ofReal_two_sum _ _ (by positivity) (by positivity)]
      congr 1
      ring

private theorem frequency_point_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)
    (he:gainFrequency m ell F z hz g=6*(sourcePair (U (normalizedState m ell F z hz g)) (shiftedState m ell F z hz g)).re)
    (η:ℝ)(hη:0<η):
    |gainFrequency m ell F z hz g|≤η*comparisonEnergy (normalizedState m ell F z hz g)+‖embed (shiftedState m ell F z hz g)‖^2/η:=by
  let w:=normalizedState m ell F z hz g
  let v:=shiftedState m ell F z hz g
  have hi:|(sourcePair (U w) v).re|≤‖embed (U w)‖*‖embed v‖:=
    (Complex.abs_re_le_norm _).trans (by unfold sourcePair;exact norm_inner_le_norm _ _)
  have hu:=SourceClockPhiCompleteHeatGainPayment.comparison_inverse_hardy w
  have hy:=sq_nonneg (η*‖embed (driftClock w)‖-‖embed v‖)
  have hd:η*(‖embed v‖^2/η)=‖embed v‖^2:=by field_simp [hη.ne']
  have hp:η*‖embed (driftClock w)‖^2≤η*comparisonEnergy w:=by
    unfold comparisonEnergy
    have hpos:0≤η*(1/2:ℝ)*‖embed (inverseVolumeAction (SourceClockPhiCombinedScalePressure.combinedGenerator w))‖^2:=by positivity
    nlinarith only [hpos]
  have hu':3*‖embed (U w)‖*‖embed v‖≤‖embed (driftClock w)‖*‖embed v‖:=
    mul_le_mul_of_nonneg_right hu (norm_nonneg _)
  have hY:2*‖embed (driftClock w)‖*‖embed v‖≤η*‖embed (driftClock w)‖^2+‖embed v‖^2/η:=by
    apply (mul_le_mul_iff_right₀ hη).mp
    nlinarith only [hy,hd]
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤6)]
  change 6*|(sourcePair (U w) v).re|≤η*comparisonEnergy w+‖embed v‖^2/η
  nlinarith only [hi,hu',hY,hp]

/-- The unbounded real-frequency gain term is paid by the original comparison form and two fixed H0 seeds. -/
theorem actual_gain_frequency_common_payment(μ:ℝ)(hμ:0<μ)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (|gainFrequency m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
        η*comparisonEnergy (normalizedState m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)))≤ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=shifted_common_tail μ hμ g (η*ε) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced
  calc
    _≤∫⁻w:ℝ,ENNReal.ofReal η⁻¹*ENNReal.ofReal (‖embed (shiftedState m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)‖^2):=by
      apply lintegral_mono
      intro w
      have hp:=frequency_point_price m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g
        (hS m ell _ _).2 η hη
      dsimp only
      rw [←ENNReal.ofReal_mul (inv_pos.mpr hη).le]
      apply ENNReal.ofReal_le_ofReal
      rw [div_eq_mul_inv] at hp
      nlinarith only [hp]
    _=ENNReal.ofReal η⁻¹*(∫⁻w:ℝ,ENNReal.ofReal (‖embed (shiftedState m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)‖^2)):=by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _≤ENNReal.ofReal η⁻¹*ENNReal.ofReal (η*ε):=mul_le_mul_of_nonneg_left (hF advanced) (show (0:ENNReal) ≤ ENNReal.ofReal η⁻¹ from zero_le)
    _=ENNReal.ofReal ε:=by
      rw [←ENNReal.ofReal_mul (inv_pos.mpr hη).le]
      congr 1
      field_simp [hη.ne']
end LowEnergy.ClockPhiMatchedGainFrequencyPayment

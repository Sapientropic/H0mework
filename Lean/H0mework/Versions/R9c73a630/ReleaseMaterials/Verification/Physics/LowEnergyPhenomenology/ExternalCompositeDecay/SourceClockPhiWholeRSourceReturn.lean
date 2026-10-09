import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeCarrierWard
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1600000
noncomputable section
namespace LowEnergy.FirstCurrentWholeCarrier
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentJointBudget FirstCurrentJointBudgetNext FirstCurrentPayerNext
open FirstCurrentAdmissibleElectric FirstCurrentAdmissibleElectric.PhysicalGaussian
open ClockPhiMatchedGainFrequencyPayment ClockPhiHeatCorrectedCovarianceSource MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private theorem n_positive:0<sourceTime 0:=by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  linarith[n_positive,actual_source_noether_gap half]
private theorem frequency_nonreal(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
  have hp:=frequency_positive half
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'
private def oldPair(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):QuantumTest×QuantumTest:=
  (frequencyState half advanced m ell F g q,normalizedForcing m ell F
    (actualFrequency advanced (sourceNoetherFrequency half) q) (frequency_nonreal half advanced q) g)
private def pointCost(half:Bool):ℝ:=scalarNoetherNormCost half+72*sourceTime 0
private theorem point_cost_nonnegative(half:Bool):0≤pointCost half:=by
  unfold pointCost scalarNoetherNormCost
  have hn:=n_positive
  have hk:=(actual_scalar_noether_fraction half).1
  positivity
attribute [local irreducible] sourcePair embed diagonalAction normalizedState normalizedForcing correctedCompleteCore
  updatedFirstCurrentRemainder remainingGeometricPrice physicalJointPrice clockSourcePair
private theorem original_R_mean_price(s:ℝ)(hs:0<s)(half advanced:Bool)(ht:s≤jointClockWindow half)
    (m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    firstCurrentGaussianMean s hs (actualFrequency advanced (sourceNoetherFrequency half) q)
      (frequencyState half advanced m ell F g q)≤
      physicalMean s hs half advanced q (frequencyState half advanced m ell F g q)+
        pointCost half*‖embed (frequencyState half advanced m ell F g q)‖^2:=by
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let hz:=frequency_nonreal half advanced q
  let w:=frequencyState half advanced m ell F g q
  let a:=oldPair half advanced m ell F g q
  have hR:=actual_whole_R_gaussian_source s hs m ell F z hz g
  have hJ:=actual_source_joint_mean_polynomial s hs half advanced m ell F q 0 g hz
  simp only[Complex.ofReal_zero,zero_smul,add_zero,zero_mul,pow_two] at hJ
  change Integrable (fun x:ℝ×ℝ=>physicalJointPrice half advanced z (clockSourcePair s hs x a)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,physicalJointPrice half advanced z (clockSourcePair s hs x a) ∂γ.prod γ)=physicalMean s hs half advanced q w at hJ
  have hi:Integrable (fun x:ℝ×ℝ=>physicalJointPrice half advanced z (clockSourcePair s hs x a)+pointCost half*‖embed w‖^2) (γ.prod γ):=
    hJ.1.add (integrable_const _)
  have hp(x:ℝ×ℝ):updatedFirstCurrentRemainder s hs x m ell F z hz g≤
      physicalJointPrice half advanced z (clockSourcePair s hs x a)+pointCost half*‖embed w‖^2:=by
    have h:=actual_remaining_geometric_point_payment s hs x.1 x.2 half advanced ht m ell F q g
    have he:=actual_physical_joint_source_price s hs x.1 x.2 half advanced m ell F q g hz
    dsimp only at he
    unfold remainingGeometricGap at h
    dsimp only at h
    rw [←he] at h
    change updatedFirstCurrentRemainder s hs x m ell F z hz g-
      physicalJointPrice half advanced z (clockSourcePair s hs x a)≤pointCost half*‖embed w‖^2 at h
    linarith only[h]
  have hb:=integral_mono hR.1 hi hp
  erw [integral_add hJ.1 (integrable_const _)] at hb
  rw [hR.2,hJ.2] at hb
  simpa only[integral_const,MeasureTheory.probReal_univ,one_smul,z,w,frequencyState] using hb
private theorem norm_integrable(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (fun q:ℝ=>‖embed (frequencyState half advanced m ell F g q)‖^2):=by
  have hp:=(SourceClockPhiWholeSignedWorkIntegrable.actual_normalized_pair_integrable
    (sourceNoetherFrequency half) (frequency_positive half) advanced m ell F g 1 1).re
  have he(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
    simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  simpa only[Module.End.one_apply,he,RCLike.re_eq_complex_re,frequencyState] using hp

/-- The complete original signed R, after its actual clock update, is paid by the same finite
admissible physical action plus a common vanishing source error. Every field and forcing leg stays literal. -/
theorem actual_original_whole_R_admissible_common_price(half:Bool)(g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,∀s:ℝ,∀hs:0<s,s≤jointClockWindow half →
      (∫q:ℝ,∫x:ℝ×ℝ,updatedFirstCurrentRemainder s hs x m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) q) (frequency_nonreal half advanced q) g ∂γ.prod γ)≤
      (∫q:ℝ,∫x:ℝ×ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
        (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)) ∂γ.prod γ)+ε:=by
  intro ε hε
  let μ:=sourceNoetherFrequency half
  let c:=pointCost half+1
  have hμ:0<μ:=frequency_positive half
  have hc0:=point_cost_nonnegative half
  have hc:0<c:=by dsimp[c];linarith
  obtain ⟨N,hN⟩:=shifted_common_tail μ hμ g (ε*μ^2/(c+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards[hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced s hs ht
  have hR:=actual_first_current_mean_frequency_integrable s hs half advanced m ell F g 1
  have hJ:=actual_physical_mean_frequency_integrable s hs half advanced m ell F g 1
  have hW:=norm_integrable half advanced m ell F g
  have hZ:Integrable (fun q:ℝ=>‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2):=
    actual_whole_carrier_shifted_square half advanced m ell F g 1
  have hbound:=(integral_mono hR (hJ.add (hW.const_mul (pointCost half)))
    (fun q=>original_R_mean_price s hs half advanced ht m ell F g q))
  erw [integral_add hJ (hW.const_mul (pointCost half)),integral_const_mul] at hbound
  have hreturn:=(actual_whole_electric_mean_payment s hs half advanced m ell F g).2
  have hWpos:0≤wholeNormPrice half advanced m ell F g:=integral_nonneg (fun _=>sq_nonneg _)
  have hZbound:(∫q:ℝ,‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2)≤ε*μ^2/(c+1):=by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity:0≤ε*μ^2/(c+1))).mp
    rw [ofReal_integral_eq_lintegral_ofReal hZ (Eventually.of_forall (fun _=>sq_nonneg _))]
    have he(q:ℝ):actualFrequency advanced μ q • frequencyState half advanced m ell F g q=
        shiftedState m ell F (actualFrequency advanced μ q) (frequency_nonreal half advanced q) g:=
      (hS m ell _ (frequency_nonreal half advanced q)).1
    simpa only[he] using hF advanced
  have hpoint(q:ℝ):μ^2*‖embed (frequencyState half advanced m ell F g q)‖^2≤
      ‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2:=by
    have hz:=Complex.abs_im_le_norm (actualFrequency advanced μ q)
    have hz':μ≤‖actualFrequency advanced μ q‖:=by
      cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
        Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ] using hz
    have hn:=mul_le_mul_of_nonneg_right hz' (norm_nonneg (embed (frequencyState half advanced m ell F g q)))
    have hh:=pow_le_pow_left₀ (by positivity:0≤μ*‖embed (frequencyState half advanced m ell F g q)‖) hn 2
    rw [map_smul,norm_smul]
    nlinarith only[hh]
  have hn:=integral_mono (hW.const_mul (μ^2)) hZ hpoint
  rw [integral_const_mul] at hn
  change μ^2*wholeNormPrice half advanced m ell F g≤_ at hn
  have hnorm:c*wholeNormPrice half advanced m ell F g≤ε:=by
    have ht:=mul_le_mul_of_nonneg_right (hn.trans hZbound) (show 0≤c+1 by positivity)
    have he:(ε*μ^2/(c+1))*(c+1)=ε*μ^2:=by field_simp[(show 0<c+1 by positivity).ne']
    rw [he] at ht
    nlinarith only[ht,sq_pos_of_pos hμ,hWpos]
  simp_rw [(actual_whole_R_gaussian_source s hs m ell F _ (frequency_nonreal half advanced _) g).2]
  change (∫q:ℝ,firstCurrentGaussianMean s hs (actualFrequency advanced μ q) (frequencyState half advanced m ell F g q))≤_
  change (∫q:ℝ,firstCurrentGaussianMean s hs (actualFrequency advanced μ q) (frequencyState half advanced m ell F g q))≤
    (∫q:ℝ,physicalMean s hs half advanced q (frequencyState half advanced m ell F g q))+
      pointCost half*wholeNormPrice half advanced m ell F g at hbound
  dsimp only[c] at hnorm
  linarith only[hbound,hreturn,hnorm,hWpos]
end LowEnergy.FirstCurrentWholeCarrier

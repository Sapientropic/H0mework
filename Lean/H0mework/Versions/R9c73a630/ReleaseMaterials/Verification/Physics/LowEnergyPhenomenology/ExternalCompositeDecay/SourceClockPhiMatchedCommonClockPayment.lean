import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiShiftedSourceGainPrice
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRMatchedCofinal
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiActualCovarianceStep SourceClockPhiWholeSignedWorkIntegrable
open FirstCurrentElectricSuccessor FirstCurrentGeometricPayer
open FirstCurrentJointBudget FirstCurrentPayerNext FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier
open ClockPhiMatchedGainFrequencyPayment OriginalRMatchedVariance MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev G(s:ℝ):End:=sourceGain (Real.sqrt s)
private abbrev C:ℝ:=432/sourceTime 0
attribute [local irreducible] sourcePair embed sourceTime sourceGain normalizedState normalizedForcing frequencyState wholeStep wholeSourceNext wholeSourceMap wholeNormPrice
private theorem n_pos:0 < sourceTime 0:=by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem c_pos:0 < C:=div_pos (by norm_num) n_pos
private theorem mu_pos(half:Bool):0 < sourceNoetherFrequency half:=by
  linarith [n_pos,actual_source_noether_gap half]
private theorem frequency_nonreal(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
  have hp:=mu_pos half
  cases advanced  <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'
private theorem norm_integrable(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (fun q:ℝ=>‖embed (frequencyState half advanced m ell F g q)‖^2):=by
  have h:=(actual_normalized_pair_integrable (sourceNoetherFrequency half) (mu_pos half)
    advanced m ell F g 1 1).re
  have he(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
    simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
  simpa only [Module.End.one_apply,he,RCLike.re_eq_complex_re,frequencyState] using h
private theorem norm_price_shifted(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    wholeNormPrice half advanced m ell F g ≤
      (1/(sourceNoetherFrequency half)^2)*shiftedSourceSquare half advanced m ell F g 1:=by
  let μ:=sourceNoetherFrequency half
  have hμ:0 < μ:=mu_pos half
  have hp(q:ℝ):‖embed (frequencyState half advanced m ell F g q)‖^2 ≤
      (1/μ^2)*‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2:=by
    have ha:=Complex.abs_im_le_norm (actualFrequency advanced μ q)
    have hb:μ ≤ ‖actualFrequency advanced μ q‖:=by
      cases advanced  <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
        Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ] using ha
    have hh:=mul_le_mul_of_nonneg_right hb (norm_nonneg (embed (frequencyState half advanced m ell F g q)))
    have hs:=pow_le_pow_left₀ (by positivity:0 ≤ μ*‖embed (frequencyState half advanced m ell F g q)‖) hh 2
    rw [map_smul,norm_smul]
    field_simp [hμ.ne']
    nlinarith only [hs]
  have hZ:=actual_whole_carrier_shifted_square half advanced m ell F g 1
  simp only [Module.End.one_apply] at hZ
  have h:=integral_mono (norm_integrable half advanced m ell F g) (hZ.const_mul (1/μ^2)) hp
  simpa only [integral_const_mul,wholeNormPrice,shiftedSourceSquare,Module.End.one_apply] using h
private theorem source_next_state(s:ℝ)(hs:0 < s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    (wholeSourceNext s hs half advanced m ell F g q).1=
      wholeSourceMap s hs half advanced m ell F g (frequencyState half advanced m ell F g q):=by
  simp only [wholeSourceNext,wholeSourceMap,electricSourceDirection,Prod.fst_add,Prod.smul_fst,
    LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply]

def matchedSourceMean(s:ℝ)(hs:0 < s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):ℝ:=
  ∫x:ℝ×ℝ,matchedPhysicalClockPrice s hs (actualFrequency advanced (sourceNoetherFrequency half) q) x
    (wholeSourceNext s hs half advanced m ell F g q).1 ∂γ.prod γ

attribute [local irreducible] shiftedSourceSquare shiftedGainRemainder matchedSourceMean matchedRadialDebit
private theorem fraction_payment(a ε:ℝ)(ha:0 ≤ a)(hε:0 < ε):a*(ε/(2*(a+1))) ≤ ε/2:=by
  apply (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr
  field_simp [ne_of_gt (show 0 < a+1 by positivity)]
  nlinarith only [hε]

/-- The clock is selected from the original finite source integral after F, and before both causes and all frequencies. The actual matched physical action plus its full radial debit has a common vanishing positive-part price. -/
theorem actual_original_matched_common_clock_payment(half:Bool)(g:diagonal.domain):
    ∀ε:ℝ,0 < ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠ F in (sourceFilter:Filter Index),
      ∃δ:ℝ,0 < δ ∧ ∀advanced:Bool,∀s:ℝ,∀hs:0 < s,s ≤ δ→
        (∫⁻q:ℝ,ENNReal.ofReal (matchedSourceMean s hs half advanced m ell F g q+
          matchedRadialDebit s hs (wholeSourceNext s hs half advanced m ell F g q).1)) ≤ ENNReal.ofReal ε:=by
  intro ε hε
  let μ:=sourceNoetherFrequency half
  let B:=C*(2+1/μ^2)
  have hμ:0 < μ:=mu_pos half
  have hB:0 < B:=by dsimp [B];have hc:=c_pos;positivity
  obtain ⟨N,hN⟩:=shifted_common_tail μ hμ g (ε/(2*(B+1))) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml,actual_gain_frequency_source g] with F hF hSource
  let P:=shiftedGainRemainder half false m ell F g+shiftedGainRemainder half true m ell F g
  have hP:0 ≤ P:=add_nonneg (actual_shifted_gain_remainder_nonnegative half false m ell F g)
    (actual_shifted_gain_remainder_nonnegative half true m ell F g)
  let δ:=ε/(2*(C*P+1))
  have hδ:0 < δ:=by dsimp [δ];have hc:=c_pos;positivity
  refine ⟨δ,hδ,?_⟩
  intro advanced s hs hsδ
  have hPa:shiftedGainRemainder half advanced m ell F g ≤ P:=by
    cases advanced  <;> dsimp [P]  <;> linarith [actual_shifted_gain_remainder_nonnegative half false m ell F g,
      actual_shifted_gain_remainder_nonnegative half true m ell F g]
  have hZ:=actual_whole_carrier_shifted_square half advanced m ell F g 1
  simp only [Module.End.one_apply] at hZ
  have hShift(q:ℝ):actualFrequency advanced μ q • frequencyState half advanced m ell F g q=
      shiftedState m ell F (actualFrequency advanced μ q) (frequency_nonreal half advanced q) g:=by
    unfold frequencyState
    exact (hSource m ell _ (frequency_nonreal half advanced q)).1
  have hZbound:shiftedSourceSquare half advanced m ell F g 1 ≤ ε/(2*(B+1)):=by
    unfold shiftedSourceSquare
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity:0 ≤ ε/(2*(B+1)))).mp
    change ENNReal.ofReal (∫q:ℝ,‖embed (actualFrequency advanced μ q • frequencyState half advanced m ell F g q)‖^2) ≤ _
    rw [ofReal_integral_eq_lintegral_ofReal hZ (Eventually.of_forall (fun _=>sq_nonneg _))]
    calc
      _=(∫⁻q:ℝ,ENNReal.ofReal (‖embed (shiftedState m ell F (actualFrequency advanced μ q) (frequency_nonreal half advanced q) g)‖^2)):=by
        apply lintegral_congr
        intro q
        exact congrArg (fun v:QuantumTest=>ENNReal.ofReal (‖embed v‖^2)) (hShift q)
      _ ≤ _:=hF advanced
  have hW:=norm_price_shifted half advanced m ell F g
  have hW0:0 ≤ wholeNormPrice half advanced m ell F g:=by
    unfold wholeNormPrice
    exact integral_nonneg (fun _=>sq_nonneg _)
  have hGain:=actual_whole_shifted_gain_price s hs half advanced m ell F g
  have hcost:C*(∫q:ℝ,‖embed (G s (actualFrequency advanced μ q •
      wholeSourceMap s hs half advanced m ell F g (frequencyState half advanced m ell F g q)))‖^2) ≤ ε:=by
    have hzero:B*shiftedSourceSquare half advanced m ell F g 1 ≤ ε/2:=by
      have h1:=mul_le_mul_of_nonneg_left hZbound hB.le
      have h2:=fraction_payment B ε hB.le hε
      exact h1.trans h2
    have hclock:C*s*shiftedGainRemainder half advanced m ell F g ≤ ε/2:=by
      have h1:=mul_le_mul_of_nonneg_left hPa (mul_nonneg c_pos.le hs.le)
      have h2:=mul_le_mul_of_nonneg_right hsδ (mul_nonneg c_pos.le hP)
      have he:C*δ*P ≤ ε/2:=by
        calc
          _=(C*P)*(ε/(2*(C*P+1))):=by dsimp only [δ];ring
          _ ≤ ε/2:=fraction_payment (C*P) ε (mul_nonneg c_pos.le hP) hε
      nlinarith only [h1,h2,he]
    have hgain:=mul_le_mul_of_nonneg_left hGain.2 c_pos.le
    have hbase:C*(2*shiftedSourceSquare half advanced m ell F g 1+wholeNormPrice half advanced m ell F g/2) ≤
        B*shiftedSourceSquare half advanced m ell F g 1:=by
      have h:=mul_le_mul_of_nonneg_left hW c_pos.le
      dsimp only [B]
      nlinarith only [h,mul_nonneg c_pos.le hW0]
    nlinarith only [hgain,hbase,hzero,hclock]
  calc
    _ ≤ ∫⁻q:ℝ,ENNReal.ofReal (C*‖embed (G s (actualFrequency advanced μ q •
        wholeSourceMap s hs half advanced m ell F g (frequencyState half advanced m ell F g q)))‖^2):=by
      apply lintegral_mono
      intro q
      apply ENNReal.ofReal_le_ofReal
      have h:matchedSourceMean s hs half advanced m ell F g q ≤
          C*‖embed (G s (actualFrequency advanced μ q • (wholeSourceNext s hs half advanced m ell F g q).1))‖^2-
          matchedRadialDebit s hs (wholeSourceNext s hs half advanced m ell F g q).1:=by
        unfold matchedSourceMean
        exact actual_whole_source_matched_shifted_payment s hs half advanced m ell F g q
      rw [source_next_state] at h ⊢
      linarith only [h]
    _=ENNReal.ofReal (C*(∫q:ℝ,‖embed (G s (actualFrequency advanced μ q •
        wholeSourceMap s hs half advanced m ell F g (frequencyState half advanced m ell F g q)))‖^2)):=by
      rw [←ofReal_integral_eq_lintegral_ofReal (hGain.1.const_mul C) (Eventually.of_forall (fun _=>mul_nonneg c_pos.le (sq_nonneg _))),integral_const_mul]
    _ ≤ ENNReal.ofReal ε:=ENNReal.ofReal_le_ofReal hcost
end LowEnergy.OriginalRMatchedCofinal

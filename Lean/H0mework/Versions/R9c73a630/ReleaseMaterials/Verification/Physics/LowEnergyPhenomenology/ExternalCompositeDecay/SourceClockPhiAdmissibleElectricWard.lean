import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiAdmissibleElectricSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedGaussianMeanSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentAdmissibleElectric
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentJointBudget FirstCurrentElectricSuccessor FirstCurrentPayerNext
open ClockPhiMatchedGainFrequencyPayment ClockPhiCorrectedGaussianMeanSource
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore
open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev A:=SourceClockPhiCombinedScalePressure.combinedConjugate
attribute [local irreducible] diagonalAction sourcePair embed normalizedState normalizedForcing
  correctedCompleteCore admissibleElectricNext
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hg:=actual_source_noether_gap half
  linarith
private theorem frequency_nonreal(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
  have hp:=frequency_positive half
  cases advanced <;> simpa only[actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hp.ne'

def admissibleSource(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(q:ℝ)(g:diagonal.domain):QuantumTest×QuantumTest:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let hz:=frequency_nonreal half advanced q
  admissibleElectricNext s hs half advanced z (normalizedState m ell F z hz g,normalizedForcing m ell F z hz g)

/-- The one source-chosen input has a common shifted budget before every new Gaussian mean. -/
theorem actual_admissible_shifted_common_payment(half:Bool)(g:diagonal.domain):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,∀s:ℝ,∀hs:0<s,
      (∫⁻q:ℝ,ENNReal.ofReal (‖embed ((actualFrequency advanced (sourceNoetherFrequency half) q) •
        (admissibleSource s hs half advanced m ell F q g).1)‖^2)) ≤ ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=shifted_common_tail (sourceNoetherFrequency half) (frequency_positive half) g (ε/4) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards[hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced s hs
  calc
    _ ≤ ∫⁻q:ℝ,(4:ENNReal)*ENNReal.ofReal (‖embed (shiftedState m ell F
      (actualFrequency advanced (sourceNoetherFrequency half) q) (frequency_nonreal half advanced q) g)‖^2):=by
      apply lintegral_mono
      intro q
      dsimp only
      rw [←show ENNReal.ofReal (4:ℝ)=(4:ENNReal) by norm_num,←ENNReal.ofReal_mul (by norm_num:(0:ℝ) ≤ 4)]
      apply ENNReal.ofReal_le_ofReal
      have hp:=(actual_admissible_electric_source_update s hs half advanced m ell F
        (actualFrequency advanced (sourceNoetherFrequency half) q) (frequency_nonreal half advanced q) g).2.2.1
      dsimp only at hp
      rw [(hS m ell _ (frequency_nonreal half advanced q)).1] at hp
      exact hp
    _=(4:ENNReal)*(∫⁻q:ℝ,ENNReal.ofReal (‖embed (shiftedState m ell F
      (actualFrequency advanced (sourceNoetherFrequency half) q) (frequency_nonreal half advanced q) g)‖^2)):=
      lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 4*ENNReal.ofReal (ε/4):=mul_le_mul_of_nonneg_left (hF advanced) zero_le
    _=ENNReal.ofReal ε:=by rw [←show ENNReal.ofReal (4:ℝ)=(4:ENNReal) by norm_num,←ENNReal.ofReal_mul (by norm_num:(0:ℝ) ≤ 4)];congr 1;ring

private theorem complete_mean_second_price(t:ℝ)(ht:0<t)(f h:QuantumTest):
    t*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))‖ ≤
      ‖embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)‖*‖embed h‖:=by
  let v:=embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)
  let B:=ClockPhiHeatSecondNativeSource.heatASecondReader t ht
  have he:inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))=inner ℂ (B v) (embed h):=by
    simpa only[correctedCompleteCore,Module.End.mul_apply] using
      (actual_corrected_mean_A_squared_source t ht (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)).2 h
  have hn:‖B v‖ ≤ (1/t)*‖v‖:=
    (B.le_opNorm v).trans (mul_le_mul_of_nonneg_right
      (ClockPhiHeatSecondNativeSource.actual_heat_second_native_source t ht).1 (norm_nonneg _))
  have hb:t*‖B v‖ ≤ ‖v‖:=by
    calc _ ≤ t*((1/t)*‖v‖):=mul_le_mul_of_nonneg_left hn ht.le
         _=‖v‖:=by field_simp [ht.ne']
  rw [he]
  calc
    _ ≤ t*(‖B v‖*‖embed h‖):=mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) ht.le
    _=(t*‖B v‖)*‖embed h‖:=by ring
    _ ≤ ‖v‖*‖embed h‖:=mul_le_mul_of_nonneg_right hb (norm_nonneg _)

private theorem complete_mean_small_time_price(t:ℝ)(ht:0<t)(ht1:t ≤ 1)(η:ℝ)(hη:0<η)(f h:QuantumTest):
    t*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))‖ ≤ η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f+
        2*η*‖embed f‖^2+‖embed h‖^2/(4*η):=by
  let G:=‖embed (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f)‖
  let H:=‖embed h‖
  have hG:=SourceClockPhiCompleteHeatGainPayment.actual_complete_heat_gain_payment t ht 1 (by norm_num) 0 f
  change ‖embed (sourceHeatCore t ht 0 (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt t) f))‖^2 ≤ _ at hG
  rw [sourceHeat_norm] at hG
  have hG':G^2 ≤ SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f+2*‖embed f‖^2:=by
    dsimp only [G]
    norm_num only [one_mul,div_one] at hG
    have ht2:t^2 ≤ 1:=by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right ht2 (sq_nonneg ‖embed f‖)]
  have hy:G*H ≤ η*G^2+H^2/(4*η):=by
    have he:(4*η)*(η*G^2+H^2/(4*η))=4*η^2*G^2+H^2:=by
      field_simp [hη.ne']
    have hh:(4*η)*(G*H) ≤ (4*η)*(η*G^2+H^2/(4*η)):=by
      rw [he]
      nlinarith [sq_nonneg (2*η*G-H)]
    exact (mul_le_mul_iff_right₀ (by positivity:0<4*η)).mp hh
  have he:=mul_le_mul_of_nonneg_left hG' hη.le
  have hP:=complete_mean_second_price t ht f h
  change _ ≤ G*H at hP
  dsimp only [H] at hy
  nlinarith

private theorem frequency_norm_floor(advanced:Bool)(μ:ℝ)(hμ:0<μ)(freq:ℝ):
    μ ≤ ‖actualFrequency advanced μ freq‖:=by
  have h:=Complex.abs_im_le_norm (actualFrequency advanced μ freq)
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,abs_neg,abs_of_pos hμ] using h

private theorem complete_mean_source_price(t:ℝ)(ht:0<t)(ht1:t ≤ 1)(η μ:ℝ)(hη:0<η)(hμ:0<μ)
    (z:ℂ)(hz:μ ≤ ‖z‖)(f h:QuantumTest)(he:z • f=h):
    t*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore t ht x.1 x.2 f) ∂γ.prod γ)
      (embed ((A*A) h))‖-η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy f ≤
        (2*η/μ^2+1/(4*η))*‖embed h‖^2:=by
  have hn:‖embed h‖=‖z‖*‖embed f‖:=by rw [←he,map_smul,norm_smul]
  have hF:μ*‖embed f‖ ≤ ‖embed h‖:=by
    rw [hn]
    exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
  have hsq:‖embed f‖^2 ≤ ‖embed h‖^2/μ^2:=by
    apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
    have hh:=mul_self_le_mul_self (by positivity:0 ≤ μ*‖embed f‖) hF
    nlinarith only [hh]
  have hp:=complete_mean_small_time_price t ht ht1 η hη f h
  have hmul:=mul_le_mul_of_nonneg_left hsq (by positivity:0 ≤ 2*η)
  have heq:2*η*(‖embed h‖^2/μ^2)+‖embed h‖^2/(4*η)=
      (2*η/μ^2+1/(4*η))*‖embed h‖^2:=by ring
  linarith only [hp,hmul,heq]


/-- The existing physical Noether consumer now directly pays the new admissible source.
Its original tau weight and its own actual comparison energy are retained. -/
theorem actual_admissible_physical_noether_common_payment(half:Bool)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,∀s:ℝ,∀hs:0<s,∀τ:ℝ,∀hτ:0<τ,τ ≤ 1 →
      (∫⁻q:ℝ,ENNReal.ofReal (τ*‖inner ℂ
        (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2
          (admissibleSource s hs half advanced m ell F q g).1) ∂γ.prod γ)
        (embed ((A*A) (diagonalAction (admissibleSource s hs half advanced m ell F q g).1-
          (admissibleSource s hs half advanced m ell F q g).2)))‖-
        η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy
          (admissibleSource s hs half advanced m ell F q g).1)) ≤ ENNReal.ofReal ε:=by
  intro ε hε
  let μ:=sourceNoetherFrequency half
  have hμ:0<μ:=frequency_positive half
  let C:ℝ:=2*η/μ^2+1/(4*η)
  have hC:0 ≤ C:=by dsimp[C];positivity
  obtain ⟨N,hN⟩:=actual_admissible_shifted_common_payment half g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards[hN m hm ell hml] with F hF
  intro advanced s hs τ hτ hτ1
  have he(q:ℝ):diagonalAction (admissibleSource s hs half advanced m ell F q g).1-
      (admissibleSource s hs half advanced m ell F q g).2=
      (actualFrequency advanced μ q) • (admissibleSource s hs half advanced m ell F q g).1:=by
    have hp:=(actual_admissible_electric_source_update s hs half advanced m ell F
      (actualFrequency advanced μ q) (frequency_nonreal half advanced q) g).1
    exact (congrArg (fun v:QuantumTest=>v-(admissibleSource s hs half advanced m ell F q g).2) hp).trans
      (add_sub_cancel_left _ _)
  calc
    _ ≤ ∫⁻q:ℝ,ENNReal.ofReal C*ENNReal.ofReal (‖embed ((actualFrequency advanced μ q) •
      (admissibleSource s hs half advanced m ell F q g).1)‖^2):=by
      apply lintegral_mono
      intro q
      dsimp only
      rw [he q,←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (complete_mean_source_price τ hτ hτ1 η μ hη hμ _
        (frequency_norm_floor advanced μ hμ q) _ _ rfl)
    _=ENNReal.ofReal C*(∫⁻q:ℝ,ENNReal.ofReal (‖embed ((actualFrequency advanced μ q) •
      (admissibleSource s hs half advanced m ell F q g).1)‖^2)):=lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)):=mul_le_mul_of_nonneg_left (hF advanced s hs) zero_le
    _ ≤ ENNReal.ofReal ε:=by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      exact (div_le_iff₀ (by positivity:C+1>0)).mpr (by nlinarith)
end LowEnergy.FirstCurrentAdmissibleElectric

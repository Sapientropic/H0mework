import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalEcSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCorrectedGaussianMeanSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentOriginalEcPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentJointBudget FirstCurrentElectricSuccessor FirstCurrentPayerNext
open ClockPhiMatchedGainFrequencyPayment ClockPhiCorrectedGaussianMeanSource
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource
open SourceClockPhiCoframeForwardCore ClockPhiMatchedNoiseCore
open FirstCurrentAdmissibleElectric FirstCurrentAdmissibleElectric.PhysicalGaussian
open MeasureTheory Filter
open scoped InnerProductSpace Topology ENNReal
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev A:=SourceClockPhiCombinedScalePressure.combinedConjugate
attribute [local irreducible] diagonalAction sourcePair embed normalizedState normalizedForcing
  correctedCompleteCore originalEcNext
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


def originalEcSource(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(q:ℝ)(g:diagonal.domain):QuantumTest×QuantumTest:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let hz:=frequency_nonreal half advanced q
  originalEcNext s hs half advanced z (normalizedState m ell F z hz g,normalizedForcing m ell F z hz g)

private theorem original_Ec_price(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(q:ℝ)(g:diagonal.domain)
    (τ:ℝ)(hτ:0<τ)(hτ1:τ≤1)(η:ℝ)(hη:0<η):
    let μ:=sourceNoetherFrequency half
    let z:=actualFrequency advanced μ q
    let hz:=frequency_nonreal half advanced q
    let w:=normalizedState m ell F z hz g
    let b:=originalEcSource s hs half advanced m ell F q g
    τ*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2 b.1) ∂γ.prod γ)
      (embed ((A*A) (diagonalAction b.1-b.2)))‖-
      η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy w ≤
      (9*η/(2*μ^2)+2/η)*‖embed (z • w)‖^2:=by
  dsimp only
  let μ:=sourceNoetherFrequency half
  let z:=actualFrequency advanced μ q
  let hz:=frequency_nonreal half advanced q
  let w:=normalizedState m ell F z hz g
  let b:=originalEcSource s hs half advanced m ell F q g
  have hμ:0<μ:=frequency_positive half
  have hpoint:=actual_original_Ec_point_payment s hs half advanced m ell F z hz g
  dsimp only at hpoint
  change ‖embed b.1‖≤2*‖embed w‖ ∧ ‖embed (z • b.1)‖^2≤4*‖embed (z • w)‖^2 ∧
    SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy b.1≤
      2*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy w+‖embed w‖^2 at hpoint
  have hsource:diagonalAction b.1=b.2+z • b.1:=
    (actual_original_Ec_full_source s hs half advanced m ell F z hz g (0,0)).1
  have he:diagonalAction b.1-b.2=z • b.1:=by rw [hsource];module
  have hp:=complete_mean_small_time_price τ hτ hτ1 (η/2) (by positivity) b.1 (z • b.1)
  have hv:=pow_le_pow_left₀ (norm_nonneg (embed b.1)) hpoint.1 2
  have hfloor:μ*‖embed w‖≤‖embed (z • w)‖:=by
    rw [map_smul,norm_smul]
    exact mul_le_mul_of_nonneg_right (frequency_norm_floor advanced μ hμ q) (norm_nonneg _)
  have hw:‖embed w‖^2≤‖embed (z • w)‖^2/μ^2:=by
    apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
    have hh:=pow_le_pow_left₀ (by positivity:0≤μ*‖embed w‖) hfloor 2
    nlinarith only[hh]
  have hEc:=mul_le_mul_of_nonneg_left hpoint.2.2 (by positivity:0≤η/2)
  have hvp:=mul_le_mul_of_nonneg_left hv hη.le
  have hzp:=div_le_div_of_nonneg_right hpoint.2.1 (by positivity:0≤4*(η/2))
  have hwp:=mul_le_mul_of_nonneg_left hw (by positivity:0≤9*η/2)
  change τ*‖inner ℂ (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2 b.1) ∂γ.prod γ)
    (embed ((A*A) (diagonalAction b.1-b.2)))‖-η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy w≤_
  rw [he]
  have hden:4*‖embed (z • w)‖^2/(4*(η/2))=2/η*‖embed (z • w)‖^2:=by ring
  have hcoef:(9*η/2)*(‖embed (z • w)‖^2/μ^2)+2/η*‖embed (z • w)‖^2=
      (9*η/(2*μ^2)+2/η)*‖embed (z • w)‖^2:=by ring
  nlinarith only[hp,hEc,hvp,hzp,hwp,hden,hcoef]

/-- The full updated source is paid by the original Ec reserve with the same coefficient eta.
The common index precedes both causes, every source-selection clock and the original tau-weighted reader. -/
theorem actual_original_Ec_physical_noether_common_payment(half:Bool)(g:diagonal.domain)(η:ℝ)(hη:0<η):
    ∀ε:ℝ,0<ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠ F in (sourceFilter:Filter Index),
      ∀advanced:Bool,∀s:ℝ,∀hs:0<s,∀τ:ℝ,∀hτ:0<τ,τ ≤ 1 →
      (∫⁻q:ℝ,ENNReal.ofReal (τ*‖inner ℂ
        (∫x:ℝ×ℝ,embed (correctedCompleteCore τ hτ x.1 x.2
          (originalEcSource s hs half advanced m ell F q g).1) ∂γ.prod γ)
        (embed ((A*A) (diagonalAction (originalEcSource s hs half advanced m ell F q g).1-
          (originalEcSource s hs half advanced m ell F q g).2)))‖-
        η*SourceClockPhiWholeSignedWorkIntegrable.comparisonEnergy
          (normalizedState m ell F (actualFrequency advanced (sourceNoetherFrequency half) q)
            (frequency_nonreal half advanced q) g))) ≤ ENNReal.ofReal ε:=by
  intro ε hε
  let μ:=sourceNoetherFrequency half
  have hμ:0<μ:=frequency_positive half
  let C:ℝ:=9*η/(2*μ^2)+2/η
  have hC:0 ≤ C:=by dsimp[C];positivity
  obtain ⟨N,hN⟩:=shifted_common_tail μ hμ g (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards[hN m hm ell hml,actual_gain_frequency_source g] with F hF hS
  intro advanced s hs τ hτ hτ1
  calc
    _ ≤ ∫⁻q:ℝ,ENNReal.ofReal C*ENNReal.ofReal (‖embed (shiftedState m ell F
      (actualFrequency advanced μ q) (frequency_nonreal half advanced q) g)‖^2):=by
      apply lintegral_mono
      intro q
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      have hp:=original_Ec_price s hs half advanced m ell F q g τ hτ hτ1 η hη
      dsimp only at hp
      rw [(hS m ell _ (frequency_nonreal half advanced q)).1] at hp
      exact hp
    _=ENNReal.ofReal C*(∫⁻q:ℝ,ENNReal.ofReal (‖embed (shiftedState m ell F
      (actualFrequency advanced μ q) (frequency_nonreal half advanced q) g)‖^2)):=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)):=mul_le_mul_of_nonneg_left (hF advanced) zero_le
    _ ≤ ENNReal.ofReal ε:=by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      exact (div_le_iff₀ (by positivity:C+1>0)).mpr (by nlinarith)

private theorem fraction_interval(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):
    0≤ecFraction s hs half advanced z a ∧ ecFraction s hs half advanced z a≤1:=by
  unfold ecFraction
  have hr:0≤electricGraphRadius a.1:=by unfold electricGraphRadius;positivity
  constructor
  · positivity
  · apply (div_le_one (by positivity)).mpr
    have ha:=norm_nonneg (embed a.1)
    have hA:=abs_nonneg (averagedJointSlope s hs half advanced z a)
    nlinarith [mul_nonneg hA (show 0≤‖embed a.1‖+electricGraphRadius a.1+1 by positivity)]
private theorem scalar_descent(A C lam:ℝ)(hlam:0≤lam)(hlam1:lam≤1):
    (-A/(2*(|C|+1))*lam)*A+(-A/(2*(|C|+1))*lam)^2*C≤ -lam*A^2/(4*(|C|+1)):=by
  have hd:0 < |C|+1:=by positivity
  have hC:lam*C≤|C|+1:=by
    calc lam*C≤lam*(|C|+1):=mul_le_mul_of_nonneg_left (by linarith[le_abs_self C]) hlam
         _≤|C|+1:=by nlinarith only[hlam1,hd]
  have h:=mul_le_mul_of_nonneg_left hC (mul_nonneg hlam (sq_nonneg A))
  field_simp [hd.ne']
  nlinarith only[h]
def originalEcMeanDebit(s:ℝ)(hs:0<s)(half advanced:Bool)(z:ℂ)(a:QuantumTest×QuantumTest):ℝ:=
  ecFraction s hs half advanced z a*(averagedJointSlope s hs half advanced z a)^2/
    (4*(|averagedJointCurvature s hs half advanced z a|+1))

/-- The input paid by the original reserve also lowers the complete, integrable Gaussian physical price. -/
theorem actual_original_Ec_joint_mean_descent(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (freq:ℝ)(g:diagonal.domain)(hz:(actualFrequency advanced (sourceNoetherFrequency half) freq).im≠0):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
    let w:=normalizedState m ell F z hz g
    let a:QuantumTest×QuantumTest:=(w,normalizedForcing m ell F z hz g)
    let b:=originalEcNext s hs half advanced z a
    Integrable (fun x:ℝ×ℝ=>physicalJointPrice half advanced z (clockSourcePair s hs x b)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,physicalJointPrice half advanced z (clockSourcePair s hs x b) ∂γ.prod γ)≤
      physicalMean s hs half advanced freq w-originalEcMeanDebit s hs half advanced z a:=by
  dsimp only
  let z:=actualFrequency advanced (sourceNoetherFrequency half) freq
  let w:=normalizedState m ell F z hz g
  let a:QuantumTest×QuantumTest:=(w,normalizedForcing m ell F z hz g)
  have hp:=actual_source_joint_mean_polynomial s hs half advanced m ell F freq
    (originalEcStep s hs half advanced z a) g hz
  dsimp only at hp
  refine ⟨?_,?_⟩
  · simpa only[originalEcNext] using hp.1
  unfold originalEcNext
  rw [hp.2]
  have hlam:=fraction_interval s hs half advanced z a
  have hd:=scalar_descent (averagedJointSlope s hs half advanced z a)
    (averagedJointCurvature s hs half advanced z a) (ecFraction s hs half advanced z a) hlam.1 hlam.2
  change physicalMean s hs half advanced freq w+
    originalEcStep s hs half advanced z a*averagedJointSlope s hs half advanced z a+
    (originalEcStep s hs half advanced z a)^2*averagedJointCurvature s hs half advanced z a≤_
  unfold originalEcStep originalEcMeanDebit
  have hpay:=add_le_add_left hd (physicalMean s hs half advanced freq w)
  convert hpay using 1 <;> ring
end LowEnergy.FirstCurrentOriginalEcPayer

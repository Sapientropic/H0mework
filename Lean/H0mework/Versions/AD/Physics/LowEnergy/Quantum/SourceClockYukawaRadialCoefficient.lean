import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceRadiusResponseDecay
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarCoefficientTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialCoefficient
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport
open SourceLocalizedInverseFormPayment SourceRadiusResponseDecay PositiveScalarWeakBudget PositiveScalarCoefficientDecay
open SourceRelativePowerTail SourceEscapeSeedTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] fullAction inverseRadius

private theorem coefficient_inverse (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) (f : QuantumTest) :
    coefficient sharp a m ell (inverseAction f)=inverseAction (coefficient sharp a m ell f) := by
  apply DFunLike.ext
  intro z
  rw [original_coefficient_split,original_coefficient_split]
  have hi (q : QuantumTest) : inverseAction q z=(reciprocal z:ℂ) • q z := rfl
  have ht (q : QuantumTest) : thetaAction m ell q z=(SourceNativeCutoffContact.theta m ell z:ℂ) • q z := by
    rw [SourceMixedNativeReturn.thetaAction,←SourceNativeCutoffContact.theta_action_polynomial]
    rfl
  have hy (q : QuantumTest) : fullAction sharp q z=branchMap sharp (GaussNativePotential.scalarField z) (q z) := by
    unfold fullAction
    cases sharp <;> rfl
  have hc (q : QuantumTest) : constantAction sharp (scalarDirection a).1 q z=branchMap sharp (scalarDirection a).1 (q z) := by
    cases sharp <;> rfl
  change thetaAction m ell (constantAction sharp (scalarDirection a).1 (inverseAction f)) z+
    derivativeAction a m ell (fullAction sharp (inverseAction f)) z=_
  rw [hi]
  change _=(reciprocal z:ℂ) • (thetaAction m ell (constantAction sharp (scalarDirection a).1 f) z+
    derivativeAction a m ell (fullAction sharp f) z)
  simp only [ht,hc,hy,hi,derivativeAction,multiply_apply,map_smul,smul_add,smul_smul]
  module

private theorem bounded_coefficient_inverse (sharp : Bool) (a : ScalarIndex) (m ell : ℕ) :
    Commute (boundedCoefficient sharp a m ell) inverseRadius := by
  apply GaussYukawaGrade.core_ext
  intro f
  change boundedCoefficient sharp a m ell (inverseRadius (embed f))=
    inverseRadius (boundedCoefficient sharp a m ell (embed f))
  rw [inverse_core,original_bounded_coefficient_core,original_bounded_coefficient_core,inverse_core,
    coefficient_inverse]

/-- The actual moving radial response retains the complete two-peak native Z,
which commutes with the original scalar inverse radius. -/
theorem actual_response_coefficient_return (sharp : Bool) (a : ScalarIndex) (m ell : ℕ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : H) :
    boundedCoefficient sharp a m ell (response F z g)=
      inverseRadius (boundedCoefficient sharp a m ell (finiteResolvent F z g))-
        boundedCoefficient sharp a m ell (finiteResolvent F z (inverseRadius g)) := by
  rw [actual_response_difference F z hz g,map_sub]
  exact congrArg (fun x : H => x-boundedCoefficient sharp a m ell (finiteResolvent F z (inverseRadius g)))
    (congrArg (fun A : Op => A (finiteResolvent F z g)) (bounded_coefficient_inverse sharp a m ell).eq)

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,if_false,if_true,
    Complex.star_def,Complex.conj_im,SourceResolventBandLimit.line_im,neg_ne_zero] using hμ.ne'

private theorem two_square (x y : H) : ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]

private theorem response_coefficient_bound (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (m ell : ℕ) (F : Index) (g : H) (w : ℝ) :
    (∑ a : ScalarIndex,‖boundedCoefficient sharp a m ell (response F (actualFrequency advanced μ w) g)‖^2) ≤
      2*‖inverseRadius‖^2*(∑ a : ScalarIndex,‖boundedCoefficient sharp a m ell
        (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)+
      2*(∑ a : ScalarIndex,‖boundedCoefficient sharp a m ell
        (finiteResolvent F (actualFrequency advanced μ w) (inverseRadius g))‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  rw [actual_response_coefficient_return sharp a m ell F _ (frequency_nonreal advanced μ hμ w)]
  have hb := pow_le_pow_left₀ (norm_nonneg _) (inverseRadius.le_opNorm
    (boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) g))) 2
  rw [mul_pow] at hb
  have hs := two_square
    (inverseRadius (boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) g)))
    (boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) (inverseRadius g)))
  nlinarith only [hs,hb]

private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (F : Index) :
    Continuous (fun w : ℝ => finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have h (z : ℂ) : (finiteResolvent F z).adjoint=finiteResolvent F (star z) := by
      change star (finiteResolvent F z)=_
      unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
      rw [←Ring.inverse_star,star_sub,star_smul,star_one,
        (GaussGradedCompression.compression_selfAdjoint F).star_eq]
    change Continuous (fun w : ℝ => finiteResolvent F (star (SourceResolventBandLimit.line μ w)))
    simp_rw [←h]
    exact ContinuousLinearMap.adjoint.continuous.comp
      (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F)

private theorem coefficient_energy_measurable (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (m ell : ℕ) (F : Index) (g : H) :
    Measurable (fun w : ℝ => ENNReal.ofReal (∑ a : ScalarIndex,
      ‖boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) := by
  have hc : Continuous (fun w : ℝ => ∑ a : ScalarIndex,
      ‖boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2) := by
    apply continuous_finsetSum
    intro a _
    exact (((boundedCoefficient sharp a m ell).continuous.comp
      ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2)
  exact hc.measurable.ennreal_ofReal

/-- The seventy joined native coefficients on the actual full corrected radial
response have one common full-frequency cutoff on the original source filter. -/
private theorem bounded_radial_joined_coefficient_tail (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
          ‖boundedCoefficient sharp a m ell (response F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := ‖inverseRadius‖^2+1
  have hC : 0<C := by dsimp [C];positivity
  obtain ⟨N₁,h₁⟩ := actual_coefficient_full_frequency_tail sharp advanced μ hμ g (ε/(2*C)) (by positivity)
  obtain ⟨N₂,h₂⟩ := actual_coefficient_full_frequency_tail sharp advanced μ hμ (inverseRadius g) (ε/(2*C)) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hml => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hml,
    h₂ m ((le_max_right _ _).trans hm) ell hml] with F hf hg
  let E (v : H) (w : ℝ) : ENNReal := ENNReal.ofReal (∑ a : ScalarIndex,
    ‖boundedCoefficient sharp a m ell (finiteResolvent F (actualFrequency advanced μ w) v)‖^2)
  have hm' : Measurable (fun w : ℝ => ENNReal.ofReal (2:ℝ)*E (inverseRadius g) w) :=
    (coefficient_energy_measurable sharp advanced μ hμ m ell F (inverseRadius g)).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2*‖inverseRadius‖^2)*E g w+ENNReal.ofReal (2:ℝ)*E (inverseRadius g) w := by
      apply lintegral_mono
      intro w
      dsimp only [E]
      apply (ENNReal.ofReal_le_ofReal (response_coefficient_bound sharp advanced μ hμ m ell F g w)).trans
      rw [←ENNReal.ofReal_mul (by positivity : 0≤2*‖inverseRadius‖^2),
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
      exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal (2*‖inverseRadius‖^2)*(∫⁻ w : ℝ,E g w)+
        ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,E (inverseRadius g) w) := by
      rw [lintegral_add_right _ hm',lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2*‖inverseRadius‖^2)*ENNReal.ofReal (ε/(2*C))+
        ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/(2*C)) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (by positivity : 0≤2*‖inverseRadius‖^2),
        ←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp only [C]
      field_simp

open SourceScalarPositiveBulkWard

def radialCore (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : QuantumTest :=
  state F z hz (coreEquiv (SourceRadiusResponseDecay.radialCurrent F (state F z hz g)))

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem compression_embed (F : Index) (q : QuantumTest) :
    embed (compressionCore F q)=GaussGradedCompression.compression F (embed q) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem radial_core_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (radialCore F z hz g)=response F z (g:H) := by
  rw [radialCore,state_embed]
  change finiteResolvent F z (embed (SourceRadiusResponseDecay.radialCurrent F (state F z hz g)))=_
  rw [original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←inverse_core,state_embed]
  simp only [response,mul_apply_eq_comp,sub_apply,map_sub]

/-- The actual source core contains R(K_S−[defect_F,S])R g. Its complete native70
joined coefficient has a common full-frequency tail; no moving-source premise is supplied. -/
theorem actual_radial_joined_coefficient_tail (sharp advanced : Bool) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (∑ a : ScalarIndex,
          ‖embed (coefficient sharp a m ell
            (radialCore F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := bounded_radial_joined_coefficient_tail sharp advanced μ hμ (g:H) ε hε
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  have he (w : ℝ) (a : ScalarIndex) :
      embed (coefficient sharp a m ell
        (radialCore F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))=
      boundedCoefficient sharp a m ell (response F (actualFrequency advanced μ w) (g:H)) := by
    rw [←original_bounded_coefficient_core,radial_core_embed]
  simpa only [he] using hF

end LowEnergy.SourceClockYukawaRadialCoefficient

import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockYukawaGradedGamma

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaGradedDouble
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussDiagonalHistory GaussUnitaryHistory GaussRadialDomain GaussYukawaOperator NativeHistoryGrade
open SourceQuantumConfigurationHilbert SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceClockYukawaTail
open SourceClockYukawaGradedGamma
open SourceClockYukawaGradedRadial SourceClockYukawaGradedInverse SourceClockYukawaNormalizedCurrent
open SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail
open SourceJointResidualEnergy SourceFourPoleEnergyClosed SourceScalarSignedInverseReturn
open SourceCutoffDilationWard
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter
open scoped Topology InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
local instance labelFintype : Fintype Label := Fintype.ofFinite _
attribute [local irreducible] state fullAction radialWeight radialWeightCore inverseWeightCore
  compressionCore defectAction correctedGradedCurrent

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)


private theorem inverse_weight (sharp : Bool) : Commute inverseRadius (radialWeight sharp) := by
  unfold radialWeight
  apply Commute.sum_right
  intro g _
  exact ((Commute.refl inverseRadius).pow_right _).mul_right
    (show Commute inverseRadius (projection g) from (GaussYukawaGrade.inverse_blocks g).symm)

private theorem tail_commute (A : Op) (hA : Commute inverseRadius A) (m ell : ℕ) :
    Commute (relativeTail m ell) A := by
  have hc : Commute sourceComplement A := (Commute.one_left A).sub_left hA
  exact (hc.pow_left _).sub_left (hc.pow_left _)

private theorem weight_theta (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    radialWeightCore sharp (thetaAction m ell f)=thetaAction m ell (radialWeightCore sharp f) := by
  apply embed_injective
  rw [←original_radial_weight_core,←SourceMixedNativeReturn.theta_core,
    ←SourceMixedNativeReturn.theta_core,←original_radial_weight_core]
  exact congrArg (fun A : Op => A (embed f)) (tail_commute _ (inverse_weight sharp) m ell).eq.symm


private theorem full_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (fullAction sharp q)=sourcePair (fullAction (!sharp) p) q := by
  unfold fullAction
  cases sharp
  · have h := congrArg (starRingEnd ℂ) (GaussFullHamiltonian.yukawa_pair q p)
    simpa only [sourcePair,inner_conj_symm,Bool.not_false] using! h.symm
  · exact GaussFullHamiltonian.yukawa_pair p q

private theorem source_b_adjoint (sharp : Bool) : (sourceB sharp).adjoint=sourceB (!sharp) := by
  cases sharp <;> simp only [sourceB,Bool.not_false,Bool.not_true,if_true,Bool.false_eq_true,if_false,
    ContinuousLinearMap.adjoint_adjoint]

private theorem normalized_pair (sharp : Bool) (p q : QuantumTest) :
    sourcePair p (normalizedAction sharp q)=sourcePair (normalizedAction (!sharp) p) q := by
  change inner ℂ (embed p) (embed (normalizedAction sharp q))=
    inner ℂ (embed (normalizedAction (!sharp) p)) (embed q)
  rw [←original_normalized_core,←original_normalized_core,←ContinuousLinearMap.adjoint_inner_left,
    source_b_adjoint]

private theorem right_yukawa_weight (sharp : Bool) :
    fullAction sharp*radialWeightCore (!sharp)=radialWeightCore (!sharp)*normalizedAction sharp := by
  apply LinearMap.ext
  intro q
  apply SourceCoframeVolume.pair_ext
  intro p
  simp only [Module.End.mul_apply]
  rw [full_pair,original_radial_weight_pair]
  have h := LinearMap.congr_fun (original_graded_yukawa_return (!sharp)) p
  change radialWeightCore (!sharp) (fullAction (!sharp) p)=
    normalizedAction (!sharp) (radialWeightCore (!sharp) p) at h
  rw [h,←normalized_pair,←original_radial_weight_pair]

private theorem right_increment_weight (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    actualIncrement sharp m ell (radialWeight (!sharp) (embed f))=
      (radialWeight (!sharp)*sourceB sharp) (relativeTail m ell (embed f)) := by
  rw [original_radial_weight_core,literal_increment_core,literal_full_return,Module.End.mul_apply,←weight_theta]
  have h := LinearMap.congr_fun (right_yukawa_weight sharp) (thetaAction m ell f)
  change fullAction sharp (radialWeightCore (!sharp) (thetaAction m ell f))=
    radialWeightCore (!sharp) (normalizedAction sharp (thetaAction m ell f)) at h
  rw [h,←original_radial_weight_core,←original_normalized_core,←SourceMixedNativeReturn.theta_core]
  rfl

private theorem response_difference (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    radialResponse sharp F z hz g=radialWeight sharp (finiteResolvent F z (liftedSource sharp g:H))-
      finiteResolvent F z (g:H) := by
  rw [actual_graded_radial_transport sharp F z hz g]
  module

def boundedAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) : ℂ :=
  inner ℂ (radialResponse sharp F (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    ((radialWeight (!sharp)*sourceB sharp) (relativeTail m ell
      (finiteResolvent F z (liftedSource (!sharp) g:H))))

def doubleAmplitude (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) : ℂ :=
  inner ℂ (radialResponse sharp F (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz) k)
    (actualIncrement sharp m ell (radialResponse (!sharp) F z hz g))

/-- Both dynamic legs now contain the actual scalar radial current and complete
compression defect; the fixed inverse lift remains on the original source core. -/
theorem actual_radial_double_split (sharp : Bool) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g k : diagonal.domain) :
    radialAmplitude sharp m ell F z hz g k=
      boundedAmplitude sharp m ell F z hz g k-doubleAmplitude sharp m ell F z hz g k := by
  have h : finiteResolvent F z (g:H)=radialWeight (!sharp)
      (finiteResolvent F z (liftedSource (!sharp) g:H))-radialResponse (!sharp) F z hz g := by
    rw [actual_graded_radial_transport (!sharp) F z hz g]
    module
  unfold radialAmplitude boundedAmplitude doubleAmplitude
  rw [h,map_sub,inner_sub_right]
  congr 2
  rw [←state_embed F z hz (liftedSource (!sharp) g),right_increment_weight]

private def responsePrice (sharp : Bool) (μ : ℝ) (k : diagonal.domain) : ℝ :=
  (‖radialWeight sharp‖*‖(liftedSource sharp k:H)‖+‖(k:H)‖)/μ

private theorem response_bound (sharp : Bool) (F : Index) (z : ℂ) (hz : z.im≠0)
    (k : diagonal.domain) :
    ‖radialResponse sharp F z hz k‖ ≤
      responsePrice sharp |z.im| k := by
  have hr (h : H) : ‖finiteResolvent F z h‖ ≤ (1/|z.im|)*‖h‖ :=
    ((finiteResolvent F z).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (finite_resolvent_norm F z hz) (norm_nonneg h))
  rw [response_difference]
  calc
    _ ≤ ‖radialWeight sharp (finiteResolvent F z (liftedSource sharp k:H))‖+
        ‖finiteResolvent F z (k:H)‖ := norm_sub_le _ _
    _ ≤ ‖radialWeight sharp‖*((1/|z.im|)*‖(liftedSource sharp k:H)‖)+
        (1/|z.im|)*‖(k:H)‖ := add_le_add
      (((radialWeight sharp).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (hr _) (norm_nonneg _))) (hr _)
    _ = _ := by unfold responsePrice;ring

private theorem bounded_amplitude_bound (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (w : ℝ) :
    ‖boundedAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2 ≤
      (responsePrice sharp μ k)^2*‖(radialWeight (!sharp)*sourceB sharp)
        (relativeTail m ell (finiteResolvent F (line μ w) (liftedSource (!sharp) g:H)))‖^2 := by
  have hs : (star (line μ w)).im≠0 := by
    simpa only [Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
  have hr := response_bound sharp F (star (line μ w)) hs k
  simp only [Complex.star_def,Complex.conj_im,line_im,abs_neg,abs_of_pos hμ] at hr
  have hn := (norm_inner_le_norm (𝕜 := ℂ)
    (radialResponse sharp F (star (line μ w)) hs k)
    ((radialWeight (!sharp)*sourceB sharp)
      (relativeTail m ell (finiteResolvent F (line μ w) (liftedSource (!sharp) g:H))))).trans
      (mul_le_mul_of_nonneg_right hr (norm_nonneg _))
  have hp := pow_le_pow_left₀ (norm_nonneg _) hn 2
  simpa only [boundedAmplitude,mul_pow] using hp

private theorem bounded_common_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖boundedAmplitude sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C : ℝ := (responsePrice sharp μ k)^2
  have hC : 0≤C := sq_nonneg _
  obtain ⟨N,hN⟩ := bounded_forcing_full_frequency_tail μ hμ (radialWeight (!sharp)*sourceB sharp)
    (liftedSource (!sharp) g) (ε/(C+1)) (by positivity)
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal
        (‖(radialWeight (!sharp)*sourceB sharp) (relativeTail m ell
          (finiteResolvent F (line μ w) (liftedSource (!sharp) g:H)))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (bounded_amplitude_bound sharp m ell F μ hμ g k w)
    _ = ENNReal.ofReal C*(∫⁻ w : ℝ,ENNReal.ofReal
        (‖(radialWeight (!sharp)*sourceB sharp) (relativeTail m ell
          (finiteResolvent F (line μ w) (liftedSource (!sharp) g:H)))‖^2)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C*ENNReal.ofReal (ε/(C+1)) := by gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hC]
      apply ENNReal.ofReal_le_ofReal
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (by positivity : 0<C+1)).mpr
      nlinarith

private theorem finite_adjoint (F : Index) (z : ℂ) :
    (finiteResolvent F z).adjoint=finiteResolvent F (star z) := by
  change star (finiteResolvent F z)=_
  unfold finiteResolvent FullYSourceResolventGraphSplice.resolvent
  rw [←Ring.inverse_star,star_sub,star_smul,star_one,
    (GaussGradedCompression.compression_selfAdjoint F).star_eq]

private theorem bounded_amplitude_continuous (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    Continuous (fun w : ℝ => boundedAmplitude sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g k) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have ha : Continuous (fun w : ℝ => finiteResolvent F (star (line μ w))) := by
    simp_rw [←finite_adjoint]
    exact ContinuousLinearMap.adjoint.continuous.comp hr
  unfold boundedAmplitude
  simp_rw [response_difference]
  exact (((radialWeight sharp).continuous.comp (ha.clm_apply continuous_const)).sub
    (ha.clm_apply continuous_const)).inner
    ((radialWeight (!sharp)*sourceB sharp).continuous.comp
      ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)))

def doubleRadialCost (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (‖doubleAmplitude sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g k‖^2)

private theorem two_square (a b : ℂ) : ‖a-b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith only [h,sq_nonneg (‖a‖-‖b‖)]

private theorem radial_double_upper (sharp : Bool) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    radialCurrentCost sharp m ell F μ hμ g k ≤
      ENNReal.ofReal (2:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (‖boundedAmplitude sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k‖^2))+
      ENNReal.ofReal (2:ℝ)*doubleRadialCost sharp m ell F μ hμ g k := by
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal (2:ℝ)*ENNReal.ofReal
      (‖boundedAmplitude sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g k‖^2)) := by
    simpa only [Pi.pow_apply] using
      (((bounded_amplitude_continuous sharp m ell F μ hμ g k).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  unfold radialCurrentCost doubleRadialCost
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖boundedAmplitude sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g k‖^2)+
        ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖doubleAmplitude sharp m ell F (line μ w)
          (by simpa only [line_im] using hμ.ne') g k‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [actual_radial_double_split]
      apply (ENNReal.ofReal_le_ofReal (two_square _ _)).trans
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
      exact ENNReal.ofReal_add_le
    _ = _ := by
      rw [lintegral_add_left hm,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- The original whole Gamma is reduced to two scalar radial currents. Both fixed
core lifts and the bounded source insertion are paid on one common cutoff tail. -/
theorem actual_original_double_radial_budget (sharp : Bool) (μ : ℝ) (hμ : 0<μ)
    (g k : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (6:ℝ)*doubleRadialCost sharp m ell F μ hμ g k := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := actual_original_graded_radial_budget sharp μ hμ g k (ε/2) (by positivity)
  obtain ⟨N₂,h₂⟩ := bounded_common_tail sharp μ hμ g k (ε/12) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hml => ?_⟩
  filter_upwards [h₁ m ((le_max_left _ _).trans hm) ell hml,
    h₂ m ((le_max_right _ _).trans hm) ell hml] with F hF hB
  have hc : ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (2:ℝ)=ENNReal.ofReal (6:ℝ) := by norm_num
  have hεeq : ENNReal.ofReal (ε/2)+ENNReal.ofReal (6:ℝ)*ENNReal.ofReal (ε/12)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤6),←ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (3:ℝ)*
        (ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/12)+
          ENNReal.ofReal (2:ℝ)*doubleRadialCost sharp m ell F μ hμ g k) := by
      apply hF.trans
      gcongr
      exact (radial_double_upper sharp m ell F μ hμ g k).trans
        (add_le_add (mul_le_mul (le_refl _) hB bot_le bot_le) (le_refl _))
    _ = _ := by
      rw [mul_add,←mul_assoc,←mul_assoc,hc,←add_assoc,hεeq]

end LowEnergy.SourceClockYukawaGradedDouble

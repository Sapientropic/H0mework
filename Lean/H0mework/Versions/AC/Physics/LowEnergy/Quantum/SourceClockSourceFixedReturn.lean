import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceClockPoleInput
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCoreFormParseval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockSourceFixedReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory GaussCoframeForm
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceDilationRemainder
open SourceClockAcceleration SourceClockReflectedForm SourceClockWindowTime SourceClockFixedInputSeed SourceClockPoleInput
open SourceRadiusHalfWindow SourceRadiusHalfSourceBudget SourceScalarPositiveBulkWard
open SourceJointResidualEnergy SourceInverseNoetherChannelGap SourceFourPoleEnergyClosed SourceResolventBandLimit
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private def causalCoefficient (advanced : Bool) (μ a w : ℝ) : ℂ :=
  if advanced then star (pole μ a w) else pole μ a w

private theorem causal_coefficient (advanced : Bool) (μ a w : ℝ) :
    ((a:ℂ)-causalPoint advanced μ w)⁻¹=causalCoefficient advanced μ a w := by
  cases advanced
  · rfl
  · simp only [causalCoefficient,causalPoint,↓reduceIte,pole,star_inv₀,map_sub,Complex.star_def,Complex.conj_ofReal]

private theorem causal_product_integrable (advanced : Bool) (μ a b : ℝ) (hμ : 0<μ) :
    Integrable (fun w : ℝ => star (causalCoefficient advanced μ a w)*causalCoefficient advanced μ b w) := by
  cases advanced
  · exact two_pole_integrable μ a b hμ
  · simpa only [causalCoefficient,↓reduceIte,star_star,mul_comm] using two_pole_integrable μ b a hμ

private theorem pair_channels (F : Index) (g : diagonal.domain) (A B : End) (c : Channel F → ℂ) :
    sourcePair (A (∑ i,c i • channelTest F g i)) (B (∑ j,c j • channelTest F g j))=
      ∑ i,∑ j,star (c i)*c j*sourcePair (A (channelTest F g i)) (B (channelTest F g j)) := by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem causal_pair_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (A B : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => sourcePair (A (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)) (B (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))) := by
  have hi : Integrable (fun w : ℝ => ∑ i : Channel F,∑ j : Channel F,
      star (causalCoefficient advanced μ (channelValue F i) w)*causalCoefficient advanced μ (channelValue F j) w*
        sourcePair (A (channelTest F g i)) (B (channelTest F g j))) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ =>
      (causal_product_integrable advanced μ (channelValue F i) (channelValue F j) hμ).mul_const _))
  apply hi.congr
  exact Eventually.of_forall (fun w => by
    dsimp only
    rw [actual_state_channels F (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g,pair_channels]
    simp only [causal_coefficient])

private theorem causal_pair_re_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (A B : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => (sourcePair (A (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)) (B (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))).re) := by
  simpa only [RCLike.re_to_complex] using (causal_pair_integrable advanced F μ hμ A B g).re

private theorem causal_form_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (A T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => (sourcePair (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)) (A (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g)))).re) :=
  causal_pair_re_integrable advanced F μ hμ T (A*T) g

private theorem causal_norm_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (A : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => ‖embed (A (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))‖^2) := by
  have h := causal_pair_re_integrable advanced F μ hμ A A g
  apply h.congr
  exact Eventually.of_forall (fun w => by
    simpa only [sourcePair,RCLike.re_to_complex] using! inner_self_eq_norm_sq (𝕜 := ℂ) _)

private theorem polynomial_smooth (i j : Fin 6) : ContDiff ℝ ∞ (fun z : SourceCoordinateSlice =>
    GaussCoframeKinetic.polynomial z.1 i j) := by
  fin_cases i <;> fin_cases j <;> simp [GaussCoframeKinetic.polynomial] <;> fun_prop

private def polynomialAction (i j : Fin 6) : End := multiply
  (fun z => GaussCoframeKinetic.polynomial z.1 i j) (fun _ => (polynomial_smooth i j).contDiffAt)

private theorem causal_coframe_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => coframeGram (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))) := by
  simp_rw [←original_reflected_coframe_gram]
  unfold reflectedForm
  have h := integrable_finsetSum (Finset.univ : Finset (Fin 6)) (fun i _ =>
    integrable_finsetSum (Finset.univ : Finset (Fin 6)) (fun j _ =>
      causal_pair_integrable advanced F μ hμ
        (SourceCoframeCovariantAction.covariantMomentum i*T)
        (((coordinateAction i*coordinateAction j)-polynomialAction i j)*
          SourceCoframeCovariantAction.covariantMomentum j*T) g))
  simpa only [Module.End.mul_apply,RCLike.re_to_complex] using! h.re

private theorem causal_scalar_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => scalarForm (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))) := by
  unfold scalarForm
  exact integrable_finsetSum _ (fun a _ =>
    causal_norm_integrable advanced F μ hμ (covariantMomentum (scalarDirection a)*T) g)

private theorem causal_radius_integrable (advanced : Bool) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (T : End) (g : diagonal.domain) :
    Integrable (fun w : ℝ => radiusForm (T (state F (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g))) := by
  unfold radiusForm
  exact causal_form_integrable advanced F μ hμ _ T g

/-- The complete actual clock price has an L1 frequency profile, generated by finite coherent source channels on each independent causal leg. -/
theorem actual_clock_source_price_integrable (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Integrable (fun w : ℝ => sourcePrice F m ell (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g) := by
  simp_rw [actual_clock_source_price]
  exact (((causal_coframe_integrable advanced F μ hμ (inverseVolumeAction*halfAction m ell) g).const_mul _).add
    ((causal_scalar_integrable advanced F μ hμ (inverseVolumeAction*halfAction m ell) g).const_mul _)).add
      ((causal_radius_integrable advanced F μ hμ (halfAction m ell) g).const_mul _)

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) : 0 ≤ (densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · have h := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
      (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
    exact (sq_nonneg _).trans_eq h.symm
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem radius_floor (f : QuantumTest) : 3*‖embed f‖^2 ≤ radiusForm f := by
  let c : SourceCoordinateSlice → ℝ := fun z => 4*(GaussYukawaCoefficient.radius z)^2-1
  have hc : ContDiff ℝ ∞ c := (contDiff_const.mul (GaussYukawaCoefficient.radius_smooth.pow 2)).sub contDiff_const
  let A : End := multiply c (fun _ => hc.contDiffAt)
  have hr : radiusForm f=(sourcePair f (A f)).re := rfl
  have hpair : (sourcePair f (A f)).re=∫ z : SourceCoordinateSlice,(densityPair f (A f) z).re
      ∂GaussHistoryHilbert.configurationMeasure := by
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f (A f))).symm
  rw [hr,hpair,GaussBoundedMultiplier.norm_square_integral,←integral_const_mul]
  apply integral_mono ((densityPair_integrable f f).re.const_mul 3) (densityPair_integrable f (A f)).re
  intro z
  change 3*(densityPair f f z).re ≤ (densityPair f (A f) z).re
  have he : densityPair f (A f) z=(c z:ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hr := GaussRadialDomain.one_le_radius z
  have hc3 : 3 ≤ c z := by dsimp only [c];nlinarith only [hr]
  exact mul_le_mul_of_nonneg_right hc3 (density_nonnegative f z)

private theorem source_price_nonnegative (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    0 ≤ sourcePrice F m ell z hz g := by
  rw [actual_clock_source_price]
  have hc := original_coframe_gram_nonnegative (inverseVolumeAction (halfAction m ell (state F z hz g)))
  have hs : 0 ≤ scalarForm (inverseVolumeAction (halfAction m ell (state F z hz g))) :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hr := (by positivity : 0 ≤ 3*‖embed (halfAction m ell (state F z hz g))‖^2).trans
    (radius_floor (halfAction m ell (state F z hz g)))
  exact add_nonneg (add_nonneg (mul_nonneg (by positivity) hc) (mul_nonneg (by positivity) hs))
    (mul_nonneg (by positivity) hr)

/-- Only the fixed clock input word is subtracted; all other signed source terms remain joined. -/
def remainingPrice (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  sourcePrice F m ell z hz g-2*(sourcePair (halfAction m ell (coreEquiv.symm g))
    (clockCurrent (halfAction m ell (state F z hz g)))).im

/-- The complete same-F defect, damping, volume/real-frequency pair and all spin/density/gauge/spatial terms remain literal source words. -/
theorem actual_remaining_price_word (F : Index) (m ell : ℕ) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    let q := state F z hz g
    let f := halfAction m ell q
    let d := raisedDefect F (halfAction m ell) q
    remainingPrice F m ell z hz g=
      2*(sourcePair d (clockCurrent f)).im-2*z.im*(sourcePair f (clockCurrent f)).re+
      (sourceTime 0/2)*(sourcePair (inverseVolumeAction f) (halfAction m ell (coreEquiv.symm g)+d)).re+
      (sourceTime 0/2)*z.re*(sourcePair f (inverseVolumeAction f)).re+
      (sourceTime 0)^2*spinForm (inverseVolumeAction f)+(sourceTime 0)^2*densityForm (inverseVolumeAction f)-
      sourceTime 0*gaugeForm (inverseVolumeAction f)-sourceTime 0*spatialForm (inverseVolumeAction f) := by
  dsimp only
  unfold remainingPrice sourcePrice
  simp only [sourcePair,map_add,inner_add_left,Complex.add_im]
  ring

private theorem remaining_causal_point (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (w : ℝ) :
    remainingPrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g=
      sourcePrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g-
        2*clockSeedIntegrand advanced F m ell μ hμ (coreEquiv.symm g) w := by
  simp only [remainingPrice,clockSeedIntegrand,coreEquiv.apply_symm_apply]

/-- Remaining price is integrable as one joined source word; no separate volume input integral is asserted. -/
theorem actual_remaining_price_integrable (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Integrable (fun w : ℝ => remainingPrice F m ell (causalPoint advanced μ w)
      (causal_nonreal advanced μ w hμ) g) := by
  have h := (actual_clock_source_price_integrable advanced F m ell μ hμ g).sub
    ((actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).1.const_mul 2)
  apply h.congr
  exact Eventually.of_forall (fun w => (remaining_causal_point advanced F m ell μ hμ g w).symm)

def remainingBudget (advanced : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) : ℝ :=
  ∫ w : ℝ,remainingPrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g

/-- The original sourceBudget returns exactly to its already-paid fixed seed plus the remaining joined integral. -/
theorem actual_source_budget_fixed_return (advanced : Bool) (F : Index) (m ell : ℕ)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    sourceBudget advanced m ell F μ hμ g=ENNReal.ofReal
      (2*causalSign advanced*Real.pi*fixedClockSeed m ell (coreEquiv.symm g)+
        remainingBudget advanced m ell F μ hμ g) := by
  have hp := actual_clock_source_price_integrable advanced F m ell μ hμ g
  have hs := (actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).1.const_mul 2
  have hr := actual_remaining_price_integrable advanced F m ell μ hμ g
  have he (w : ℝ) : sourcePrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g=
      2*clockSeedIntegrand advanced F m ell μ hμ (coreEquiv.symm g) w+
        remainingPrice F m ell (causalPoint advanced μ w) (causal_nonreal advanced μ w hμ) g := by
    rw [remaining_causal_point advanced F m ell μ hμ g w]
    ring
  unfold sourceBudget
  rw [←ofReal_integral_eq_lintegral_ofReal hp
    (Eventually.of_forall (fun w => source_price_nonnegative F m ell _ _ g))]
  simp_rw [he]
  rw [integral_add hs hr,integral_const_mul,
    (actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).2]
  unfold remainingBudget
  congr 1
  ring

/-- Every F and both causal orientations consume the original fixed input tail on one source-owned cutoff. -/
theorem actual_source_budget_fixed_common_tail (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell : ℕ,∀ F : Index,∀ advanced : Bool,
      ∀ μ : ℝ,∀ hμ : 0<μ,
        sourceBudget advanced m ell F μ hμ g ≤ ENNReal.ofReal ε+
          ENNReal.ofReal (remainingBudget advanced m ell F μ hμ g) := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_fixed_clock_input_common_tail (coreEquiv.symm g) ε hε
  refine ⟨N,fun m hm ell F advanced μ hμ => ?_⟩
  rw [actual_source_budget_fixed_return]
  have hf := hN m hm ell F advanced μ hμ
  rw [integral_const_mul,(actual_fixed_clock_input_integral advanced F m ell μ hμ (coreEquiv.symm g)).2] at hf
  have hf' : |2*causalSign advanced*Real.pi*fixedClockSeed m ell (coreEquiv.symm g)| ≤ ε := by
    simpa only [mul_assoc] using hf
  have hle : 2*causalSign advanced*Real.pi*fixedClockSeed m ell (coreEquiv.symm g) ≤ ε :=
    (le_abs_self _).trans hf'
  exact ENNReal.ofReal_add_le.trans
    (add_le_add (ENNReal.ofReal_le_ofReal hle) (le_refl _))

/-- The original freely-small leg norm price now sees only the remaining joined source integral. -/
def remainingLegPrice (advanced : Bool) (ε : ℝ) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (η : ℝ) : ENNReal :=
  ENNReal.ofReal (η*(Real.pi/μ*‖(g:H)‖^2))+
    ENNReal.ofReal ((1+η⁻¹)/(6*(sourceTime 0)^2))*
      (ENNReal.ofReal ε+ENNReal.ofReal (remainingBudget advanced m ell F μ hμ g))

/-- The complete paired-radius cost actually consumes the reduced same-F source price on a lower strip. -/
theorem actual_paired_radius_fixed_return (ν μ : ℝ) (hν : 0<ν) (hδ : ν<μ)
    (g k : diagonal.domain) (ηg ηk : ℝ) (hηg : 0<ηg) (hηk : 0<ηk) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell : ℕ,∀ F : Index,
      SourceRadiusClosedJointCost.pairedRadiusCost m ell F μ g k ≤
        ENNReal.ofReal (1/(4*Real.pi*(μ-ν)))*
          remainingLegPrice true ε m ell F ν hν k ηk*remainingLegPrice false ε m ell F ν hν g ηg := by
  intro ε hε
  obtain ⟨Ng,hg⟩ := actual_source_budget_fixed_common_tail g ε hε
  obtain ⟨Nk,hk⟩ := actual_source_budget_fixed_common_tail k ε hε
  refine ⟨max Ng Nk,fun m hm ell F => ?_⟩
  have hgb := hg m ((le_max_left _ _).trans hm) ell F false ν hν
  have hkb := hk m ((le_max_right _ _).trans hm) ell F true ν hν
  have hgl : legPrice false m ell F ν hν g ηg ≤ remainingLegPrice false ε m ell F ν hν g ηg := by
    unfold legPrice remainingLegPrice
    exact add_le_add (le_refl _) (mul_le_mul_right hgb _)
  have hkl : legPrice true m ell F ν hν k ηk ≤ remainingLegPrice true ε m ell F ν hν k ηk := by
    unfold legPrice remainingLegPrice
    exact add_le_add (le_refl _) (mul_le_mul_right hkb _)
  apply (actual_paired_radius_clock_budget m ell F ν μ hν hδ g k ηg ηk hηg hηk).trans
  exact mul_le_mul (mul_le_mul (le_refl _) hkl bot_le bot_le) hgl bot_le bot_le

end LowEnergy.SourceClockSourceFixedReturn

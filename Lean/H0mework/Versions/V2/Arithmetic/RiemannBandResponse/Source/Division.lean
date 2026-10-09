import H0mework.Versions.V2.Arithmetic.RiemannBandResponse.Source.Jet

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Division
open Complex MeasureTheory Set Filter Function
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open SourceGeneratedComplexFeaturePerfectification
open scoped InnerProductSpace Topology
noncomputable section

abbrev sourceMellin (source : burnolCompactAnnulusSource) : ℂ → ℂ :=
  fun w => mellin (positiveMellinExtension (coPoissonQuarterMellinMap source.1)) w

def jet {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (source : burnolCompactAnnulusSource) (k : Nat) : ℂ → ℂ :=
  fun w => (-1 : ℂ)^k *
    ((swap dslope (burnolAnalyticComplementDivisionCenter observation))^[k] (sourceMellin source)) w

def state {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (source : burnolCompactAnnulusSource) (k : Nat) :
    HilbertAmbient (quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation)) :=
  quarterFeatureCompletionRightResolventIterate (selectedCoPoissonMuntzParameter observation) k
    (burnolSourceQuarterCompletionValue source (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
      (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial))

@[simp] theorem state_succ {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (source : burnolCompactAnnulusSource) (k : Nat) :
    state observation nontrivial source (k+1) =
      quarterFeatureCompletionRightResolvent (selectedCoPoissonMuntzParameter observation)
        (state observation nontrivial source k) := rfl

theorem source_analytic (source : burnolCompactAnnulusSource) :
    AnalyticOnNhd ℂ (sourceMellin source) burnolPhysicalHeatMellinStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    have doubledPositive : 0 < (2*w).re := by simp only [mul_re]; norm_num; linarith [hw.1]
    have doubledNeOne : 2*w ≠ 1 := ne_of_apply_ne Complex.re (by
      have below : (2*w).re < 1 := by simp only [mul_re]; norm_num; linarith [hw.2]
      simpa using ne_of_lt below)
    have linear : DifferentiableAt ℂ (fun u : ℂ => 2*u) w :=
      (differentiableAt_const (2:ℂ)).mul differentiableAt_id
    have analyticProduct := ((differentiableAt_riemannZeta doubledNeOne).comp w linear).mul
      ((differentiableAt_const (2:ℂ)).mul
        ((coPoissonMuntzEvenSourceMellin_differentiableAt source.1 (2*w) doubledPositive).comp w linear))
    apply DifferentiableAt.differentiableWithinAt
    apply analyticProduct.congr_of_eventuallyEq
    filter_upwards [burnolPhysicalHeatMellinStrip_isOpen.mem_nhds hw] with u hu
    exact positiveMellinExtension_coPoissonQuarterMellinMap_factorization source.1 hu.1 hu.2
  · exact burnolPhysicalHeatMellinStrip_isOpen

private theorem dslope_analytic {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f burnolPhysicalHeatMellinStrip)
    (hc : c ∈ burnolPhysicalHeatMellinStrip) :
    AnalyticOnNhd ℂ (dslope f c) burnolPhysicalHeatMellinStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro w hw
    apply DifferentiableAt.differentiableWithinAt
    by_cases same : w = c
    · subst w
      obtain ⟨p, hp⟩ := hf c hc
      exact hp.has_fpower_series_dslope_fslope.differentiableAt
    · exact (differentiableAt_dslope_of_ne same).2 (hf w hw).differentiableAt
  · exact burnolPhysicalHeatMellinStrip_isOpen

private theorem center_mem {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2 < observation.coordinate.re) :
    burnolAnalyticComplementDivisionCenter observation ∈ burnolPhysicalHeatMellinStrip := by
  dsimp only [burnolAnalyticComplementDivisionCenter, burnolPhysicalHeatMellinStrip]
  norm_num
  constructor <;> linarith [observation.coordinate_re_lt_one]

theorem jet_analytic {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat) :
    AnalyticOnNhd ℂ (jet observation source k) burnolPhysicalHeatMellinStrip := by
  have iter : ∀ j : Nat, AnalyticOnNhd ℂ
      ((swap dslope (burnolAnalyticComplementDivisionCenter observation))^[j] (sourceMellin source))
      burnolPhysicalHeatMellinStrip := by
    intro j
    induction j with
    | zero => exact source_analytic source
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact dslope_analytic ih (center_mem observation rightHalf)
  intro w hw
  exact (analyticAt_const).mul (iter k w hw)

theorem iter_center_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat)
    (before : k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    ((swap dslope (burnolAnalyticComplementDivisionCenter observation))^[k] (sourceMellin source))
      (burnolAnalyticComplementDivisionCenter observation) = 0 := by
  let c := burnolAnalyticComplementDivisionCenter observation
  have analytic := source_analytic source c (center_mem observation rightHalf)
  have series := analytic.hasFPowerSeriesAt
  rw [← (series.has_fpower_series_iterate_dslope_fslope k).coeff_zero 1,
    ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope,
    zero_add, FormalMultilinearSeries.coeff_ofScalars]
  rw [CombSource.Jets.actual_compact_full_jet observation rightHalf source k before]
  simp

theorem jet_center_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat)
    (before : k < generatedRiemannXiZeroOrder owner observation.coordinate) :
    jet observation source k (burnolAnalyticComplementDivisionCenter observation) = 0 := by
  unfold jet
  rw [iter_center_zero observation rightHalf source k before, mul_zero]

theorem jet_succ {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat)
    (before : k < generatedRiemannXiZeroOrder owner observation.coordinate)
    (w : ℂ) (hne : w ≠ burnolAnalyticComplementDivisionCenter observation) :
    (-(1 / (selectedCoPoissonMuntzParameter observation + w - (1/2 : ℂ)))) *
      jet observation source k w = jet observation source (k+1) w := by
  have zero := iter_center_zero observation rightHalf source k before
  have denom : selectedCoPoissonMuntzParameter observation + w - (1/2 : ℂ) =
      w - burnolAnalyticComplementDivisionCenter observation := by
    dsimp only [selectedCoPoissonMuntzParameter, burnolAnalyticComplementDivisionCenter]
    ring
  rw [denom]
  simp only [jet, Function.iterate_succ_apply', dslope_of_ne _ hne, slope,
    zero, vsub_eq_sub, sub_zero, smul_eq_mul, pow_succ]
  ring

theorem state_zero_raw {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (source : burnolCompactAnnulusSource) :
    quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source 0) = (2:ℂ) • burnolCompactAdditiveL2 source := by
  unfold state quarterFeatureCompletionRightResolventIterate
    burnolSourceQuarterCompletionValue burnolSourceQuarterRelation
  rw [quarterMellinFeatureCompletionEvenAdditive_source,
    compactQuarterMellinAdditiveEvenRechart_eq]

theorem state_position {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat) :
    quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source k) ∈ locallyConstantFace burnolUnscaledCommonGapRadius := by
  have rq : 1/4 < (selectedCoPoissonMuntzParameter observation).re := by
    change 1/4 < (observation.coordinate/2).re
    rw [Complex.div_re]; norm_num; linarith
  induction k with
  | zero =>
      rw [state_zero_raw]
      exact (locallyConstantFace burnolUnscaledCommonGapRadius).smul_mem _
        (burnolCompactAdditiveL2_mem_locallyConstantFace source)
  | succ k ih =>
      rw [state_succ, quarterMellinFeatureCompletionEvenAdditive_rightResolvent_eq_direct _ rq]
      unfold burnolDirectRightResolvent
      apply (locallyConstantFace burnolUnscaledCommonGapRadius).neg_mem
      apply integral_mem_closedSubmodule
        {toSubmodule := locallyConstantFace burnolUnscaledCommonGapRadius,
         isClosed' := locallyConstantFace_isClosed burnolUnscaledCommonGapRadius}
      · exact burnolDirectRightResolventIntegrand_integrableOn_feature _ rq _
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
        apply (locallyConstantFace burnolUnscaledCommonGapRadius).smul_mem
        apply burnolMultiplicativeDilation_mem_locallyConstantFace_of_nonpositive
          burnolUnscaledCommonGapRadius (by norm_num [burnolUnscaledCommonGapRadius])
        · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hh.le) (by norm_num)
        · exact ih

theorem ambient_initial {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (wr : 1/4 < w.re) (wb : w.re < 1/2) :
    burnolFeatureCompletionAmbientMellinRead (burnolDivisionCompletedMellinCoordinate w wr wb)
      (selectedCoPoissonMuntzParameter observation) (state observation nontrivial source 0) = sourceMellin source w := by
  let coordinate := burnolDivisionCompletedMellinCoordinate w wr wb
  have restriction := congrArg (fun functional : BurnolPaAmbientCarrier →L[ℂ] ℂ =>
    functional (burnolCompactAdditivePhysicalState source))
    (burnolAmbientCompletedMellinEvaluator_restrict coordinate)
  change burnolAmbientCompletedMellinEvaluator coordinate (burnolCompactAdditiveL2 source) =
    burnolCompletedMellinEvaluator coordinate (burnolCompactAdditivePhysicalState source) at restriction
  have original := four_mul_burnolCompletedMellinEvaluator_eq_quarterMellinRead source coordinate
  unfold burnolFeatureCompletionAmbientMellinRead
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  rw [state_zero_raw, map_smul]
  change 2 * (2 * burnolAmbientCompletedMellinEvaluator coordinate (burnolCompactAdditiveL2 source)) = _
  rw [restriction]
  change 4 * burnolCompletedMellinEvaluator coordinate (burnolCompactAdditivePhysicalState source) =
    mellin (positiveMellinExtension (coPoissonQuarterMellinMap source.1)) (coordinate.value / 2) at original
  rw [show coordinate.value / 2 = w by dsimp only [coordinate, burnolDivisionCompletedMellinCoordinate]; ring] at original
  dsimp only [sourceMellin]
  linear_combination original

theorem ambient_jet {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (wr : 1/4 < w.re) (wb : w.re < 1/2)
    (beyond : (burnolAnalyticComplementDivisionCenter observation).re < w.re)
    (k : Nat) (atMost : k ≤ generatedRiemannXiZeroOrder owner observation.coordinate) :
    burnolFeatureCompletionAmbientMellinRead (burnolDivisionCompletedMellinCoordinate w wr wb)
      (selectedCoPoissonMuntzParameter observation) (state observation nontrivial source k) = jet observation source k w := by
  induction k with
  | zero => simpa only [jet, pow_zero, Function.iterate_zero_apply, one_mul] using ambient_initial observation nontrivial source w wr wb
  | succ k ih =>
      have rq : 1/4 < (selectedCoPoissonMuntzParameter observation).re := by
        change 1/4 < (observation.coordinate/2).re
        rw [Complex.div_re]; norm_num; linarith
      have decay : ((1/2 : ℂ) - selectedCoPoissonMuntzParameter observation - w).re < 0 := by
        change (burnolAnalyticComplementDivisionCenter observation).re - w.re < 0
        linarith
      rw [state_succ, burnolFeatureCompletionAmbientMellinRead_rightResolvent_eq_scalar
        (burnolDivisionCompletedMellinCoordinate w wr wb) w
        (selectedCoPoissonMuntzParameter observation) rfl rq
        (state observation nontrivial source k) (state_position observation nontrivial rightHalf source k) decay,
        ih (by omega)]
      exact jet_succ observation rightHalf source k (by omega) w (by
        intro equal; subst w; exact (lt_irrefl _ beyond))

theorem heat_jet {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat)
    (atMost : k ≤ generatedRiemannXiZeroOrder owner observation.coordinate)
    (physical : quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source k) ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius) :
    EqOn (burnolDivisionNormalizedPhysicalHeatMellin
      ⟨quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
        (state observation nontrivial source k), physical⟩)
      (jet observation source k) burnolPhysicalHeatMellinStrip := by
  let w₀ : ℂ := 3/8
  have wMem : w₀ ∈ burnolPhysicalHeatMellinStrip := by
    dsimp only [w₀, burnolPhysicalHeatMellinStrip]; constructor <;> norm_num
  have wrNhd : {w : ℂ | 1/4 < w.re} ∈ 𝓝 w₀ :=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds (by dsimp only [w₀]; norm_num)
  have wbNhd : {w : ℂ | w.re < 1/2} ∈ 𝓝 w₀ :=
    (isOpen_Iio.preimage Complex.continuous_re).mem_nhds (by dsimp only [w₀]; norm_num)
  have beyondNhd : {w : ℂ | (burnolAnalyticComplementDivisionCenter observation).re < w.re} ∈ 𝓝 w₀ := by
    apply (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds
    dsimp only [w₀, burnolAnalyticComplementDivisionCenter]
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
    norm_num; linarith
  have eventuallyEqual : burnolDivisionNormalizedPhysicalHeatMellin
      ⟨quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
        (state observation nontrivial source k), physical⟩ =ᶠ[𝓝 w₀] jet observation source k := by
    filter_upwards [wrNhd, wbNhd, beyondNhd] with w wr wb beyond
    rw [burnolDivisionNormalizedPhysicalHeatMellin_eq_ambientRead
      (selectedCoPoissonMuntzParameter observation) (state observation nontrivial source k) physical w wr wb]
    exact ambient_jet observation nontrivial rightHalf source w wr wb beyond k atMost
  exact (burnolDivisionNormalizedPhysicalHeatMellin_analyticOn _).eqOn_of_preconnected_of_eventuallyEq
    (jet_analytic observation rightHalf source k) burnolPhysicalHeatMellinStrip_isConnected.isPreconnected wMem eventuallyEqual

theorem compact_fourier_zero_of_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat)
    (before : k < generatedRiemannXiZeroOrder owner observation.coordinate)
    (physical : quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source k) ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius) :
    burnolCompletedMellinEvaluator (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
      (evenFaceFourier burnolUnscaledCommonGapRadius
        ⟨quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
          (state observation nontrivial source k), physical⟩) = 0 := by
  let value : BurnolPaAmbientCarrier := ⟨_, physical⟩
  let c := burnolAnalyticComplementDivisionCenter observation
  have heat := heat_jet observation nontrivial rightHalf source k (Nat.le_of_lt before) physical
    (center_mem observation rightHalf)
  rw [jet_center_zero observation rightHalf source k before] at heat
  have gammaC : Gammaℝ (2*c) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    have positive := (center_mem observation rightHalf).1
    change 0 < (2*burnolAnalyticComplementDivisionCenter observation).re
    simp only [Complex.mul_re]; norm_num; linarith)
  have rawHeat : mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) c = 0 := by
    change (Gammaℝ (2*c))⁻¹ * mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) c = 0 at heat
    exact (mul_eq_zero.mp heat).resolve_left (inv_ne_zero gammaC)
  have bridge := burnolGenericHomogeneousGammaMellinBridge
    (evenFaceFourier burnolUnscaledCommonGapRadius value)
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
  have fourier := burnolGenericGaussianFourierHomogeneousIdentity value observation.coordinate
  change Gammaℝ observation.coordinate *
    burnolCompletedMellinEvaluator (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
      (evenFaceFourier burnolUnscaledCommonGapRadius value) =
    (1/2 : ℂ) * mellin (burnolGenericGaussianHeatPairTotal (fourierL2 (value : BurnolL2)))
      (observation.coordinate/2) at bridge
  rw [fourier, show (1-observation.coordinate)/2 = c by
    dsimp only [c, burnolAnalyticComplementDivisionCenter]; ring, rawHeat, mul_zero] at bridge
  exact (mul_eq_zero.mp bridge).resolve_left
    (Gammaℝ_ne_zero_of_re_pos (lt_trans (by norm_num) rightHalf))

theorem compact_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
    (rightHalf : 1/2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) (k : Nat)
    (atMost : k ≤ generatedRiemannXiZeroOrder owner observation.coordinate) :
    quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source k) ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  induction k with
  | zero =>
      rw [state_zero_raw]
      exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).smul_mem _
        (burnolCompactAdditiveL2_mem_evenBurnolClosedFace source)
  | succ k ih =>
      have previous := ih (by omega)
      have rq : 1/4 < (selectedCoPoissonMuntzParameter observation).re := by
        change 1/4 < (observation.coordinate/2).re
        rw [Complex.div_re]; norm_num; linarith
      rw [state_succ]
      apply quarterMellinFeatureCompletionEvenAdditive_rightResolvent_mem_evenBurnolClosedFace
        burnolUnscaledCommonGapRadius (by norm_num [burnolUnscaledCommonGapRadius])
        (selectedCoPoissonMuntzParameter observation) rq
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        (state observation nontrivial source k) previous
      have coordinateEq : burnolDivisionCoordinate (selectedCoPoissonMuntzParameter observation) rq
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial) =
          burnolDivisionZeroCompletedMellinCoordinate observation rightHalf := by
        unfold burnolDivisionCoordinate burnolDivisionZeroCompletedMellinCoordinate
        congr 1
        change 2*(observation.coordinate/2) = observation.coordinate
        ring
      rw [coordinateEq]
      exact compact_fourier_zero_of_physical observation nontrivial rightHalf source k (by omega) previous


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Division
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

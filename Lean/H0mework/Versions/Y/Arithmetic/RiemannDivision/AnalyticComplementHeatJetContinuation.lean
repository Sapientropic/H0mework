import H0mework.Versions.Y.Arithmetic.RiemannDivision.AnalyticComplementAmbientMellinRead
import H0mework.Versions.Y.Arithmetic.BurnolMellin.PhysicalHeatMellinStrip

/-! # Physical heat continuation of the analytic-complement division jet -/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter FourierTransform
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal InnerProductSpace Topology

noncomputable section

def burnolDivisionZeroCompletedMellinCoordinate
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    BurnolCompletedMellinCoordinate :=
  ⟨observation.coordinate, rightHalf, observation.coordinate_re_lt_one⟩


def burnolDivisionNormalizedPhysicalHeatMellin
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius)
    (coordinate : ℂ) : ℂ :=
  (Gammaℝ (2 * coordinate))⁻¹ *
    mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) coordinate

theorem burnolDivisionNormalizedPhysicalHeatMellin_analyticOn
    (value : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) :
    AnalyticOnNhd ℂ (burnolDivisionNormalizedPhysicalHeatMellin value)
      burnolPhysicalHeatMellinStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro coordinate membership
    have doubledDifferentiable : DifferentiableAt ℂ
        (fun current : ℂ => 2 * current) coordinate :=
      (differentiableAt_const (2 : ℂ)).mul differentiableAt_id
    have gammaDifferentiable : DifferentiableAt ℂ
        (fun current : ℂ => (Gammaℝ (2 * current))⁻¹) coordinate :=
      differentiable_Gammaℝ_inv.differentiableAt.comp coordinate
        doubledDifferentiable
    exact (gammaDifferentiable.mul
      (burnolGenericGaussianHeatPair_mellin_differentiableAt
        value coordinate membership.1 membership.2)).differentiableWithinAt
  · exact burnolPhysicalHeatMellinStrip_isOpen

theorem burnolAnalyticComplementDivisionJet_analyticOn
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (k : ℕ) :
    AnalyticOnNhd ℂ
      (burnolAnalyticComplementDivisionJet owner observation k)
      burnolPhysicalHeatMellinStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro coordinate membership
    exact (differentiableAt_burnolAnalyticComplementDivisionJet
      observation k coordinate membership.1 membership.2).differentiableWithinAt
  · exact burnolPhysicalHeatMellinStrip_isOpen

theorem burnolDivisionNormalizedPhysicalHeatMellin_eq_ambientRead
    (z : ℂ)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (physical : quarterMellinFeatureCompletionEvenAdditive z value ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius)
    (w : ℂ) (rightQuarter : 1 / 4 < w.re)
    (belowHalf : w.re < 1 / 2) :
    burnolDivisionNormalizedPhysicalHeatMellin
        ⟨quarterMellinFeatureCompletionEvenAdditive z value, physical⟩ w =
      burnolFeatureCompletionAmbientMellinRead
        (burnolDivisionCompletedMellinCoordinate w rightQuarter belowHalf)
        z value := by
  let coordinate :=
    burnolDivisionCompletedMellinCoordinate w rightQuarter belowHalf
  let state : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius :=
    ⟨quarterMellinFeatureCompletionEvenAdditive z value, physical⟩
  have bridge := burnolGenericHomogeneousGammaMellinBridge state coordinate
  have gammaNe : Gammaℝ (2 * w) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [mul_re]
    norm_num
    linarith
  have restriction := congrArg
    (fun functional : EvenBurnolPhysicalCarrier
        burnolUnscaledCommonGapRadius →L[ℂ] ℂ => functional state)
    (burnolAmbientCompletedMellinEvaluator_restrict coordinate)
  change burnolAmbientCompletedMellinEvaluator coordinate
      (state : BurnolL2) =
    burnolCompletedMellinEvaluator coordinate state at restriction
  unfold burnolDivisionNormalizedPhysicalHeatMellin
    burnolFeatureCompletionAmbientMellinRead
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  change (Gammaℝ (2 * w))⁻¹ *
      mellin (burnolGenericGaussianHeatPairTotal (state : BurnolL2)) w =
    2 * burnolAmbientCompletedMellinEvaluator coordinate (state : BurnolL2)
  dsimp only [coordinate] at bridge
  rw [burnolDivisionCompletedMellinCoordinate_value,
    show (2 * w) / 2 = w by ring] at bridge
  change Gammaℝ (2 * w) * burnolCompletedMellinEvaluator coordinate state =
      (1 / 2 : ℂ) *
        mellin (burnolGenericGaussianHeatPairTotal (state : BurnolL2)) w
    at bridge
  rw [restriction]
  have heatEq :
      mellin (burnolGenericGaussianHeatPairTotal (state : BurnolL2)) w =
        2 * (Gammaℝ (2 * w) *
          burnolCompletedMellinEvaluator coordinate state) := by
    calc
      _ = 2 * ((1 / 2 : ℂ) *
          mellin (burnolGenericGaussianHeatPairTotal (state : BurnolL2)) w) := by
        ring
      _ = 2 * (Gammaℝ (2 * w) *
          burnolCompletedMellinEvaluator coordinate state) := by rw [← bridge]
  rw [heatEq]
  field_simp [gammaNe]

theorem burnolDivisionNormalizedPhysicalHeatMellin_eq_jet
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (k : ℕ)
    (atMostOrder :
      k ≤ generatedRiemannXiZeroOrder owner observation.coordinate)
    (physical : burnolAnalyticComplementDivisionAdditiveState
        observation nontrivial k ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius) :
    EqOn
      (burnolDivisionNormalizedPhysicalHeatMellin
        ⟨burnolAnalyticComplementDivisionAdditiveState
          observation nontrivial k, physical⟩)
      (burnolAnalyticComplementDivisionJet owner observation k)
      burnolPhysicalHeatMellinStrip := by
  let z₀ : ℂ := 3 / 8
  have z₀Mem : z₀ ∈ burnolPhysicalHeatMellinStrip := by
    dsimp only [z₀, burnolPhysicalHeatMellinStrip]
    constructor <;> norm_num
  have rightQuarterNhd : {w : ℂ | 1 / 4 < w.re} ∈ 𝓝 z₀ := by
    apply (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds
    dsimp only [z₀]
    norm_num
  have belowHalfNhd : {w : ℂ | w.re < 1 / 2} ∈ 𝓝 z₀ := by
    apply (isOpen_Iio.preimage Complex.continuous_re).mem_nhds
    dsimp only [z₀]
    norm_num
  have rightOfResonanceNhd :
      {w : ℂ |
        (burnolAnalyticComplementDivisionCenter observation).re < w.re} ∈
        𝓝 z₀ := by
    apply (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds
    dsimp only [z₀, burnolAnalyticComplementDivisionCenter]
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
    norm_num
    linarith
  have eventualEquality :
      burnolDivisionNormalizedPhysicalHeatMellin
          ⟨burnolAnalyticComplementDivisionAdditiveState
            observation nontrivial k, physical⟩ =ᶠ[𝓝 z₀]
        burnolAnalyticComplementDivisionJet owner observation k := by
    filter_upwards [rightQuarterNhd, belowHalfNhd, rightOfResonanceNhd]
      with w rightQuarter belowHalf rightOfResonance
    unfold burnolAnalyticComplementDivisionAdditiveState
    rw [burnolDivisionNormalizedPhysicalHeatMellin_eq_ambientRead
      (observation.coordinate / 2)
      (burnolAnalyticComplementDivisionState observation nontrivial k)
      physical w rightQuarter belowHalf]
    exact burnolAnalyticComplementDivisionState_ambientRead_eq_jet
      observation nontrivial rightHalf w rightQuarter belowHalf
      rightOfResonance k atMostOrder
  exact (burnolDivisionNormalizedPhysicalHeatMellin_analyticOn
      ⟨burnolAnalyticComplementDivisionAdditiveState
        observation nontrivial k, physical⟩).eqOn_of_preconnected_of_eventuallyEq
    (burnolAnalyticComplementDivisionJet_analyticOn observation k)
    burnolPhysicalHeatMellinStrip_isConnected.isPreconnected z₀Mem
    eventualEquality

/-- Every physical preterminal raw division state has a genuine zero
Gaussian heat Mellin integral at the complement center. -/
theorem burnolAnalyticComplementDivisionRawHeatMellin_center_eq_zero_of_physical
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (k : ℕ)
    (beforeOrder :
      k < generatedRiemannXiZeroOrder owner observation.coordinate)
    (physical : burnolAnalyticComplementDivisionAdditiveState
        observation nontrivial k ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius) :
    mellin
        (burnolGenericGaussianHeatPairTotal
          (burnolAnalyticComplementDivisionAdditiveState
            observation nontrivial k))
        (burnolAnalyticComplementDivisionCenter observation) = 0 := by
  let center := burnolAnalyticComplementDivisionCenter observation
  have centerPositive : 0 < center.re := by
    dsimp only [center, burnolAnalyticComplementDivisionCenter]
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
    norm_num
    linarith [observation.coordinate_re_lt_one]
  have centerBelowHalf : center.re < 1 / 2 := by
    dsimp only [center, burnolAnalyticComplementDivisionCenter]
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
    norm_num
    linarith
  have continuation := burnolDivisionNormalizedPhysicalHeatMellin_eq_jet
    observation nontrivial rightHalf k (Nat.le_of_lt beforeOrder) physical
    ⟨centerPositive, centerBelowHalf⟩
  have jetZero := burnolAnalyticComplementDivisionJet_at_eq_zero_of_lt
    observation k beforeOrder
  dsimp only [center] at continuation jetZero
  rw [jetZero] at continuation
  unfold burnolDivisionNormalizedPhysicalHeatMellin at continuation
  have gammaNe :
      Gammaℝ (2 * burnolAnalyticComplementDivisionCenter observation) ≠ 0 := by
    apply Gammaℝ_ne_zero_of_re_pos
    simp only [mul_re]
    norm_num
    exact centerPositive
  exact (mul_eq_zero.mp continuation).resolve_left (inv_ne_zero gammaNe)

/-- Fourier homogeneity turns the preceding center heat zero into exactly
the completed-Mellin zero required by the Sonine division consumer. -/
theorem burnolAnalyticComplementDivisionRawFourierRead_zero_of_physical
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (k : ℕ)
    (beforeOrder :
      k < generatedRiemannXiZeroOrder owner observation.coordinate)
    (physical : burnolAnalyticComplementDivisionAdditiveState
        observation nontrivial k ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius) :
    burnolCompletedMellinEvaluator
        (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
        (evenFaceFourier burnolUnscaledCommonGapRadius
          ⟨burnolAnalyticComplementDivisionAdditiveState
            observation nontrivial k, physical⟩) = 0 := by
  let coordinate :=
    burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let raw : EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius :=
    ⟨burnolAnalyticComplementDivisionAdditiveState
      observation nontrivial k, physical⟩
  have heatZero :=
    burnolAnalyticComplementDivisionRawHeatMellin_center_eq_zero_of_physical
      observation nontrivial rightHalf k beforeOrder physical
  have bridge := burnolGenericHomogeneousGammaMellinBridge
    (evenFaceFourier burnolUnscaledCommonGapRadius raw) coordinate
  have fourier := burnolGenericGaussianFourierHomogeneousIdentity
    raw observation.coordinate
  change Gammaℝ observation.coordinate *
      burnolCompletedMellinEvaluator coordinate
        (evenFaceFourier burnolUnscaledCommonGapRadius raw) =
    (1 / 2 : ℂ) *
      mellin
        (burnolGenericGaussianHeatPairTotal
          (fourierL2 (raw : BurnolL2)))
        (observation.coordinate / 2) at bridge
  rw [fourier] at bridge
  have doubledCenter :
      2 * burnolAnalyticComplementDivisionCenter observation =
        1 - observation.coordinate := by
    unfold burnolAnalyticComplementDivisionCenter
    ring
  rw [← doubledCenter, show
      2 * burnolAnalyticComplementDivisionCenter observation / 2 =
        burnolAnalyticComplementDivisionCenter observation by ring,
    heatZero, mul_zero] at bridge
  have gammaNe : Gammaℝ observation.coordinate ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (lt_trans (by norm_num) rightHalf)
  exact (mul_eq_zero.mp bridge).resolve_left gammaNe

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

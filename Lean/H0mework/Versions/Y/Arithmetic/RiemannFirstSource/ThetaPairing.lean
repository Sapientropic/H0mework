import H0mework.Versions.Y.Arithmetic.RiemannFirstSource.AnalyticComplementPaSourceRealization
import H0mework.Versions.Y.Arithmetic.RiemannResolvent.QuarterCompletionSignedBoundary

/-! Actual modified-WeakFE signed boundaries paired through the original theta source. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped InnerProductSpace Topology
noncomputable section

local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius

local instance thetaPairingAmbientComplete : CompleteSpace Ambient := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The compact generator written directly through its original theta
remainder.  The value at zero retains the first source mean. -/
def burnolCompactCoPoissonThetaRaw
    (source : burnolCompactAnnulusSource) (x : ℝ) : ℂ :=
  if x = 0 then -burnolCompactAdditiveNormalization source
  else (((2 * |x| : ℝ) : ℂ)⁻¹) *
    coPoissonMuntzScaleRemainder source.1 |x|⁻¹

theorem burnolCompactCoPoissonThetaRaw_eq_coSum
    (source : burnolCompactAnnulusSource) (x : ℝ) :
    burnolCompactCoPoissonThetaRaw source x =
      burnolCompactAdditiveCoSum source x := by
  by_cases hx : x = 0
  · subst x
    rw [burnolCompactCoPoissonThetaRaw, if_pos rfl,
      burnolCompactAdditiveCoSum_eq_neg_normalization_of_abs_le_quarter
        source (by norm_num)]
  · have positive : 0 < |x| := abs_pos.mpr hx
    rw [burnolCompactCoPoissonThetaRaw, if_neg hx,
      coPoissonMuntzScaleRemainder_reciprocal_eq_compactAdditiveCoSum
        source positive]
    have absRead : burnolCompactAdditiveCoSum source |x| =
        burnolCompactAdditiveCoSum source x := by
      rcases lt_or_ge x 0 with negative | nonnegative
      · rw [abs_of_neg negative]
        exact burnolCompactAdditiveCoSum_even source x
      · rw [abs_of_nonneg nonnegative]
    rw [absRead]
    push_cast
    field_simp [abs_ne_zero.mpr hx]

/-- At the same exact stage, the modified-WeakFE action is paired directly
with its oriented signed source boundary.  The compact test is inserted by
its actual co-Poisson raw, so neither the action residual nor its Pa
membership occurs as an input. -/
theorem burnolAnalyticComplementExactOrder_signedBoundary_concretePairing
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (source : burnolCompactAnnulusSource) :
    let z := observation.coordinate / 2
    let sourceValue := burnolAnalyticComplementCompletionSource
      observation nontrivial
    let predecessor :=
      generatedRiemannXiZeroOrder owner observation.coordinate - 1
    let previous := quarterFeatureCompletionRightResolventIterate
      z predecessor sourceValue
    let boundary := quarterCompletionRightResolventSignedBoundary
      z previous shift
    let state := burnolAnalyticComplementExactOrderPhysicalState
      observation nontrivial
    inner ℂ (burnolCompactAdditivePhysicalState source)
        (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
            (-shift / 2) state -
          positiveMellinQuarterRightResolventCharacter z shift • state) =
      ∫ x : ℝ, inner ℂ (burnolCompactCoPoissonThetaRaw source x)
        (((positiveMellinQuarterRightResolventCharacter z shift •
            burnolSourceFeatureCompletionPhysicalMap z boundary : Ambient) :
          BurnolL2) x) := by
  dsimp only
  let z := observation.coordinate / 2
  let sourceValue := burnolAnalyticComplementCompletionSource
    observation nontrivial
  let order := generatedRiemannXiZeroOrder owner observation.coordinate
  let predecessor := order - 1
  let previous := quarterFeatureCompletionRightResolventIterate
    z predecessor sourceValue
  let exactValue := burnolAnalyticComplementExactOrderCompletionResolvent
    observation nontrivial
  let boundary := quarterCompletionRightResolventSignedBoundary z previous shift
  let state := burnolAnalyticComplementExactOrderPhysicalState
    observation nontrivial
  let character := positiveMellinQuarterRightResolventCharacter z shift
  let physicalMap := burnolSourceFeatureCompletionPhysicalMap z
  have rightQuarter : 1 / 4 < z.re := by
    dsimp only [z]
    rw [Complex.div_re]
    norm_num
    linarith
  have orderPos : 0 < order :=
    generatedRiemannXiZeroOrder_pos observation nontrivial
  have orderEq : predecessor + 1 = order := Nat.sub_add_cancel orderPos
  have nextEq : quarterFeatureCompletionRightResolvent z previous = exactValue := by
    change quarterFeatureCompletionRightResolvent z
        (quarterFeatureCompletionRightResolventIterate z predecessor sourceValue) =
      quarterFeatureCompletionRightResolventIterate z order sourceValue
    rw [← orderEq]
    rfl
  have physicalEq : physicalMap exactValue = state := by
    rfl
  have actionEq : physicalMap
        (quarterFeatureCompletionTranslation z shift exactValue) =
      evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
        (-shift / 2) state := by
    have generated := burnolAnalyticComplementExactOrder_projectionPreservation
      observation nontrivial shift
    have raw := burnolAnalyticComplementExactOrderPhysicalState_coe_eq_raw
      observation nontrivial rightHalf
    change physicalMap
        (quarterFeatureCompletionTranslation z shift exactValue) =
      burnolEvenAmbientProjection
        (burnolMultiplicativeDilation (-shift / 2) (state : BurnolL2))
    rw [raw]
    exact generated
  have sourceBoundary := quarterCompletionRightResolvent_signedSourceBoundary
    z rightQuarter previous shift
  have physicalBoundary := congrArg physicalMap sourceBoundary
  have physicalBoundary' :
      evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
            (-shift / 2) state - character • state =
        character • physicalMap boundary := by
    simpa only [nextEq, actionEq, physicalEq, map_sub, map_smul,
      character, boundary, physicalMap] using physicalBoundary
  rw [physicalBoundary']
  change inner ℂ
      (burnolCompactAdditiveL2 source)
      ((character • physicalMap boundary : Ambient) : BurnolL2) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [burnolCompactAdditiveL2_coeFn source] with x hsource
  rw [hsource, burnolCompactCoPoissonThetaRaw_eq_coSum]

private theorem sourceCharacter_forward (coordinate : ℂ) (shift : ℝ) :
    positiveMellinQuarterRightResolventCharacter (coordinate / 2) shift =
      reciprocalMellinTranslationCharacter coordinate (shift / 2) := by
  unfold positiveMellinQuarterRightResolventCharacter
    positiveMellinQuarterRightResolventWeight
    reciprocalMellinTranslationCharacter
  congr 1
  push_cast
  ring

private theorem sourceCharacter_inverse (coordinate : ℂ) (shift : ℝ) :
    positiveMellinQuarterRightResolventCharacter (coordinate / 2) (-shift) =
      fullMellinTranslationCharacter coordinate (shift / 2) := by
  unfold positiveMellinQuarterRightResolventCharacter
    positiveMellinQuarterRightResolventWeight fullMellinTranslationCharacter
  congr 1
  push_cast
  ring

/-- The two oriented source boundaries combine before any residual is
introduced.  This is the actual paired source term against the compact
theta test. -/
theorem burnolAnalyticComplementExactOrder_pairedSignedBoundary_concretePairing
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (source : burnolCompactAnnulusSource) :
    let z := observation.coordinate / 2
    let sourceValue := burnolAnalyticComplementCompletionSource
      observation nontrivial
    let predecessor :=
      generatedRiemannXiZeroOrder owner observation.coordinate - 1
    let previous := quarterFeatureCompletionRightResolventIterate
      z predecessor sourceValue
    let state := burnolAnalyticComplementExactOrderPhysicalState
      observation nontrivial
    let inverseBoundary : Ambient :=
      positiveMellinQuarterRightResolventCharacter z (-shift) •
        burnolSourceFeatureCompletionPhysicalMap z
          (quarterCompletionRightResolventSignedBoundary
            z previous (-shift))
    let forwardBoundary : Ambient :=
      positiveMellinQuarterRightResolventCharacter z shift •
        burnolSourceFeatureCompletionPhysicalMap z
          (quarterCompletionRightResolventSignedBoundary z previous shift)
    inner ℂ (burnolCompactAdditivePhysicalState source)
        (burnolPairedAmbientCompression (shift / 2) state -
          pairedMellinTranslationCharacter observation.coordinate
            (shift / 2) • state) =
      ∫ x : ℝ, (1 / 2 : ℂ) *
        (inner ℂ (burnolCompactCoPoissonThetaRaw source x)
            ((inverseBoundary : BurnolL2) x) +
          inner ℂ (burnolCompactCoPoissonThetaRaw source x)
            ((forwardBoundary : BurnolL2) x)) := by
  dsimp only
  let z := observation.coordinate / 2
  let sourceValue := burnolAnalyticComplementCompletionSource
    observation nontrivial
  let predecessor :=
    generatedRiemannXiZeroOrder owner observation.coordinate - 1
  let previous := quarterFeatureCompletionRightResolventIterate
    z predecessor sourceValue
  let state := burnolAnalyticComplementExactOrderPhysicalState
    observation nontrivial
  let test := burnolCompactAdditivePhysicalState source
  let characterInverse :=
    positiveMellinQuarterRightResolventCharacter z (-shift)
  let characterForward :=
    positiveMellinQuarterRightResolventCharacter z shift
  let inverseBoundary : Ambient := characterInverse •
    burnolSourceFeatureCompletionPhysicalMap z
      (quarterCompletionRightResolventSignedBoundary z previous (-shift))
  let forwardBoundary : Ambient := characterForward •
    burnolSourceFeatureCompletionPhysicalMap z
      (quarterCompletionRightResolventSignedBoundary z previous shift)
  have inverseRead :
      inner ℂ test
          (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
              (shift / 2) state - characterInverse • state) =
        ∫ x : ℝ, inner ℂ (burnolCompactCoPoissonThetaRaw source x)
          ((inverseBoundary : BurnolL2) x) := by
    have generated :=
      burnolAnalyticComplementExactOrder_signedBoundary_concretePairing
        observation nontrivial rightHalf (-shift) source
    simpa only [z, sourceValue, predecessor, previous, state, test,
      characterInverse, inverseBoundary, neg_neg, neg_div] using generated
  have forwardRead :
      inner ℂ test
          (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
              (-shift / 2) state - characterForward • state) =
        ∫ x : ℝ, inner ℂ (burnolCompactCoPoissonThetaRaw source x)
          ((forwardBoundary : BurnolL2) x) := by
    simpa only [z, sourceValue, predecessor, previous, state, test,
      characterForward, forwardBoundary] using
        (burnolAnalyticComplementExactOrder_signedBoundary_concretePairing
          observation nontrivial rightHalf shift source)
  have characterEq :
      pairedMellinTranslationCharacter observation.coordinate (shift / 2) =
        (1 / 2 : ℂ) * (characterInverse + characterForward) := by
    dsimp only [characterInverse, characterForward, z]
    rw [sourceCharacter_inverse, sourceCharacter_forward]
    unfold pairedMellinTranslationCharacter
    ring
  have leftRead :
      inner ℂ test
          (burnolPairedAmbientCompression (shift / 2) state -
            pairedMellinTranslationCharacter observation.coordinate
              (shift / 2) • state) =
        (1 / 2 : ℂ) *
          (inner ℂ test
              (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
                (shift / 2) state - characterInverse • state) +
            inner ℂ test
              (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
                (-shift / 2) state - characterForward • state)) := by
    have vectorEq :
        burnolPairedAmbientCompression (shift / 2) state -
            pairedMellinTranslationCharacter observation.coordinate
              (shift / 2) • state =
          (1 / 2 : ℂ) •
            ((evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
                (shift / 2) state - characterInverse • state) +
              (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
                (-shift / 2) state - characterForward • state)) := by
      unfold burnolPairedAmbientCompression
      simp only [smul_apply, add_apply]
      rw [show -(shift / 2) = -shift / 2 by ring]
      rw [characterEq]
      simp only [mul_add, add_smul, smul_add, smul_sub, smul_smul]
      abel
    rw [vectorEq]
    calc
      inner ℂ test ((1 / 2 : ℂ) •
          ((evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
                (shift / 2) state - characterInverse • state) +
            (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
                (-shift / 2) state - characterForward • state))) =
          (1 / 2 : ℂ) * inner ℂ test
            ((evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
                (shift / 2) state - characterInverse • state) +
              (evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius
                (-shift / 2) state - characterForward • state)) :=
        inner_smul_right (𝕜 := ℂ) test _ (1 / 2 : ℂ)
      _ = _ := by rw [inner_add_right]
  have inverseIntegrable : Integrable (fun x : ℝ ↦
      inner ℂ (burnolCompactCoPoissonThetaRaw source x)
        ((inverseBoundary : BurnolL2) x)) := by
    apply (MeasureTheory.L2.integrable_inner
      (burnolCompactAdditiveL2 source) (inverseBoundary : BurnolL2)).congr
    filter_upwards [burnolCompactAdditiveL2_coeFn source] with x hsource
    rw [hsource, burnolCompactCoPoissonThetaRaw_eq_coSum]
  have forwardIntegrable : Integrable (fun x : ℝ ↦
      inner ℂ (burnolCompactCoPoissonThetaRaw source x)
        ((forwardBoundary : BurnolL2) x)) := by
    apply (MeasureTheory.L2.integrable_inner
      (burnolCompactAdditiveL2 source) (forwardBoundary : BurnolL2)).congr
    filter_upwards [burnolCompactAdditiveL2_coeFn source] with x hsource
    rw [hsource, burnolCompactCoPoissonThetaRaw_eq_coSum]
  rw [leftRead, inverseRead, forwardRead, ← integral_add inverseIntegrable forwardIntegrable,
    ← integral_const_mul]

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.Y.Arithmetic.RiemannDivision.AnalyticComplementAmbientMellinEvaluator

/-! # Ambient Mellin read of analytic-complement division states -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter
open SourceGeneratedComplexFeaturePerfectification
open ClozelGeneralizedDual
open ClozelGeneralizedDual.BurnolPhysicalState
open scoped ENNReal InnerProductSpace

noncomputable section

/-- Bounded completed-Mellin read of the raw additive state, before the
physical projection. -/
def burnolFeatureCompletionAmbientMellinRead
    (coordinate : BurnolCompletedMellinCoordinate) (z : ℂ) :
    HilbertAmbient (quarterMellinL2Feature z) →L[ℂ] ℂ :=
  (2 : ℂ) •
    ((burnolAmbientCompletedMellinEvaluator coordinate).comp
      (quarterMellinFeatureCompletionEvenAdditive z))

theorem burnolFeatureCompletionAmbientMellinRead_translation
    (coordinate : BurnolCompletedMellinCoordinate)
    (w z : ℂ) (coordinateValue : coordinate.value = 2 * w)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (shift : ℝ) (nonnegative : 0 ≤ shift)
    (positionGap : quarterMellinFeatureCompletionEvenAdditive z value ∈
      locallyConstantFace burnolUnscaledCommonGapRadius) :
    burnolFeatureCompletionAmbientMellinRead coordinate z
        (quarterFeatureCompletionTranslation z shift value) =
      quarterDilationCharacter w (Real.exp shift) *
        burnolFeatureCompletionAmbientMellinRead coordinate z value := by
  unfold burnolFeatureCompletionAmbientMellinRead
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  rw [quarterMellinFeatureCompletionEvenAdditive_translation]
  have covariance :=
    burnolAmbientCompletedMellinEvaluator_dilation_of_positionGap
      coordinate (-shift / 2)
      (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr nonnegative) (by norm_num))
      (quarterMellinFeatureCompletionEvenAdditive z value) positionGap
  rw [covariance, coordinateValue,
    divisionJet_ambientDilationExp_eq_quarterCharacter]
  ring

theorem burnolFeatureCompletionAmbientMellinRead_rightResolvent
    (coordinate : BurnolCompletedMellinCoordinate)
    (w z : ℂ) (coordinateValue : coordinate.value = 2 * w)
    (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (positionGap : quarterMellinFeatureCompletionEvenAdditive z value ∈
      locallyConstantFace burnolUnscaledCommonGapRadius) :
    burnolFeatureCompletionAmbientMellinRead coordinate z
        (quarterFeatureCompletionRightResolvent z value) =
      -∫ shift : ℝ in Ioi (0 : ℝ),
        positiveMellinQuarterRightResolventWeight z shift *
          quarterDilationCharacter w (Real.exp shift) *
            burnolFeatureCompletionAmbientMellinRead coordinate z value := by
  let read := burnolFeatureCompletionAmbientMellinRead coordinate z
  have integrable := quarterFeatureCompletionRightResolventIntegrand_integrableOn
    z rightQuarter value
  change read (quarterFeatureCompletionRightResolvent z value) = _
  unfold quarterFeatureCompletionRightResolvent
  rw [map_neg, ← read.integral_comp_comm integrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro shift positiveShift
  unfold quarterFeatureCompletionRightResolventIntegrand
  change read
      (positiveMellinQuarterRightResolventWeight z shift •
        quarterFeatureCompletionTranslation z shift value) = _
  rw [map_smul,
    burnolFeatureCompletionAmbientMellinRead_translation
      coordinate w z coordinateValue value shift positiveShift.le positionGap]
  simp only [smul_eq_mul]
  ring

/-- One actual Bochner division of the ambient read is the scalar Cauchy
kernel, with no conditional covariance interface. -/
theorem burnolFeatureCompletionAmbientMellinRead_rightResolvent_eq_scalar
    (coordinate : BurnolCompletedMellinCoordinate)
    (w z : ℂ) (coordinateValue : coordinate.value = 2 * w)
    (rightQuarter : 1 / 4 < z.re)
    (value : HilbertAmbient (quarterMellinL2Feature z))
    (positionGap : quarterMellinFeatureCompletionEvenAdditive z value ∈
      locallyConstantFace burnolUnscaledCommonGapRadius)
    (decay : (((1 / 2 : ℂ) - z - w).re < 0)) :
    burnolFeatureCompletionAmbientMellinRead coordinate z
        (quarterFeatureCompletionRightResolvent z value) =
      (-(1 / (z + w - (1 / 2 : ℂ)))) *
        burnolFeatureCompletionAmbientMellinRead coordinate z value := by
  rw [burnolFeatureCompletionAmbientMellinRead_rightResolvent
    coordinate w z coordinateValue rightQuarter value positionGap]
  rw [integral_mul_const,
    positiveMellinQuarterRightResolvent_scalarKernel z w decay]
  ring

theorem burnolAnalyticComplementDivisionState_ambientRead_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (w : ℂ) (rightQuarter : 1 / 4 < w.re)
    (belowHalf : w.re < 1 / 2) :
    burnolFeatureCompletionAmbientMellinRead
        (burnolDivisionCompletedMellinCoordinate w rightQuarter belowHalf)
        (observation.coordinate / 2)
        (burnolAnalyticComplementDivisionState observation nontrivial 0) =
      burnolAnalyticComplementDivisionJet owner observation 0 w := by
  let coordinate :=
    burnolDivisionCompletedMellinCoordinate w rightQuarter belowHalf
  let source := burnolAnalyticComplementNormalizedSource observation
  have restriction := congrArg
    (fun functional : BurnolPaAmbientCarrier →L[ℂ] ℂ =>
      functional (burnolCompactAdditivePhysicalState source))
    (burnolAmbientCompletedMellinEvaluator_restrict coordinate)
  have sourceRead := four_mul_burnolCompletedMellinEvaluator_eq_quarterMellinRead
    source coordinate
  unfold burnolFeatureCompletionAmbientMellinRead
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  rw [burnolAnalyticComplementDivisionState_zero]
  unfold burnolAnalyticComplementCompletionSource
    burnolSourceQuarterCompletionValue burnolSourceQuarterRelation
  rw [quarterMellinFeatureCompletionEvenAdditive_source]
  have rechart := compactQuarterMellinAdditiveEvenRechart_eq
    (observation.coordinate / 2)
    (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
    (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
    source
  rw [show quarterMellinAdditiveEvenRechart
      (coPoissonQuarterMellinConvergentMap
        (observation.coordinate / 2)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        source.1) = burnolCompactAdditiveL2 source by
      simpa only using rechart,
    map_smul]
  change 2 * (2 * burnolAmbientCompletedMellinEvaluator coordinate
      (burnolCompactAdditiveL2 source)) = _
  change burnolAmbientCompletedMellinEvaluator coordinate
      (burnolCompactAdditiveL2 source) =
    burnolCompletedMellinEvaluator coordinate
      (burnolCompactAdditivePhysicalState source) at restriction
  rw [restriction]
  have coordinateValue : coordinate.value = 2 * w := rfl
  change 4 * burnolCompletedMellinEvaluator coordinate
      (burnolCompactAdditivePhysicalState source) =
    mellin (positiveMellinExtension
      (coPoissonQuarterMellinMap source.1)) (coordinate.value / 2)
    at sourceRead
  rw [coordinateValue, show (2 * w) / 2 = w by ring] at sourceRead
  have initial := burnolAnalyticComplementDivisionJet_zero observation w
    (by simp only [mul_re]; norm_num; linarith)
    (by simp only [mul_re]; norm_num; linarith)
    (by apply ne_of_apply_ne Complex.re
        simp only [mul_re]
        norm_num
        linarith)
    (by apply ne_of_apply_ne Complex.re
        simp only [mul_re, Complex.one_re]
        norm_num
        linarith)
    (by apply Gammaℝ_ne_zero_of_re_pos
        simp only [mul_re]
        norm_num
        linarith)
  calc
    2 * (2 * burnolCompletedMellinEvaluator coordinate
        (burnolCompactAdditivePhysicalState source)) =
      4 * burnolCompletedMellinEvaluator coordinate
        (burnolCompactAdditivePhysicalState source) := by ring
    _ = mellin (positiveMellinExtension
        (coPoissonQuarterMellinMap source.1)) w := sourceRead
    _ = _ := initial.symm

theorem burnolAnalyticComplementDivisionState_ambientRead_eq_jet
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (w : ℂ) (rightQuarter : 1 / 4 < w.re)
    (belowHalf : w.re < 1 / 2)
    (rightOfResonance :
      (burnolAnalyticComplementDivisionCenter observation).re < w.re)
    (k : ℕ)
    (atMostOrder :
      k ≤ generatedRiemannXiZeroOrder owner observation.coordinate) :
    burnolFeatureCompletionAmbientMellinRead
        (burnolDivisionCompletedMellinCoordinate w rightQuarter belowHalf)
        (observation.coordinate / 2)
        (burnolAnalyticComplementDivisionState observation nontrivial k) =
      burnolAnalyticComplementDivisionJet owner observation k w := by
  induction k with
  | zero =>
      exact burnolAnalyticComplementDivisionState_ambientRead_zero
        observation nontrivial w rightQuarter belowHalf
  | succ k inductionHypothesis =>
      have beforeOrder :
          k < generatedRiemannXiZeroOrder owner observation.coordinate := by
        omega
      have previous := inductionHypothesis (by omega)
      have zRightQuarter :
          1 / 4 < (observation.coordinate / 2).re := by
        rw [Complex.div_re]
        norm_num
        linarith
      have positionGap :=
        burnolAnalyticComplementDivisionAdditiveState_positionGap
          observation nontrivial rightHalf k
      have decay :
          (((1 / 2 : ℂ) - observation.coordinate / 2 - w).re < 0) := by
        change (burnolAnalyticComplementDivisionCenter observation).re -
          w.re < 0
        linarith
      rw [burnolAnalyticComplementDivisionState_succ,
        burnolFeatureCompletionAmbientMellinRead_rightResolvent_eq_scalar
          (burnolDivisionCompletedMellinCoordinate w rightQuarter belowHalf)
          w (observation.coordinate / 2) rfl zRightQuarter
          (burnolAnalyticComplementDivisionState observation nontrivial k)
          positionGap decay,
        previous]
      exact burnolAnalyticComplementDivisionJet_succ observation k
        beforeOrder w (by
          intro resonant
          have realEq := congrArg Complex.re resonant
          linarith)

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

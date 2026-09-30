import H0mework.Versions.Y.Arithmetic.RemainderSource.ResolventBoundary
import H0mework.Versions.Y.Arithmetic.RiemannFirstSource.Remainder

/-! The full exact-order source and its Pa complement share the original comb-remainder action. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private def sourceRead (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  (1 / 2 : ℂ) • innerSL ℂ (star (burnolRemainderL2Kernel test))

private theorem sourceRead_eq (test : SchwartzMap ℝ ℂ) (source : BurnolL2) :
    sourceRead test source = burnolRemainderSourceRead source test := by
  change (1 / 2 : ℂ) * inner ℂ (star (burnolRemainderL2Kernel test)) source =
    (1 / 2 : ℂ) * inner ℂ (star source) (burnolRemainderL2Kernel test)
  rw [L2.inner_def, L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (burnolRemainderL2Kernel test), Lp.coeFn_star source]
    with x hkernel hsource
  rw [hkernel, hsource]
  simp only [RCLike.inner_apply, Pi.star_apply, starRingEnd_apply, star_star]
  exact mul_comm _ _

private def valueRead (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ :=
  innerSL ℂ (star (test.toLp 2 volume))

private theorem valueRead_eq (test : SchwartzMap ℝ ℂ) (value : BurnolL2) :
    valueRead test value = (Lp.toTemperedDistributionCLM ℂ volume 2 value) test := by
  change inner ℂ (star (test.toLp 2 volume)) value = _
  rw [L2.inner_def, Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star (test.toLp 2 volume), test.coeFn_toLp 2 volume]
    with x hstar htest
  rw [hstar, Pi.star_apply, htest]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_star, smul_eq_mul]
  exact mul_comm _ _

private theorem schwartzDilation_toLp (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    (burnolRemainderSchwartzDilation shift test).toLp 2 volume =
      burnolMultiplicativeDilation shift (test.toLp 2 volume) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [(burnolRemainderSchwartzDilation shift test).coeFn_toLp 2 volume,
    burnolMultiplicativeDilation_coeFn shift (test.toLp 2 volume),
    qmp.ae (test.coeFn_toLp 2 volume)] with x hleft hright htest
  rw [hleft, hright]
  unfold burnolL2RawNormalizedDilation
  rw [htest]
  rfl

private theorem valueRead_dilation (shift : ℝ) (test : SchwartzMap ℝ ℂ)
    (value : BurnolL2) :
    valueRead (burnolRemainderSchwartzDilation (-shift) test) value =
      valueRead test (burnolMultiplicativeDilation shift value) := by
  change inner ℂ (star ((burnolRemainderSchwartzDilation (-shift) test).toLp 2 volume))
    value = _
  rw [schwartzDilation_toLp, burnolMultiplicativeDilation_star,
    (burnolMultiplicativeDilation (-shift)).inner_map_eq_flip,
    ← burnolMultiplicativeDilation_neg_eq_symm (-shift), neg_neg]
  rfl

private theorem sourceRead_action {source value : BurnolL2}
    (realizes : ∀ test : SchwartzMap ℝ ℂ, sourceRead test source = valueRead test value)
    (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    sourceRead test (burnolMultiplicativeDilation shift source) =
      valueRead test (burnolMultiplicativeDilation shift value) := by
  rw [sourceRead_eq, burnolRemainderSourceRead_dilation, ← sourceRead_eq,
    realizes, valueRead_dilation]

private theorem sourceRead_resolvent {source value : BurnolL2}
    (realizes : ∀ test : SchwartzMap ℝ ℂ, sourceRead test source = valueRead test value)
    (z : ℂ)
    (sourceIntegrable : IntegrableOn (burnolDirectRightResolventIntegrand z source) (Ioi 0))
    (valueIntegrable : IntegrableOn (burnolDirectRightResolventIntegrand z value) (Ioi 0))
    (test : SchwartzMap ℝ ℂ) :
    sourceRead test (burnolDirectRightResolvent z source) =
      valueRead test (burnolDirectRightResolvent z value) := by
  unfold burnolDirectRightResolvent
  rw [map_neg, map_neg, ← (sourceRead test).integral_comp_comm sourceIntegrable,
    ← (valueRead test).integral_comp_comm valueIntegrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro shift _
  dsimp only [burnolDirectRightResolventIntegrand]
  rw [map_smul, map_smul, sourceRead_action realizes]

/-- Apply the actual resolvent to the compact seed itself, before either
physical projection. The iterates are full L² sources, not annulus claims. -/
def burnolCompleteRemainderSource (z : ℂ) (source : burnolCompactAnnulusSource) :
    Nat → BurnolL2
  | 0 => (2 : ℂ) • burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)
  | order + 1 => burnolDirectRightResolvent z (burnolCompleteRemainderSource z source order)

theorem burnolCompleteRemainderSource_realizes (z : ℂ)
    (rightQuarter : 1 / 4 < z.re) (positive : 0 < z.re) (belowHalf : z.re < 1 / 2)
    (source : burnolCompactAnnulusSource) (order : Nat) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolCompleteRemainderSource z source order) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (quarterMellinFeatureCompletionEvenAdditive z
          (quarterFeatureCompletionRightResolventIterate z order
            (burnolSourceQuarterCompletionValue source z positive belowHalf)))) test := by
  rw [← sourceRead_eq, ← valueRead_eq]
  induction order generalizing test with
  | zero =>
      change sourceRead test ((2 : ℂ) • burnolMobiusSourceL2
          (burnolCompactAdditivePhysicalState source)) =
        valueRead test (quarterMellinFeatureCompletionEvenAdditive z
          (burnolSourceQuarterCompletionValue source z positive belowHalf))
      unfold burnolSourceQuarterCompletionValue burnolSourceQuarterRelation
      rw [quarterMellinFeatureCompletionEvenAdditive_source,
        compactQuarterMellinAdditiveEvenRechart_eq, map_smul, map_smul]
      congr 1
      rw [sourceRead_eq, burnolRemainderSourceRead_compact, valueRead_eq,
        Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [burnolCompactAdditiveL2_coeFn source] with x hx
      rw [hx]
      rfl
  | succ order previous =>
      change sourceRead test (burnolDirectRightResolvent z
          (burnolCompleteRemainderSource z source order)) =
        valueRead test (quarterMellinFeatureCompletionEvenAdditive z
          (quarterFeatureCompletionRightResolvent z
            (quarterFeatureCompletionRightResolventIterate z order
              (burnolSourceQuarterCompletionValue source z positive belowHalf))))
      rw [quarterMellinFeatureCompletionEvenAdditive_rightResolvent_eq_direct z rightQuarter]
      exact sourceRead_resolvent previous z
        (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter _)
        (burnolDirectRightResolventIntegrand_integrableOn z rightQuarter _) test

theorem burnolExactOrderRemainderSource_realizes {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead
      (burnolCompleteRemainderSource (observation.coordinate / 2)
        (burnolAnalyticComplementNormalizedSource observation)
        (generatedRiemannXiZeroOrder owner observation.coordinate)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial : BurnolL2)) test := by
  rw [burnolAnalyticComplementExactOrderPhysicalState_coe_eq_raw
    observation nontrivial rightHalf]
  apply burnolCompleteRemainderSource_realizes
  rw [Complex.div_re]
  norm_num
  linarith

local instance fullRemainderAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolPaResidualCompleteSource {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) : BurnolL2 :=
  burnolCompleteRemainderSource (observation.coordinate / 2)
      (burnolAnalyticComplementNormalizedSource observation)
      (generatedRiemannXiZeroOrder owner observation.coordinate) -
    burnolMobiusSourceL2 (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial))

/-- The original nonzero Pa-complement state is realized by the difference
of its full resolvent source and its actual finite-window Pa source. -/
theorem burnolPaResidualCompleteSource_realizes {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolPaResidualCompleteSource observation nontrivial) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        ((burnolAnalyticComplementExactOrderPaPositionResidualState observation nontrivial :
          BurnolPaAmbientCarrier) : BurnolL2)) test := by
  let state := burnolAnalyticComplementExactOrderPhysicalState observation nontrivial
  let projection := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection state
  have full := burnolExactOrderRemainderSource_realizes observation nontrivial rightHalf test
  rw [← sourceRead_eq, ← valueRead_eq] at full
  have projected : sourceRead test (burnolMobiusSourceL2 projection) =
      valueRead test (projection : BurnolL2) := by
    rw [sourceRead_eq, valueRead_eq, Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_apply]
    simpa only [smul_eq_mul] using burnolRemainderSourceRead_Pa projection
      (Submodule.starProjection_apply_mem _ _) test
  have residualValue :
      (burnolAnalyticComplementExactOrderPaPositionResidualState observation nontrivial :
        BurnolPaAmbientCarrier) = state - projection := by
    exact Submodule.starProjection_orthogonal_val
      (K := burnolCompactCoPoissonClosedRange.toSubmodule) state
  rw [← sourceRead_eq, ← valueRead_eq, burnolPaResidualCompleteSource, map_sub, full]
  change valueRead test (state : BurnolL2) - sourceRead test (burnolMobiusSourceL2 projection) = _
  rw [projected, ← map_sub, residualValue]
  rfl

theorem burnolPaResidualCompleteSource_action {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolMultiplicativeDilation shift
        (burnolPaResidualCompleteSource observation nontrivial)) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolMultiplicativeDilation shift
          ((burnolAnalyticComplementExactOrderPaPositionResidualState observation nontrivial :
            BurnolPaAmbientCarrier) : BurnolL2))) test := by
  rw [← sourceRead_eq, ← valueRead_eq]
  apply sourceRead_action
  intro test
  rw [sourceRead_eq, valueRead_eq]
  exact burnolPaResidualCompleteSource_realizes observation nontrivial rightHalf test

/-- Source-native current: the actual predecessor's finite orbit write,
minus the actual Pa source's character difference. -/
def burnolPaResidualNativeSourceCurrent {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (shift : ℝ) : BurnolL2 :=
  let z := observation.coordinate / 2
  let character := positiveMellinQuarterRightResolventCharacter z shift
  let previous := burnolCompleteRemainderSource z
    (burnolAnalyticComplementNormalizedSource observation)
    (generatedRiemannXiZeroOrder owner observation.coordinate - 1)
  let projectionSource := burnolMobiusSourceL2
    (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial))
  character • burnolDirectRightResolventSignedBoundary z previous shift -
    (burnolMultiplicativeDilation (-shift / 2) projectionSource - character • projectionSource)

theorem burnolPaResidualNativeSourceCurrent_generated {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) :
    burnolMultiplicativeDilation (-shift / 2)
        (burnolPaResidualCompleteSource observation nontrivial) -
      positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift •
        burnolPaResidualCompleteSource observation nontrivial =
      burnolPaResidualNativeSourceCurrent observation nontrivial shift := by
  let z := observation.coordinate / 2
  let source := burnolAnalyticComplementNormalizedSource observation
  let order := generatedRiemannXiZeroOrder owner observation.coordinate
  have rightQuarter : 1 / 4 < z.re := by
    dsimp only [z]
    rw [Complex.div_re]
    norm_num
    linarith
  have orderEq : order - 1 + 1 = order :=
    Nat.sub_add_cancel (generatedRiemannXiZeroOrder_pos observation nontrivial)
  have actualStep := burnolDirectRightResolvent_sourceBoundary z rightQuarter
    (burnolCompleteRemainderSource z source (order - 1)) shift
  have top : burnolDirectRightResolvent z
      (burnolCompleteRemainderSource z source (order - 1)) =
        burnolCompleteRemainderSource z source order := by
    rw [← orderEq]
    rfl
  rw [top] at actualStep
  unfold burnolPaResidualCompleteSource burnolPaResidualNativeSourceCurrent
  dsimp only
  rw [map_sub, smul_sub]
  change _ = positiveMellinQuarterRightResolventCharacter z shift •
    burnolDirectRightResolventSignedBoundary z (burnolCompleteRemainderSource z source (order - 1)) shift - _
  rw [← actualStep]
  module

theorem burnolPaResidualNativeSourceCurrent_actualRead {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolPaResidualNativeSourceCurrent observation nontrivial shift) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolMultiplicativeDilation (-shift / 2)
            ((burnolAnalyticComplementExactOrderPaPositionResidualState observation nontrivial :
              BurnolPaAmbientCarrier) : BurnolL2) -
          positiveMellinQuarterRightResolventCharacter (observation.coordinate / 2) shift •
            ((burnolAnalyticComplementExactOrderPaPositionResidualState observation nontrivial :
              BurnolPaAmbientCarrier) : BurnolL2))) test := by
  rw [← burnolPaResidualNativeSourceCurrent_generated observation nontrivial rightHalf shift,
    ← sourceRead_eq, map_sub, map_smul, sourceRead_eq, sourceRead_eq,
    burnolPaResidualCompleteSource_action observation nontrivial rightHalf,
    burnolPaResidualCompleteSource_realizes observation nontrivial rightHalf,
    map_sub, map_smul, sub_apply, smul_apply]

def burnolRemainderSourceReadCLM (test : SchwartzMap ℝ ℂ) : BurnolL2 →L[ℂ] ℂ := sourceRead test

theorem burnolRemainderSourceReadCLM_apply (test : SchwartzMap ℝ ℂ) (source : BurnolL2) :
    burnolRemainderSourceReadCLM test source = burnolRemainderSourceRead source test :=
  sourceRead_eq test source

theorem burnolRemainderSourceRead_bochner (μ : Measure ℝ) (sources values : ℝ → BurnolL2)
    (sourceIntegrable : Integrable sources μ) (valueIntegrable : Integrable values μ)
    (realizes : ∀ᵐ u ∂μ, ∀ test : SchwartzMap ℝ ℂ,
      burnolRemainderSourceRead (sources u) test =
        (Lp.toTemperedDistributionCLM ℂ volume 2 (values u)) test)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (∫ u, sources u ∂μ) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (∫ u, values u ∂μ)) test := by
  rw [← sourceRead_eq, ← valueRead_eq,
    ← (sourceRead test).integral_comp_comm sourceIntegrable,
    ← (valueRead test).integral_comp_comm valueIntegrable]
  apply integral_congr_ae
  filter_upwards [realizes] with u hu
  rw [sourceRead_eq, valueRead_eq]
  exact hu test

theorem burnolRemainderRealization_dilation (source value : BurnolL2)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) (shift : ℝ) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolMultiplicativeDilation shift source) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolMultiplicativeDilation shift value)) test := by
  rw [← sourceRead_eq, ← valueRead_eq]
  apply sourceRead_action
  intro ψ
  rw [sourceRead_eq, valueRead_eq]
  exact realizes ψ

/-- Bochner averaging keeps the original source/readout action square. -/
theorem burnolRemainderSourceRead_dilation_average (weight shift : ℝ → ℝ)
    (source value : BurnolL2)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test)
    (sourceIntegrable : Integrable (fun h => weight h • burnolMultiplicativeDilation (shift h) source))
    (valueIntegrable : Integrable (fun h => weight h • burnolMultiplicativeDilation (shift h) value))
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (∫ h : ℝ, weight h • burnolMultiplicativeDilation (shift h) source) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (∫ h : ℝ, weight h • burnolMultiplicativeDilation (shift h) value)) test := by
  rw [← sourceRead_eq, ← valueRead_eq]
  change (sourceRead test).restrictScalars ℝ (∫ h : ℝ,
    weight h • burnolMultiplicativeDilation (shift h) source) = _
  change _ = (valueRead test).restrictScalars ℝ (∫ h : ℝ,
    weight h • burnolMultiplicativeDilation (shift h) value)
  rw [← ((sourceRead test).restrictScalars ℝ).integral_comp_comm sourceIntegrable,
    ← ((valueRead test).restrictScalars ℝ).integral_comp_comm valueIntegrable]
  apply integral_congr_ae
  filter_upwards with h
  rw [map_smul, map_smul]
  apply congrArg (fun current : ℂ => weight h • current)
  exact sourceRead_action (by
    intro ψ
    rw [sourceRead_eq, valueRead_eq]
    exact realizes ψ) (shift h) test

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

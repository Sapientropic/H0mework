import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.UnitResponseSource
import H0mework.Versions.Y.Arithmetic.RiemannFirstSource.FirstFeedback

/-! The same zero occurrence realizes the unit response and the retained internal source on the original physical face. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolRemainderRealization_even (source value : BurnolL2)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead source test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) : reflectL2 value = value := by
  have dual := burnolRemainderRealization_fourier source value realizes
  have twice := burnolRemainderRealization_fourier (burnolTateReciprocalL2 source) (fourierL2 value) dual
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  have exactRead := twice test
  rw [burnolTateReciprocalL2_involutive, fourierL2_fourierL2, realizes] at exactRead
  exact exactRead.symm

theorem burnolTateReciprocal_reflect (source : BurnolL2) :
    burnolTateReciprocalL2 (reflectL2 source) = reflectL2 (burnolTateReciprocalL2 source) := by
  have reflected := Lp.coeFn_compMeasurePreserving source negMeasurePreserving
  change (reflectL2 source : ℝ → ℂ) =ᵐ[volume] fun x => source (-x) at reflected
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp (reflectL2 source))
    ((Lp.memLp (reflectL2 source)).ae_eq reflected) reflected
  apply Lp.ext
  filter_upwards [burnolTateReciprocalL2_coeFn (reflectL2 source), pulled,
    Lp.coeFn_compMeasurePreserving (burnolTateReciprocalL2 source) negMeasurePreserving,
    negMeasurePreserving.quasiMeasurePreserving.ae (burnolTateReciprocalL2_coeFn source)]
      with x direct rawAt reflectionAt sourceAt
  rw [direct, rawAt]
  have reflection : reflectL2 (burnolTateReciprocalL2 source) x = burnolTateReciprocalL2 source (-x) := reflectionAt
  rw [reflection, sourceAt]
  simp only [burnolTateReciprocalRaw, abs_neg, neg_inv]

theorem burnolTateMobiusSource_innerGap (value : BurnolPaAmbientCarrier) :
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 value) : ℝ → ℂ) =ᵐ[
      volume.restrict (symmetricInterval (1 / 4 : ℝ))] fun _ => 0 := by
  let source := burnolMobiusSourceL2 value
  let raw : ℝ → ℂ := (symmetricInterval (4 : ℝ)).indicator (fun x => burnolMobiusWindowSourceRead value x)
  have sourceRead : (source : ℝ → ℂ) =ᵐ[volume] raw :=
    burnolRadiusZeroExtension_coe (burnolMobiusWindowSourceRead value)
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp source)
    ((Lp.memLp source).ae_eq sourceRead) sourceRead
  filter_upwards [ae_restrict_of_ae (burnolTateReciprocalL2_coeFn source), ae_restrict_of_ae pulled,
    ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ)),
    ae_restrict_of_ae (volume.ae_ne (1 / 4 : ℝ)), ae_restrict_of_ae (volume.ae_ne (-(1 / 4 : ℝ)))]
      with x direct rawAt inside notUpper notLower
  rw [direct, rawAt]
  by_cases zero : x = 0
  · simp [zero, burnolTateReciprocalRaw]
  · have strict : |x| < (1 / 4 : ℝ) :=
      abs_lt.mpr ⟨lt_of_le_of_ne inside.1 notLower.symm, lt_of_le_of_ne inside.2 notUpper⟩
    have inverseOutside : (4 : ℝ) < |x⁻¹| := by
      simpa only [abs_inv, one_div, inv_inv] using
        (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 1 / 4) (abs_pos.mpr zero)).mpr strict
    have outside : x⁻¹ ∉ symmetricInterval (4 : ℝ) :=
      fun belongs => not_le_of_gt inverseOutside (abs_le.mpr belongs)
    simp only [burnolTateReciprocalRaw, raw, indicator_of_notMem outside, mul_zero]

theorem burnolMobiusSource_realization_physical (original : BurnolPaAmbientCarrier) (value : BurnolL2)
    (realizes : ∀ test : SchwartzMap ℝ ℂ, burnolRemainderSourceRead (burnolMobiusSourceL2 original) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) test) :
    value ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  have evenSource := burnolMobiusSourceL2_even original
  have dualEven : reflectL2 (burnolTateReciprocalL2 (burnolMobiusSourceL2 original)) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2 original) := by
    rw [← burnolTateReciprocal_reflect, evenSource]
  exact ⟨⟨burnolRemainderRealization_positionGap _ _ evenSource (burnolMobiusSourceL2_innerGap original) realizes,
    burnolRemainderRealization_positionGap _ _ dualEven (burnolTateMobiusSource_innerGap original)
      (burnolRemainderRealization_fourier _ _ realizes)⟩,
    mem_evenL2ClosedFace_iff.mpr (burnolRemainderRealization_even _ _ realizes)⟩

def burnolFirstInternalValue {owner : GlobalGermOwner} (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : BurnolL2 :=
  ((burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
    (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf) : BurnolPaAmbientCarrier) : BurnolL2) -
    burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 4

theorem burnolFirstInternalValue_realizes {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolMobiusSourceL2
      (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
        (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf))) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolFirstInternalValue observation nontrivial rightHalf)) test := by
  have whole := burnolAnalyticComplementFirstPaSource_readback observation nontrivial rightHalf test
  dsimp only at whole
  rw [← burnolRemainderSourceReadCLM_apply, map_add,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply, burnolOriginalUnitTail_realizes] at whole
  rw [burnolFirstInternalValue, map_sub, sub_apply]
  apply eq_sub_of_add_eq
  simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul] using whole

theorem burnolFirstInternalValue_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolFirstInternalValue observation nontrivial rightHalf ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius :=
  burnolMobiusSource_realization_physical _ _ (burnolFirstInternalValue_realizes observation nontrivial rightHalf)

theorem burnolZeroOwnedUnitTailResponse_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 4 ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let residue := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
    (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf)
  have reconstructed : burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 4 =
      (residue : BurnolL2) - burnolFirstInternalValue observation nontrivial rightHalf := by
    unfold burnolFirstInternalValue
    change _ = (residue : BurnolL2) - ((residue : BurnolL2) - _)
    abel
  rw [reconstructed]
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.sub_mem residue.property
    (burnolFirstInternalValue_physical observation nontrivial rightHalf)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

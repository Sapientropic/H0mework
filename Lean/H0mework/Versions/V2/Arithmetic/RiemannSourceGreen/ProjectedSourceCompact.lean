import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.CutoffComplete
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.Algebra
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.UnitResponseSource

/-! Every original compact source generates its weighted Pa correction and its literal Mellin tail coefficient. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolCompactFirstResponse_split (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    (2 : ℂ) • burnolDirectRightResolvent (coordinate.value / 2) (burnolCompactAdditiveL2 source) =
      burnolWeightedReciprocalStepWave (1 / 4) 4 (burnolFirstSourceCoefficient coordinate source)
        (burnolFirstSourceCoefficientSlope coordinate source) +
      burnolFirstSourceMellinCoefficient coordinate.value source • burnolUnitTailResponse coordinate 4 := by
  have rq : 1 / 4 < (coordinate.value / 2).re := by
    rw [Complex.div_re]; norm_num; linarith [coordinate.rightHalf]
  have pos : 0 < (coordinate.value / 2).re := by linarith
  have bh : (coordinate.value / 2).re < 1 / 2 := by
    rw [Complex.div_re]; norm_num; linarith [coordinate.belowOne]
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  have full := burnolCompleteRemainderSource_realizes (coordinate.value / 2) rq pos bh source 1 test
  have read : burnolRemainderSourceRead
      (burnolCompleteRemainderSource (coordinate.value / 2) source 1) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2
        ((2 : ℂ) • burnolDirectRightResolvent (coordinate.value / 2)
          (burnolCompactAdditiveL2 source))) test := by
    rw [quarterFeatureCompletionRightResolventIterate,
      quarterMellinFeatureCompletionEvenAdditive_rightResolvent_eq_direct _ rq] at full
    unfold burnolSourceQuarterCompletionValue burnolSourceQuarterRelation at full
    rw [quarterFeatureCompletionRightResolventIterate,
      quarterMellinFeatureCompletionEvenAdditive_source,
      compactQuarterMellinAdditiveEvenRechart_eq,
      burnolDirectRightResolvent_smul] at full
    exact full
  change (Lp.toTemperedDistributionCLM ℂ volume 2
    ((2 : ℂ) • burnolDirectRightResolvent (coordinate.value / 2)
      (burnolCompactAdditiveL2 source))) test = _
  rw [← read, burnolCompleteFirstSource_eq_weighted_add_tail, ← burnolRemainderSourceReadCLM_apply,
    map_add, map_smul, burnolRemainderSourceReadCLM_apply,
    burnolRemainderSourceReadCLM_apply, burnolOriginalUnitTail_realizes,
    burnolWeightedReciprocalStepSource_realizes (1 / 4) 4 _ _ (by norm_num) (by norm_num) (by norm_num)
      (burnolFirstSourceCoefficientSlope_continuous _ _).continuousOn]
  simp only [map_add, map_smul, add_apply, smul_apply]
  rfl

theorem burnolCompactFirstResponse_correction (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    burnolDirectRightResolvent (coordinate.value / 2) (burnolCompactAdditiveL2 source) -
      (burnolFirstSourceMellinCoefficient coordinate.value source / 2) • burnolUnitTailResponse coordinate 4 ∈
        burnolOriginalPaInL2 := by
  have split := burnolCompactFirstResponse_split coordinate source
  have same :
      burnolDirectRightResolvent (coordinate.value / 2) (burnolCompactAdditiveL2 source) -
        (burnolFirstSourceMellinCoefficient coordinate.value source / 2) • burnolUnitTailResponse coordinate 4 =
      (1 / 2 : ℂ) • burnolWeightedReciprocalStepWave (1 / 4) 4
        (burnolFirstSourceCoefficient coordinate source) (burnolFirstSourceCoefficientSlope coordinate source) := by
    calc
      _ = (1 / 2 : ℂ) • ((2 : ℂ) • burnolDirectRightResolvent
        (coordinate.value / 2) (burnolCompactAdditiveL2 source)) -
        (burnolFirstSourceMellinCoefficient coordinate.value source / 2) • burnolUnitTailResponse coordinate 4 := by module
      _ = _ := by rw [split]; module
  rw [same]
  exact burnolOriginalPaInL2.smul_mem _ (burnolFirstSourceWeightedWave_inPa coordinate source)

/-- The actual Tate sibling of the recovered compact source is the original Schwartz source. -/
theorem burnolCompactPa_tate_source (source : burnolCompactAnnulusSource) :
    burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) =
      source.1.toLp 2 volume := by
  have seed := burnolCompleteRemainderSource_tateSeed (3 / 8) source
  change burnolTateReciprocalL2 ((2 : ℂ) • burnolMobiusSourceL2
    (burnolCompactAdditivePhysicalState source)) = (2 : ℂ) • source.1.toLp 2 volume at seed
  rw [map_smul] at seed
  have scaled := congrArg (fun v : BurnolL2 => (1 / 2 : ℂ) • v) seed
  simpa only [smul_smul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] using scaled

def burnolPaResolventSourceCoefficient (coordinate : BurnolCompletedMellinCoordinate) :
    BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  (2 : ℂ) • (burnolMellinTailEvaluator coordinate.value coordinate.rightHalf).comp
    (burnolTateReciprocalL2.comp burnolMobiusSourceL2)

theorem burnolPaResolventSourceCoefficient_compact (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source) =
      burnolFirstSourceMellinCoefficient coordinate.value source / 2 := by
  change (2 : ℂ) * burnolMellinTailEvaluator coordinate.value coordinate.rightHalf
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source))) = _
  rw [burnolCompactPa_tate_source, burnolMellinTailEvaluator_eq_integral]
  have rawIntegral :
      (∫ t : ℝ in Ioi burnolUnscaledCommonGapRadius,
        (t : ℂ) ^ (-coordinate.value) * source.1.toLp 2 volume t) =
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-coordinate.value) * source.1 t := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [source.1.coeFn_toLp 2 volume] with t ht
    by_cases large : burnolUnscaledCommonGapRadius < t
    · rw [indicator_of_mem (show t ∈ Ioi burnolUnscaledCommonGapRadius from large),
        indicator_of_mem (show t ∈ Ioi (0 : ℝ) by
        have qpos : 0 < burnolUnscaledCommonGapRadius := by norm_num [burnolUnscaledCommonGapRadius]
        exact qpos.trans large), ht]
    · rw [indicator_of_notMem (show t ∉ Ioi burnolUnscaledCommonGapRadius from large)]
      by_cases positive : 0 < t
      · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from positive), source.2.2.1 t (by
          rw [abs_of_pos positive]
          exact le_of_not_gt large), mul_zero]
      · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from positive)]
  rw [rawIntegral]
  unfold burnolFirstSourceMellinCoefficient coPoissonMuntzEvenSourceMellin mellin
  have integrand : (fun t : ℝ =>
      (t : ℂ) ^ (1 - coordinate.value - 1) • coPoissonMuntzEvenSource source.1 t) =
      fun t : ℝ => (2 : ℂ) * ((t : ℂ) ^ (-coordinate.value) * source.1 t) := by
    funext t
    rw [show 1 - coordinate.value - 1 = -coordinate.value by ring]
    simp only [coPoissonMuntzEvenSource, source.2.1 t, smul_eq_mul]
    ring
  rw [integrand, integral_const_mul]
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

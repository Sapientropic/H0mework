import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.ProbeCutoffValue

/-! Tail readouts of the actual physical cutoff and the original Pa inverse source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem source_tail_cutoff_inside
    (coordinate : BurnolCompletedMellinCoordinate) (t : ℝ) (positive : 0 < t)
    (b : ℝ) (inside : t ≤ b) (value : BurnolL2) :
    burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf
      (originalPhysicalCutoff b value) =
      burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf value -
        burnolRadiusMellinTailEvaluator b (lt_of_lt_of_le positive inside)
          coordinate.value coordinate.rightHalf value := by
  simp only [burnolRadiusMellinTailEvaluator_eq_integral]
  rw [← setIntegral_sdiff measurableSet_Ioi
    (burnolRadiusMellinWeight_integrableOn_tail t positive coordinate.value
      coordinate.rightHalf value) (Ioi_subset_Ioi inside), Ioi_sdiff_Ioi]
  calc
    (∫ x : ℝ in Ioi t, (x : ℂ) ^ (-coordinate.value) * originalPhysicalCutoff b value x) =
        ∫ x : ℝ in Ioi t,
          (Iic b).indicator (fun x : ℝ => (x : ℂ) ^ (-coordinate.value) * value x) x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (originalPhysicalCutoff_coeFn b value),
        ae_restrict_mem measurableSet_Ioi] with x cutoffRead hx
      rw [cutoffRead]
      by_cases below : x ≤ b
      · have symmetric : x ∈ symmetricInterval b := by
          change -b ≤ x ∧ x ≤ b
          exact ⟨by linarith [show t < x from hx], below⟩
        rw [Set.indicator_of_mem symmetric,
          Set.indicator_of_mem (show x ∈ Iic b from below)]
      · have notSymmetric : x ∉ symmetricInterval b := fun h => below h.2
        rw [Set.indicator_of_notMem notSymmetric,
          Set.indicator_of_notMem (show x ∉ Iic b from below), mul_zero]
    _ = ∫ x : ℝ in Ioc t b, (x : ℂ) ^ (-coordinate.value) * value x := by
      rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]

theorem source_tail_cutoff_outside
    (coordinate : BurnolCompletedMellinCoordinate) (t : ℝ) (positive : 0 < t)
    (b : ℝ) (outside : b ≤ t) (value : BurnolL2) :
    burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf
      (originalPhysicalCutoff b value) = 0 := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae (originalPhysicalCutoff_coeFn b value),
    ae_restrict_mem measurableSet_Ioi] with x cutoffRead hx
  have notSymmetric : x ∉ symmetricInterval b := by
    intro h
    exact (not_le_of_gt (lt_of_le_of_lt outside hx)) h.2
  simp only [cutoffRead, Set.indicator_of_notMem notSymmetric, mul_zero, Pi.zero_apply]

theorem original_source_tail_below_quarter
    (coordinate : BurnolCompletedMellinCoordinate) (t : ℝ) (positive : 0 < t)
    (below : t ≤ 1 / 4) (p : BurnolPaAmbientCarrier) :
    burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
      burnolRadiusMellinTailEvaluator (1 / 4) (by norm_num)
        coordinate.value coordinate.rightHalf
          (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) := by
  apply sub_eq_zero.mp
  simp only [burnolRadiusMellinTailEvaluator_eq_integral]
  rw [← setIntegral_sdiff measurableSet_Ioi
    (burnolRadiusMellinWeight_integrableOn_tail t positive coordinate.value
      coordinate.rightHalf (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))
    (Ioi_subset_Ioi below), Ioi_sdiff_Ioi]
  apply integral_eq_zero_of_ae
  have restricted : Ioc t (1 / 4 : ℝ) ⊆ symmetricInterval (1 / 4 : ℝ) := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2⟩
  filter_upwards [ae_restrict_of_ae_restrict_of_subset restricted
    (burnolTateMobiusSource_innerGap p)] with x sourceRead
  simp only [sourceRead, mul_zero, Pi.zero_apply]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

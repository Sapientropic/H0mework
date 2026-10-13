import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Volterra.Window

/-! The source annulus and Volterra action preserve the original reflection and support. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem sourceAnnulusCut_reflect (value : BurnolL2) :
    reflectL2 (sourceAnnulusCut value) = sourceAnnulusCut (reflectL2 value) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (sourceAnnulusCut value) negMeasurePreserving,
    negMeasurePreserving.quasiMeasurePreserving.ae (sourceAnnulusCut_coeFn value),
    sourceAnnulusCut_coeFn (reflectL2 value),
    Lp.coeFn_compMeasurePreserving value negMeasurePreserving]
      with x reflection negative cut reflected
  change reflectL2 (sourceAnnulusCut value) x = sourceAnnulusCut value (-x) at reflection
  change reflectL2 value x = value (-x) at reflected
  rw [reflection, negative, cut, abs_neg]
  split_ifs
  · exact reflected.symm
  · rfl

theorem sourceAnnulusCut_even (value : BurnolL2) (even : reflectL2 value = value) :
    reflectL2 (sourceAnnulusCut value) = sourceAnnulusCut value := by
  rw [sourceAnnulusCut_reflect, even]

private theorem source_directRightResolvent_reflect
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    reflectL2 (burnolDirectRightResolvent (coordinate.value / 2) value) =
      burnolDirectRightResolvent (coordinate.value / 2) (reflectL2 value) := by
  let reflection : BurnolL2 →L[ℂ] BurnolL2 := reflectL2.toContinuousLinearMap
  have rightQuarter : 1 / 4 < (coordinate.value / 2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [coordinate.rightHalf]
  have integrable := burnolDirectRightResolventIntegrand_integrableOn
    (coordinate.value / 2) rightQuarter value
  change reflection (burnolDirectRightResolvent (coordinate.value / 2) value) = _
  unfold burnolDirectRightResolvent
  rw [map_neg, ← reflection.integral_comp_comm integrable]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h _
  change reflectL2 (burnolDirectRightResolventIntegrand (coordinate.value / 2) value h) = _
  simp only [burnolDirectRightResolventIntegrand, map_smul,
    reflectL2_burnolMultiplicativeDilation]

theorem sourceVolterraResolvent_reflect
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    reflectL2 (sourceVolterraResolvent coordinate value) =
      sourceVolterraResolvent coordinate (reflectL2 value) := by
  change reflectL2 (burnolTateReciprocalL2
    (burnolDirectRightResolvent (coordinate.value / 2) (burnolTateReciprocalL2 value))) = _
  rw [← burnolTateReciprocal_reflect, source_directRightResolvent_reflect,
    ← burnolTateReciprocal_reflect]
  rfl

theorem sourceVolterraWindow_reflect
    (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    reflectL2 (sourceVolterraWindow coordinate value) =
      sourceVolterraWindow coordinate (reflectL2 value) := by
  change reflectL2 (sourceAnnulusCut (sourceVolterraResolvent coordinate value)) = _
  rw [sourceAnnulusCut_reflect, sourceVolterraResolvent_reflect]
  rfl

theorem sourceVolterraWindow_even (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolL2) (even : reflectL2 value = value) :
    reflectL2 (sourceVolterraWindow coordinate value) = sourceVolterraWindow coordinate value := by
  rw [sourceVolterraWindow_reflect, even]

theorem original_tate_source_even (p : BurnolPaAmbientCarrier) :
    reflectL2 (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2 p) := by
  rw [← burnolTateReciprocal_reflect, burnolMobiusSourceL2_even]

theorem sourceAnnulusCut_original_pa (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    sourceAnnulusCut (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2 p) := by
  apply Lp.ext
  filter_upwards [sourceAnnulusCut_coeFn (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)),
    pa_tate_source_annulus p inside] with x cut support
  rw [cut]
  by_cases band : (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4
  · rw [if_pos band]
  · rw [if_neg band]
    exact (support band).symm

theorem original_source_dilation_inner_cutoff_zero
    (p : BurnolPaAmbientCarrier) (h : ℝ) (nonnegative : 0 ≤ h) :
    originalPhysicalCutoff (1 / 4)
      (burnolMultiplicativeDilation (-h) (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) = 0 := by
  let source := burnolTateReciprocalL2 (burnolMobiusSourceL2 p)
  have gap := (ae_restrict_iff' (measurableSet_symmetricInterval (1 / 4 : ℝ))).mp
    (burnolTateMobiusSource_innerGap p)
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp (-h) * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp (-h)) (Real.exp_ne_zero _))
  have scale : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr nonnegative)
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn (1 / 4)
    (burnolMultiplicativeDilation (-h) source),
    burnolMultiplicativeDilation_coeFn (-h) source, qmp.ae gap, Lp.coeFn_zero ℂ 2 volume]
      with x cut dilation sourceGap zero
  rw [cut, zero]
  change _ = (0 : ℂ)
  by_cases inside : x ∈ symmetricInterval (1 / 4 : ℝ)
  · have scaled : Real.exp (-h) * x ∈ symmetricInterval (1 / 4 : ℝ) := by
      apply abs_le.mp
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc
        Real.exp (-h) * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right scale (abs_nonneg _)
        _ ≤ 1 / 4 := by simpa only [one_mul] using abs_le.mpr inside
    rw [Set.indicator_of_mem inside, dilation]
    change (Real.exp (-h / 2) : ℂ) * source (Real.exp (-h) * x) = 0
    rw [show source (Real.exp (-h) * x) = 0 from sourceGap scaled, mul_zero]
  · rw [Set.indicator_of_notMem inside]

theorem sourceAnnulusCut_dilation_original (p : BurnolPaAmbientCarrier)
    (h : ℝ) (nonnegative : 0 ≤ h) :
    sourceAnnulusCut
      (burnolMultiplicativeDilation (-h) (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) =
        originalPhysicalCutoff 4
          (burnolMultiplicativeDilation (-h) (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) := by
  rw [sourceAnnulusCut_apply, original_source_dilation_inner_cutoff_zero p h nonnegative, sub_zero]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

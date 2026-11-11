import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Physical.Shell

/-! The actual negative Fourier shell source is the bounded positive power band. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private theorem radiusTail_tate_raw (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (positiveRadius : 0 < radius) :
    (burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate radius positiveRadius) :
      ℝ → ℂ) =ᵐ[volume]
      fun x => if |x| < radius⁻¹ then -(((|x| : ℝ) : ℂ) ^ (coordinate.value - 1)) else 0 := by
  have rawRead := burnolRadiusUnitTail_coeFn coordinate radius positiveRadius
  have sourceMem := Lp.memLp (burnolRadiusNormalizedUnitTail coordinate radius positiveRadius)
  have pulled := burnolTateReciprocalRaw_ae_congr sourceMem (sourceMem.ae_eq rawRead) rawRead
  filter_upwards [burnolTateReciprocalL2_coeFn
    (burnolRadiusNormalizedUnitTail coordinate radius positiveRadius),
    pulled, volume.ae_ne (0 : ℝ)] with x hread hpull nonzero
  have positive : 0 < |x| := abs_pos.mpr nonzero
  rw [hread, hpull]
  unfold burnolTateReciprocalRaw
  dsimp only
  rw [abs_inv]
  simp only [lt_inv_comm₀ positiveRadius positive]
  by_cases small : |x| < radius⁻¹
  · rw [if_pos small, if_pos small, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (abs_nonneg x), Complex.cpow_neg, inv_inv, mul_neg]
    congr 1
    rw [← Complex.cpow_neg_one, ← Complex.cpow_add _ _
      (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero))]
    congr 1
    ring
  · rw [if_neg small, if_neg small, mul_zero]

/-- The same physical source gives the band with its literal half-open source endpoints. -/
theorem negativeFourierShellState_source_raw (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    (burnolMobiusSourceL2 (negativeFourierShellState coordinate radius admitted) : ℝ → ℂ)
      =ᵐ[volume] fun t =>
        if |t| ∈ Ico (1 / 4 : ℝ) radius⁻¹ then
          ((|t| : ℝ) : ℂ) ^ (coordinate.value - 1) else 0 := by
  let positive : 0 < radius := lt_of_lt_of_le (by norm_num) admitted.1
  let low := burnolTateReciprocalL2 (burnolRadiusNormalizedUnitTail coordinate radius positive)
  let high := burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate)
  have ordered : (1 / 4 : ℝ) ≤ radius⁻¹ := by
    rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num,
      inv_le_inv₀ (by norm_num : (0 : ℝ) < 4) positive]
    exact admitted.2
  rw [negativeFourierShellState_source, map_sub]
  filter_upwards [Lp.coeFn_neg (low - high), Lp.coeFn_sub low high,
    radiusTail_tate_raw coordinate radius positive,
    burnolNormalizedFirstSourceUnitTail_tate_coeFn coordinate] with t negRead subRead lowRead highRead
  change (-(low - high) : BurnolL2) t = _
  rw [negRead, Pi.neg_apply, subRead, Pi.sub_apply, lowRead, highRead]
  simp only [mem_Ico]
  by_cases lower : (1 / 4 : ℝ) ≤ |t|
  · rw [if_neg (not_lt.mpr lower)]
    by_cases upper : |t| < radius⁻¹
    · simp only [upper, lower, and_self, if_true, sub_zero, neg_neg]
    · simp only [upper, and_false, if_false, sub_self, neg_zero]
  · have beforeQuarter := lt_of_not_ge lower
    simp only [if_pos (beforeQuarter.trans_le ordered), if_pos beforeQuarter,
      lower, false_and, if_false, sub_self, neg_zero]

/-- On positive t the source is the closed power band; endpoint changes are AE-null. -/
theorem negativeFourierShellState_source_positive_band
    (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    (burnolMobiusSourceL2 (negativeFourierShellState coordinate radius admitted) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi 0)] fun t =>
        if t ∈ Icc (1 / 4 : ℝ) radius⁻¹ then (t : ℂ) ^ (coordinate.value - 1) else 0 := by
  filter_upwards [ae_restrict_of_ae (negativeFourierShellState_source_raw coordinate radius admitted),
    ae_restrict_mem measurableSet_Ioi,
    ae_restrict_of_ae (volume.ae_ne radius⁻¹)] with t raw positive endpoint
  rw [raw, abs_of_pos positive]
  have same : t ∈ Ico (1 / 4 : ℝ) radius⁻¹ ↔ t ∈ Icc (1 / 4 : ℝ) radius⁻¹ := by
    constructor
    · exact fun h => ⟨h.1, h.2.le⟩
    · exact fun h => ⟨h.1, lt_of_le_of_ne h.2 endpoint⟩
  simp only [same]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Probe.OriginalHead

/-! The original tail read follows the same native dilation before the finite source cut. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem original_tail_read_native_dilation
    (coordinate : BurnolCompletedMellinCoordinate) (radius : ℝ) (positive : 0 < radius)
    (h : ℝ) (value : BurnolL2) :
    burnolRadiusMellinTailEvaluator radius positive coordinate.value coordinate.rightHalf
      (burnolMultiplicativeDilation h value) =
      fullMellinTranslationCharacter coordinate.value (-h) *
        burnolRadiusMellinTailEvaluator (radius * Real.exp h)
          (mul_pos positive (Real.exp_pos h)) coordinate.value coordinate.rightHalf value := by
  let kernel := burnolRadiusMellinTailKernelL2 radius positive coordinate.value coordinate.rightHalf
  have flip := (burnolMultiplicativeDilation (-h)).inner_map_eq_flip kernel value
  rw [← burnolMultiplicativeDilation_neg_eq_symm (-h), neg_neg] at flip
  change inner ℂ kernel (burnolMultiplicativeDilation h value) =
    fullMellinTranslationCharacter coordinate.value (-h) *
      inner ℂ (burnolRadiusMellinTailKernelL2 (radius * Real.exp h)
        (mul_pos positive (Real.exp_pos h)) coordinate.value coordinate.rightHalf) value
  rw [← flip]
  change inner ℂ (burnolMultiplicativeDilation (-h)
    (burnolRadiusMellinTailKernelL2 radius positive coordinate.value coordinate.rightHalf)) value = _
  rw [burnolRadiusMellinTail_dilation positive coordinate (-h), inner_smul_left]
  simp only [neg_neg]
  congr 1
  unfold fullMellinTranslationCharacter
  simp only [Complex.star_def, ← Complex.exp_conj, map_mul, map_sub, map_div₀,
    map_one, map_ofNat, Complex.conj_conj, Complex.conj_ofReal]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

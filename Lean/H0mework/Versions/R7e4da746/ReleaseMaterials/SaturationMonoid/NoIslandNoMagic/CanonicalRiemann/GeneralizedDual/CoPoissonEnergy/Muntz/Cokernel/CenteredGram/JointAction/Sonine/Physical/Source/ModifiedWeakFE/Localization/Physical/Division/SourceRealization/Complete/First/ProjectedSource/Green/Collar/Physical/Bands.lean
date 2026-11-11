import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.Contact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Physical.Shell.Raw

/-! The original source coefficients generate the two physical Pa collar bands. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

/-- Both scalar coefficients are read from the same original source. -/
def sourceCollarPhysicalState (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (p : BurnolPaAmbientCarrier)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4) : BurnolPaAmbientCarrier :=
  fullMellinTranslationCharacter coordinate.value h •
    (sourceOuterCollarCoefficient coordinate h
        (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) •
          (-closedShellState coordinate (1 / 4) (by norm_num)) -
      burnolPaResolventSourceCoefficient coordinate p •
        (-closedShellState coordinate (4 * Real.exp (-h)) admitted))

theorem sourceCollarPhysicalState_mem (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (p : BurnolPaAmbientCarrier)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4) :
    sourceCollarPhysicalState coordinate h p admitted ∈ burnolCompactCoPoissonClosedRange := by
  let Pa := burnolCompactCoPoissonClosedRange.toSubmodule
  exact Pa.smul_mem _ (Pa.sub_mem
    (Pa.smul_mem _ (Pa.neg_mem (closedShellState_mem coordinate (1 / 4) (by norm_num))))
    (Pa.smul_mem _ (Pa.neg_mem (closedShellState_mem coordinate (4 * Real.exp (-h)) admitted))))

private theorem negativeShell_tate_source (coordinate : BurnolCompletedMellinCoordinate)
    (radius : ℝ) (admitted : radius ∈ Icc (1 / 4 : ℝ) 4) :
    burnolTateReciprocalL2 (burnolMobiusSourceL2 (-closedShellState coordinate radius admitted)) =
      burnolMobiusSourceL2 (negativeFourierShellState coordinate radius admitted) := by
  simp only [negativeFourierShellState, map_neg,
    burnolMobiusSource_fourier _ (closedShellState_mem coordinate radius admitted)]

theorem sourceCollarPhysicalState_source (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (p : BurnolPaAmbientCarrier)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4) :
    burnolTateReciprocalL2 (burnolMobiusSourceL2 (sourceCollarPhysicalState coordinate h p admitted)) =
      fullMellinTranslationCharacter coordinate.value h •
        (sourceOuterCollarCoefficient coordinate h
          (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) •
            burnolMobiusSourceL2 (negativeFourierShellState coordinate (1 / 4) (by norm_num)) -
          burnolPaResolventSourceCoefficient coordinate p •
            burnolMobiusSourceL2
              (negativeFourierShellState coordinate (4 * Real.exp (-h)) admitted)) := by
  simp only [sourceCollarPhysicalState, map_smul, map_sub, negativeShell_tate_source]

/-- The physical state recovers the full-line whole-band minus lower-collar source. -/
theorem sourceCollarPhysicalState_source_raw (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (p : BurnolPaAmbientCarrier)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4) :
    (burnolTateReciprocalL2 (burnolMobiusSourceL2
      (sourceCollarPhysicalState coordinate h p admitted)) : ℝ → ℂ) =ᵐ[volume]
      fun t => fullMellinTranslationCharacter coordinate.value h *
        ((|t| : ℝ) : ℂ) ^ (coordinate.value - 1) *
          ((if |t| ∈ Ico (1 / 4 : ℝ) 4 then
              sourceOuterCollarCoefficient coordinate h
                (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) else 0) -
            if |t| ∈ Ico (1 / 4 : ℝ) ((1 / 4) * Real.exp h) then
              burnolPaResolventSourceCoefficient coordinate p else 0) := by
  let c := fullMellinTranslationCharacter coordinate.value h
  let E := sourceOuterCollarCoefficient coordinate h
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))
  let M := burnolPaResolventSourceCoefficient coordinate p
  let A := burnolMobiusSourceL2 (negativeFourierShellState coordinate (1 / 4) (by norm_num))
  let B := burnolMobiusSourceL2
    (negativeFourierShellState coordinate (4 * Real.exp (-h)) admitted)
  have inverseRadius : (4 * Real.exp (-h))⁻¹ = (1 / 4 : ℝ) * Real.exp h := by
    simp only [mul_inv_rev, Real.exp_neg, inv_inv]
    ring
  rw [sourceCollarPhysicalState_source]
  filter_upwards [Lp.coeFn_smul c (E • A - M • B), Lp.coeFn_sub (E • A) (M • B),
    Lp.coeFn_smul E A, Lp.coeFn_smul M B,
    negativeFourierShellState_source_raw coordinate (1 / 4) (by norm_num),
    negativeFourierShellState_source_raw coordinate (4 * Real.exp (-h)) admitted]
    with t scalar difference leftScalar rightScalar whole lower
  rw [show (1 / 4 : ℝ)⁻¹ = 4 by norm_num] at whole
  rw [inverseRadius] at lower
  change (c • (E • A - M • B) : BurnolL2) t = _
  rw [scalar, Pi.smul_apply, difference, Pi.sub_apply, leftScalar, rightScalar,
    Pi.smul_apply, Pi.smul_apply, whole, lower]
  change c * (E * (if |t| ∈ Ico (1 / 4 : ℝ) 4 then
    ((|t| : ℝ) : ℂ) ^ (coordinate.value - 1) else 0) -
      M * (if |t| ∈ Ico (1 / 4 : ℝ) ((1 / 4) * Real.exp h) then
        ((|t| : ℝ) : ℂ) ^ (coordinate.value - 1) else 0)) =
    c * ((|t| : ℝ) : ℂ) ^ (coordinate.value - 1) *
      ((if |t| ∈ Ico (1 / 4 : ℝ) 4 then E else 0) -
        if |t| ∈ Ico (1 / 4 : ℝ) ((1 / 4) * Real.exp h) then M else 0)
  split_ifs <;> ring

theorem sourceCollarPhysicalState_source_positive_band
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (p : BurnolPaAmbientCarrier)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4) :
    (burnolTateReciprocalL2 (burnolMobiusSourceL2
      (sourceCollarPhysicalState coordinate h p admitted)) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ioi 0)] fun t =>
        fullMellinTranslationCharacter coordinate.value h * (t : ℂ) ^ (coordinate.value - 1) *
          ((if t ∈ Ico (1 / 4 : ℝ) 4 then
              sourceOuterCollarCoefficient coordinate h
                (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) else 0) -
            if t ∈ Ico (1 / 4 : ℝ) ((1 / 4) * Real.exp h) then
              burnolPaResolventSourceCoefficient coordinate p else 0) := by
  filter_upwards [ae_restrict_of_ae (sourceCollarPhysicalState_source_raw coordinate h p admitted),
    ae_restrict_mem measurableSet_Ioi] with t raw positive
  simpa only [abs_of_pos (show 0 < t from positive)] using raw

/-- On the original contact band this is exactly the finite commutator's source expression. -/
theorem sourceCollarPhysicalState_source_contact_band
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (p : BurnolPaAmbientCarrier)
    (admitted : 4 * Real.exp (-h) ∈ Icc (1 / 4 : ℝ) 4) :
    (burnolTateReciprocalL2 (burnolMobiusSourceL2
      (sourceCollarPhysicalState coordinate h p admitted)) : ℝ → ℂ)
      =ᵐ[volume.restrict (Ico (1 / 4 : ℝ) 4)] fun t =>
        fullMellinTranslationCharacter coordinate.value h * (t : ℂ) ^ (coordinate.value - 1) *
          (sourceOuterCollarCoefficient coordinate h
            (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) -
            if t * Real.exp (-h) < (1 / 4 : ℝ) then
              burnolPaResolventSourceCoefficient coordinate p else 0) := by
  filter_upwards [ae_restrict_of_ae (sourceCollarPhysicalState_source_raw coordinate h p admitted),
    ae_restrict_mem measurableSet_Ico] with t raw inside
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have sameLower : t ∈ Ico (1 / 4 : ℝ) ((1 / 4) * Real.exp h) ↔
      t * Real.exp (-h) < (1 / 4 : ℝ) := by
    simp only [mem_Ico, inside.1, true_and]
    have comparison := (mul_lt_mul_iff_of_pos_right (Real.exp_pos (-h)) :
      t * Real.exp (-h) < ((1 / 4 : ℝ) * Real.exp h) * Real.exp (-h) ↔
        t < (1 / 4 : ℝ) * Real.exp h)
    simpa only [Real.exp_neg, mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero h), mul_one]
      using comparison.symm
  simpa only [abs_of_pos positive, if_pos inside, sameLower] using raw

theorem sourceCollarPhysicalState_zero (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) :
    sourceCollarPhysicalState coordinate 0 p (by norm_num) = 0 := by
  simp [sourceCollarPhysicalState, sourceOuterCollarCoefficient, closedShellState_four]

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.TailAction
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.TailCut
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Green.Collar.Source.OriginalMass

/-! Finite dilation exposes both collars of the original source Volterra contact. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def finiteSourceContact (coordinate : BurnolCompletedMellinCoordinate)
    (t : ℝ) (positive : 0 < t) (value : BurnolL2) : ℂ :=
  -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
    (burnolRadiusMellinTailEvaluator t positive coordinate.value coordinate.rightHalf value -
      burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf value)

theorem finiteSourceContact_original (coordinate : BurnolCompletedMellinCoordinate)
    (t : ℝ) (positive : 0 < t) (p : BurnolPaAmbientCarrier) :
    finiteSourceContact coordinate t positive
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
        burnolPaSourceContact coordinate t positive p := rfl

theorem source_contact_reverse_cut (coordinate : BurnolCompletedMellinCoordinate)
    (t : ℝ) (positive : 0 < t) (inside : t ≤ 4) (h : ℝ) (value : BurnolL2) :
    finiteSourceContact coordinate t positive
      (originalPhysicalCutoff 4 (burnolMultiplicativeDilation (-h) value)) =
      -(2 : ℂ) * (t : ℂ) ^ (coordinate.value - 1) *
        fullMellinTranslationCharacter coordinate.value h *
          (burnolRadiusMellinTailEvaluator (t * Real.exp (-h))
            (mul_pos positive (Real.exp_pos (-h))) coordinate.value coordinate.rightHalf value -
          burnolRadiusMellinTailEvaluator (4 * Real.exp (-h))
            (mul_pos (by norm_num) (Real.exp_pos (-h)))
              coordinate.value coordinate.rightHalf value) := by
  unfold finiteSourceContact
  rw [source_tail_cutoff_inside coordinate t positive 4 inside,
    source_tail_cutoff_outside coordinate 4 (by norm_num) 4 le_rfl,
    sub_zero, original_tail_read_native_dilation, original_tail_read_native_dilation]
  simp only [neg_neg]
  ring

theorem source_contact_halfDensity_power (coordinate : BurnolCompletedMellinCoordinate)
    (h t : ℝ) (positive : 0 < t) :
    (Real.exp (-h / 2) : ℂ) * ((t * Real.exp (-h) : ℝ) : ℂ) ^
        (coordinate.value - 1) =
      fullMellinTranslationCharacter coordinate.value h *
        (t : ℂ) ^ (coordinate.value - 1) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg positive.le (Real.exp_pos (-h)).le]
  have power : (Real.exp (-h) : ℂ) ^ (coordinate.value - 1) =
      Complex.exp ((-h : ℂ) * (coordinate.value - 1)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos (-h)).le, Real.log_exp, Complex.ofReal_neg]
  rw [power, Complex.ofReal_exp]
  rw [mul_left_comm, ← Complex.exp_add]
  unfold fullMellinTranslationCharacter
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- The upper collar is read from the same unshifted source, not supplied as boundary data. -/
def sourceOuterCollarCoefficient (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) : BurnolL2 →L[ℂ] ℂ :=
  (2 : ℂ) • (burnolRadiusMellinTailEvaluator (4 * Real.exp (-h))
    (mul_pos (by norm_num) (Real.exp_pos (-h))) coordinate.value coordinate.rightHalf -
      burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf)

/-- Reverse shift of the finite contact has an outer band and the actual lower-gap collar. -/
theorem original_source_contact_reverse_commutator
    (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) (forward : 0 ≤ h)
    (p : BurnolPaAmbientCarrier) (insidePa : p ∈ burnolCompactCoPoissonClosedRange)
    (t : ℝ) (inside : t ∈ Ico (1 / 4 : ℝ) 4) :
    finiteSourceContact coordinate t (lt_of_lt_of_le (by norm_num) inside.1)
        (originalPhysicalCutoff 4 (burnolMultiplicativeDilation (-h)
          (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) -
      (Real.exp (-h / 2) : ℂ) * firstContactRead coordinate (t * Real.exp (-h)) p =
      fullMellinTranslationCharacter coordinate.value h * (t : ℂ) ^ (coordinate.value - 1) *
        (sourceOuterCollarCoefficient coordinate h (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) -
          if t * Real.exp (-h) < (1 / 4 : ℝ) then
            burnolPaResolventSourceCoefficient coordinate p else 0) := by
  let sigma := burnolTateReciprocalL2 (burnolMobiusSourceL2 p)
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have scaledPositive : 0 < t * Real.exp (-h) := mul_pos positive (Real.exp_pos (-h))
  have scaleBound : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr forward)
  have scaledUpper : t * Real.exp (-h) < 4 :=
    lt_of_le_of_lt (mul_le_of_le_one_right positive.le scaleBound) inside.2
  have scaling := source_contact_halfDensity_power coordinate h t positive
  have mass := original_source_mass_eq_coefficient coordinate p insidePa
  rw [source_contact_reverse_cut coordinate t positive inside.2.le]
  by_cases lower : (1 / 4 : ℝ) ≤ t * Real.exp (-h)
  · rw [firstContactRead, dif_pos (by simpa only [abs_of_pos scaledPositive] using
      (show (1 / 4 : ℝ) ≤ t * Real.exp (-h) ∧ t * Real.exp (-h) < 4 from ⟨lower, scaledUpper⟩))]
    simp only [abs_of_pos scaledPositive, burnolPaSourceContact, smul_apply,
      ContinuousLinearMap.comp_apply, sub_apply, smul_eq_mul,
      sourceOuterCollarCoefficient, if_neg (not_lt.mpr lower)]
    linear_combination (2 : ℂ) *
      (burnolRadiusMellinTailEvaluator (t * Real.exp (-h)) scaledPositive
        coordinate.value coordinate.rightHalf sigma -
       burnolRadiusMellinTailEvaluator 4 (by norm_num)
        coordinate.value coordinate.rightHalf sigma) * scaling
  · rw [firstContactRead, dif_neg (by simpa only [abs_of_pos scaledPositive] using
      (show ¬ ((1 / 4 : ℝ) ≤ t * Real.exp (-h) ∧ t * Real.exp (-h) < 4) from
        fun bound => lower bound.1)), zero_apply, mul_zero, sub_zero,
      if_pos (lt_of_not_ge lower), ← mass,
      original_source_tail_below_quarter coordinate (t * Real.exp (-h)) scaledPositive
        (le_of_lt (lt_of_not_ge lower)) p]
    simp only [sourceOuterCollarCoefficient, smul_apply, sub_apply, smul_eq_mul]
    ring

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

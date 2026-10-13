import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.ProbeCutoffValue
import H0mework.Versions.V2.Arithmetic.RiemannShiftedSource.SourceActionResolvent
import H0mework.Versions.V2.Arithmetic.RiemannWholeWard.FirstProfile

/-! The source-side Volterra window is an actual bounded operator on the original L². -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

/-- The fixed source annulus, cut by the original physical restriction and extension. -/
def sourceAnnulusCut : BurnolL2 →L[ℂ] BurnolL2 :=
  (burnolRadiusZeroExtension 4).comp (burnolRadiusRestriction 4) -
    (burnolRadiusZeroExtension (1 / 4)).comp (burnolRadiusRestriction (1 / 4))

theorem sourceAnnulusCut_apply (value : BurnolL2) :
    sourceAnnulusCut value =
      originalPhysicalCutoff 4 value - originalPhysicalCutoff (1 / 4) value := rfl

theorem sourceAnnulusCut_coeFn (value : BurnolL2) :
    (sourceAnnulusCut value : ℝ → ℂ) =ᵐ[volume]
      fun x => if (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4 then value x else 0 := by
  filter_upwards [Lp.coeFn_sub (originalPhysicalCutoff 4 value)
    (originalPhysicalCutoff (1 / 4) value), originalPhysicalCutoff_coeFn 4 value,
    originalPhysicalCutoff_coeFn (1 / 4) value] with x difference outer inner
  change (originalPhysicalCutoff 4 value - originalPhysicalCutoff (1 / 4) value : BurnolL2) x = _
  rw [difference, Pi.sub_apply, outer, inner]
  have membership (r : ℝ) : x ∈ symmetricInterval r ↔ |x| ≤ r := abs_le.symm
  by_cases large : |x| ≤ 4
  · rw [Set.indicator_of_mem ((membership 4).mpr large)]
    by_cases small : |x| ≤ (1 / 4 : ℝ)
    · rw [Set.indicator_of_mem ((membership (1 / 4)).mpr small), sub_self,
        if_neg (fun h => (not_lt_of_ge small) h.1)]
    · rw [Set.indicator_of_notMem (fun h => small ((membership (1 / 4)).mp h)),
        sub_zero, if_pos ⟨lt_of_not_ge small, large⟩]
  · have small : x ∉ symmetricInterval (1 / 4 : ℝ) := by
      intro h
      exact large (le_trans ((membership (1 / 4)).mp h) (by norm_num))
    rw [Set.indicator_of_notMem (fun h => large ((membership 4).mp h)),
      Set.indicator_of_notMem small, sub_self, if_neg (fun h => large h.2)]

/-- The original Tate involution conjugates the original direct right resolvent. -/
def sourceVolterraResolvent (coordinate : BurnolCompletedMellinCoordinate) :
    BurnolL2 →L[ℂ] BurnolL2 :=
  burnolTateReciprocalL2.comp
    ((burnolDirectRightResolventCLM coordinate).comp burnolTateReciprocalL2)

/-- The Volterra output is cut in source L² before any physical realization. -/
def sourceVolterraWindow (coordinate : BurnolCompletedMellinCoordinate) :
    BurnolL2 →L[ℂ] BurnolL2 :=
  sourceAnnulusCut.comp (sourceVolterraResolvent coordinate)

/-- The full original Pa correction is exactly the source-side Volterra window. -/
theorem sourceVolterraWindow_original_pa (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    sourceVolterraWindow coordinate (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) =
      burnolTateReciprocalL2 (burnolMobiusSourceL2
        (burnolPaSourceCorrection coordinate ⟨p, inside⟩)) := by
  let corrected := burnolTateReciprocalL2 (burnolMobiusSourceL2
    (burnolPaSourceCorrection coordinate ⟨p, inside⟩))
  let tail := burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate)
  let coefficient := burnolPaResolventSourceCoefficient coordinate p
  have actual := congrArg burnolTateReciprocalL2
    (correction_source_resolvent coordinate p inside)
  rw [map_sub, map_smul] at actual
  have split : sourceVolterraResolvent coordinate
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) = corrected + coefficient • tail := by
    change burnolTateReciprocalL2 (burnolDirectRightResolvent (coordinate.value / 2)
      (burnolTateReciprocalL2 (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)))) = _
    rw [burnolTateReciprocalL2_involutive]
    exact (eq_sub_iff_add_eq.mp actual).symm
  change sourceAnnulusCut (sourceVolterraResolvent coordinate
    (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) = corrected
  rw [split]
  apply Lp.ext
  filter_upwards [sourceAnnulusCut_coeFn (corrected + coefficient • tail),
    Lp.coeFn_add corrected (coefficient • tail), Lp.coeFn_smul coefficient tail,
    pa_correction_contact_profile coordinate p inside,
    burnolNormalizedFirstSourceUnitTail_tate_coeFn coordinate,
    volume.ae_ne (1 / 4 : ℝ), volume.ae_ne (-1 / 4 : ℝ)]
      with x cutRead sumRead scaleRead correctedRead tailRead notPositive notNegative
  change corrected x = firstContactRead coordinate x p at correctedRead
  change tail x = _ at tailRead
  rw [cutRead]
  by_cases band : (1 / 4 : ℝ) < |x| ∧ |x| ≤ 4
  · rw [if_pos band, sumRead, Pi.add_apply, scaleRead, Pi.smul_apply, smul_eq_mul,
      tailRead, if_neg (not_lt.mpr band.1.le), mul_zero, add_zero]
  · have outside : ¬ ((1 / 4 : ℝ) ≤ |x| ∧ |x| < 4) := by
      intro h
      have ne : |x| ≠ (1 / 4 : ℝ) := by
        intro equality
        rcases (abs_eq (show (0 : ℝ) ≤ 1 / 4 by norm_num)).mp equality with right | left
        · exact notPositive right
        · exact notNegative (by simpa only [neg_div] using left)
      exact band ⟨lt_of_le_of_ne h.1 ne.symm, h.2.le⟩
    rw [if_neg band, correctedRead, firstContactRead, dif_neg outside, zero_apply]


end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

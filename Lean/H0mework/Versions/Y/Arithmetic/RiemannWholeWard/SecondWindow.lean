import H0mework.Versions.Y.Arithmetic.RiemannWholeWard.FirstProfile
import H0mework.Versions.Y.Arithmetic.RiemannWholeWard.SecondContact
import H0mework.Versions.Y.Arithmetic.RiemannShiftedSource.SourceActionSecondStrong

/-! The original Pa source generates one second-order window and its literal contact coordinates. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def sourceSecondWindow (coordinate : BurnolCompletedMellinCoordinate) :
    burnolCompactCoPoissonClosedRange.toSubmodule →L[ℂ] BurnolL2 :=
  let read := burnolMobiusSourceL2.comp (burnolPaSourceCorrection coordinate)
  let coefficient := (burnolPaResolventSourceCoefficient coordinate).comp
    burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL
  (2 / (2 * coordinate.value - 1) : ℂ) •
    (read + burnolTateReciprocalL2.comp read - coefficient.smulRight
      (burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
        burnolNormalizedFirstSourceUnitTail coordinate))

theorem sourceSecondWindow_same_operator (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius p = p) :
    sourceSecondWindow coordinate ⟨p, inside⟩ =
      sourceSecondWhole coordinate (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) -
        (2 / (2 * coordinate.value - 1) * burnolPaResolventSourceCoefficient coordinate p) •
          (burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) +
            burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate)) := by
  have same := burnolMobiusSource_fourier p inside
  rw [fixed] at same
  change (2 / (2 * coordinate.value - 1) : ℂ) •
    (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate ⟨p, inside⟩) +
      burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate ⟨p, inside⟩)) -
      burnolPaResolventSourceCoefficient coordinate p •
        (burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
          burnolNormalizedFirstSourceUnitTail coordinate)) = _
  rw [correction_source_resolvent coordinate p inside, map_sub, map_smul]
  unfold sourceSecondWhole
  rw [← same]
  module

theorem sourceSecondWindow_contact_profile (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    (sourceSecondWindow coordinate ⟨p, inside⟩ : ℝ → ℂ) =ᵐ[volume.restrict (Ioo (1 / 4 : ℝ) 4)]
      fun t => if positive : 0 < t then secondContact coordinate t positive p else 0 := by
  let C := burnolPaSourceCorrection coordinate ⟨p, inside⟩
  let R := burnolMobiusSourceL2 C
  let psi := burnolTateReciprocalL2 R
  let M := burnolPaResolventSourceCoefficient coordinate p
  let tail := burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num) -
    burnolNormalizedFirstSourceUnitTail coordinate
  let coefficient : ℂ := 2 / (2 * coordinate.value - 1)
  have profile : (psi : ℝ → ℂ) =ᵐ[volume] fun x => firstContactRead coordinate x p :=
    pa_correction_contact_profile coordinate p inside
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp psi)
    ((Lp.memLp psi).ae_eq profile) profile
  have reversed := burnolTateReciprocalL2_coeFn psi
  change (burnolTateReciprocalL2 (burnolTateReciprocalL2 R) : ℝ → ℂ) =ᵐ[volume] _ at reversed
  rw [burnolTateReciprocalL2_involutive] at reversed
  have totalRead : (sourceSecondWindow coordinate ⟨p, inside⟩ : ℝ → ℂ) =ᵐ[volume]
      fun x => coefficient * (R x + psi x - M * tail x) := by
    change ((coefficient • (R + psi - M • tail) : BurnolL2) : ℝ → ℂ) =ᵐ[volume] _
    filter_upwards [Lp.coeFn_smul coefficient (R + psi - M • tail),
      Lp.coeFn_sub (R + psi) (M • tail), Lp.coeFn_add R psi, Lp.coeFn_smul M tail]
      with x scaleRead subRead addRead tailRead
    rw [scaleRead, Pi.smul_apply, subRead, Pi.sub_apply, addRead, Pi.add_apply,
      tailRead, Pi.smul_apply]
    rfl
  filter_upwards [ae_restrict_of_ae totalRead, ae_restrict_of_ae profile,
    ae_restrict_of_ae reversed, ae_restrict_of_ae pulled,
    ae_restrict_of_ae (Lp.coeFn_sub
      (burnolRadiusNormalizedUnitTail coordinate (1 / 4) (by norm_num))
      (burnolNormalizedFirstSourceUnitTail coordinate)),
    ae_restrict_of_ae (burnolRadiusUnitTail_coeFn coordinate (1 / 4) (by norm_num)),
    ae_restrict_of_ae (burnolNormalizedFirstSourceUnitTail_coeFn coordinate),
    ae_restrict_mem measurableSet_Ioo] with t read contact reverse pull subTail low high ht
  have positive : 0 < t := lt_trans (by norm_num) ht.1
  have inRange : (1 / 4 : ℝ) ≤ t ∧ t < 4 := ⟨ht.1.le, ht.2⟩
  have inverseRange : (1 / 4 : ℝ) ≤ t⁻¹ ∧ t⁻¹ < 4 := by
    constructor
    · exact le_of_lt ((lt_inv_comm₀ (by norm_num) positive).mpr (by simpa using ht.2))
    · exact (inv_lt_comm₀ positive (by norm_num)).mpr (by simpa using ht.1)
  rw [read, contact, reverse, pull]
  simp only [burnolTateReciprocalRaw, firstContactRead, dif_pos inRange, dif_pos inverseRange,
    abs_of_pos positive, abs_of_pos (inv_pos.mpr positive), dif_pos positive]
  change coefficient * (_ + _ - M * tail t) = _
  change tail t = _ at subTail
  rw [subTail, Pi.sub_apply, low, high]
  simp only [abs_of_pos positive, if_pos ht.1, burnolNormalizedFirstSourceUnitTailRaw,
    if_neg (not_lt_of_ge ht.2.le), sub_zero]
  simp only [secondContact, smul_apply, add_apply, smul_eq_mul]
  dsimp only [coefficient, M]
  ring

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.V2.Arithmetic.RiemannWholeWard.CompactReciprocity

/-! The original Pa inverse source generates its bounded second-flux contacts. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def secondContactFlux (coordinate : BurnolCompletedMellinCoordinate)
    (t : ℝ) (positive : 0 < t) : BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  (2 / (2 * coordinate.value - 1) : ℂ) •
    (((coordinate.value - 1) * (t : ℂ)) • burnolPaSourceContact coordinate t positive -
      (coordinate.value * (t : ℂ)) •
        ((t : ℂ)⁻¹ • burnolPaSourceContact coordinate t⁻¹ (inv_pos.mpr positive) +
          (t : ℂ) ^ (-coordinate.value) • burnolPaResolventSourceCoefficient coordinate))

theorem secondContactFlux_compact (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource)
    (fixed : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolCompactAdditivePhysicalState source) = burnolCompactAdditivePhysicalState source)
    {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    secondContactFlux coordinate t (lt_of_lt_of_le (by norm_num) inside.1)
      (burnolCompactAdditivePhysicalState source) = secondFlux coordinate source t := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  change (2 / (2 * coordinate.value - 1) : ℂ) *
    ((coordinate.value - 1) * (t : ℂ) *
        burnolPaSourceContact coordinate t positive (burnolCompactAdditivePhysicalState source) -
      coordinate.value * (t : ℂ) *
        ((t : ℂ)⁻¹ * burnolPaSourceContact coordinate t⁻¹ (inv_pos.mpr positive)
            (burnolCompactAdditivePhysicalState source) +
          (t : ℂ) ^ (-coordinate.value) * burnolPaResolventSourceCoefficient coordinate
            (burnolCompactAdditivePhysicalState source))) = _
  rw [burnolPaSourceContact_compact coordinate source inside,
    burnolPaSourceContact_compact coordinate source (reciprocal_inside inside)]
  have power : (t : ℂ) ^ (-coordinate.value) *
      (t : ℂ) ^ (coordinate.value - 1) = (t : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ nonzero,
      show -coordinate.value + (coordinate.value - 1) = -1 by ring, Complex.cpow_neg_one]
  have shiftLeft : (t : ℂ) * (t : ℂ) ^ (-coordinate.value) =
      (t : ℂ) ^ (1 - coordinate.value) := by
    nth_rw 1 [← Complex.cpow_one (t : ℂ)]
    rw [← Complex.cpow_add _ _ nonzero, sub_eq_add_neg]
  have shiftRight : (t : ℂ) * (t : ℂ) ^ (coordinate.value - 1) =
      (t : ℂ) ^ coordinate.value := by
    nth_rw 1 [← Complex.cpow_one (t : ℂ)]
    rw [← Complex.cpow_add _ _ nonzero]
    congr 1
    ring
  calc
    _ = (2 / (2 * coordinate.value - 1) : ℂ) *
      ((coordinate.value - 1) * (t : ℂ) *
          ((1 / 2 : ℂ) * burnolFirstSourceCoefficient coordinate source t) -
        coordinate.value * (t : ℂ) * (t : ℂ) ^ (-coordinate.value) *
          tatePrimitive coordinate source t) := by
      unfold tatePrimitive
      rw [← power]
      ring
    _ = _ := by
      rw [firstCoefficient_eq_finiteMoment coordinate source inside.1,
        tatePrimitive_eq_upperMoment coordinate source fixed inside]
      unfold secondFlux
      rw [← shiftLeft, ← shiftRight]
      ring

theorem secondContactFlux_outer (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    secondContactFlux coordinate 4 (by norm_num) p = 0 := by
  have contact := secondContact_outer coordinate p inside
  change (2 / (2 * coordinate.value - 1) : ℂ) *
    (burnolPaSourceContact coordinate 4 (by norm_num) p +
      (4 : ℂ)⁻¹ * burnolPaSourceContact coordinate (4 : ℝ)⁻¹ (by norm_num) p +
      (4 : ℂ) ^ (-coordinate.value) * burnolPaResolventSourceCoefficient coordinate p) = 0 at contact
  change (2 / (2 * coordinate.value - 1) : ℂ) *
    ((coordinate.value - 1) * 4 * burnolPaSourceContact coordinate 4 (by norm_num) p -
      coordinate.value * 4 *
        ((4 : ℂ)⁻¹ * burnolPaSourceContact coordinate (4 : ℝ)⁻¹ (by norm_num) p +
          (4 : ℂ) ^ (-coordinate.value) * burnolPaResolventSourceCoefficient coordinate p)) = 0
  rw [burnolPaSourceContact_outer] at contact ⊢
  linear_combination -coordinate.value * 4 * contact

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

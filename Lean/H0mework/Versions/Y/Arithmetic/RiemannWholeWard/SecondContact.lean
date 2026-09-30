import H0mework.Versions.Y.Arithmetic.RiemannWholeWard.FirstContact

/-! Same-source contact and strong-action coordinates of the original Pa correction. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def secondContact (coordinate : BurnolCompletedMellinCoordinate) (t : ℝ) (positive : 0 < t) :
    BurnolPaAmbientCarrier →L[ℂ] ℂ :=
  (2 / (2 * coordinate.value - 1) : ℂ) •
    (burnolPaSourceContact coordinate t positive +
      (t : ℂ)⁻¹ • burnolPaSourceContact coordinate t⁻¹ (inv_pos.mpr positive) +
      (t : ℂ) ^ (-coordinate.value) • burnolPaResolventSourceCoefficient coordinate)

private theorem reciprocal_power (z : ℂ) (t : ℝ) (positive : 0 < t) :
    (t : ℂ)⁻¹ * ((t⁻¹ : ℝ) : ℂ) ^ (z - 1) = (t : ℂ) ^ (-z) := by
  have nonzero : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg positive.le,
    Complex.cpow_sub _ _ nonzero, Complex.cpow_one, Complex.cpow_neg]
  field_simp

theorem secondContact_outer (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    secondContact coordinate 4 (by norm_num) p = 0 := by
  change (2 / (2 * coordinate.value - 1) : ℂ) *
    (burnolPaSourceContact coordinate 4 (by norm_num) p +
      (4 : ℂ)⁻¹ * burnolPaSourceContact coordinate (4 : ℝ)⁻¹ (by norm_num) p +
      (4 : ℂ) ^ (-coordinate.value) * burnolPaResolventSourceCoefficient coordinate p) = 0
  rw [burnolPaSourceContact_outer]
  have inner := burnolPaSourceContact_inner coordinate p inside
  have low : (4 : ℝ)⁻¹ = 1 / 4 := by norm_num
  simp only [low]
  rw [inner]
  have power := reciprocal_power coordinate.value 4 (by norm_num)
  rw [low] at power
  norm_num only [Complex.ofReal_ofNat] at power
  linear_combination -(2 / (2 * coordinate.value - 1) : ℂ) * burnolPaResolventSourceCoefficient coordinate p * power

theorem secondContact_inner (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    secondContact coordinate (1 / 4) (by norm_num) p =
      (2 / (2 * coordinate.value - 1) : ℂ) *
        ((((1 / 4 : ℝ) : ℂ) ^ (-coordinate.value)) -
          (((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1))) *
        burnolPaResolventSourceCoefficient coordinate p := by
  change (2 / (2 * coordinate.value - 1) : ℂ) *
    (burnolPaSourceContact coordinate (1 / 4) (by norm_num) p +
      (((1 / 4 : ℝ) : ℂ))⁻¹ * burnolPaSourceContact coordinate ((1 / 4 : ℝ)⁻¹) (by norm_num) p +
      (((1 / 4 : ℝ) : ℂ)) ^ (-coordinate.value) * burnolPaResolventSourceCoefficient coordinate p) = _
  rw [burnolPaSourceContact_inner coordinate p inside]
  simp only [show ((1 / 4 : ℝ)⁻¹) = 4 by norm_num]
  rw [burnolPaSourceContact_outer]
  ring

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

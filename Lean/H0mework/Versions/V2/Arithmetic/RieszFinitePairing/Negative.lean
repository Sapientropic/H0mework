import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.NegativeRaw
import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.AnnulusChange
import H0mework.Versions.V2.Arithmetic.RieszFinitePairing.ColumnMass

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Complex Filter MeasureTheory Set
open OriginalRieszFiniteColumns
noncomputable section

local notation "q" => (1 / 4 : ℝ)

theorem annularRead_negative (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    annularRead coordinate (-shift) =
      -(2 : ℂ) * (Real.exp (shift / 2) : ℂ) *
        ∫ y : ℝ in (q * Real.exp (-shift))..q,
          star (positionSource coordinate y) * positionSource coordinate (Real.exp shift * y) := by
  let f := fun x : ℝ =>
    star (positionColumn coordinate (-shift) x) * positionTail coordinate x
  have regular : IntegrableOn f (symmetricInterval q)ᶜ :=
    exterior_integrable (positionColumn coordinate (-shift))
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) _ _ _
      (positionColumn_integrable coordinate (-shift))
      (burnolRieszState_ae_raw coordinate) (position_raw coordinate)
  have even : (fun x : ℝ => f (-x)) =ᵐ[volume] f := by
    filter_upwards [negativePositionColumn_even coordinate shift] with x reflected
    simp only [f, reflected, positionTail_even]
  have support : ∀ᵐ x : ℝ ∂volume,
      x ∉ symmetricInterval (q * Real.exp shift) → f x = 0 := by
    filter_upwards [negativePositionColumn_support coordinate shift nonnegative] with x zero outside
    simp only [f, zero outside, star_zero, zero_mul]
  have scaled := exterior_integral_eq_scaled shift nonnegative f regular even support
  have interval : q * Real.exp (-shift) ≤ q := by
    nlinarith [Real.exp_le_one_iff.mpr (by linarith : -shift ≤ 0)]
  have endpoint : Real.exp shift * (q * Real.exp (-shift)) = q := by
    rw [Real.exp_neg]
    field_simp
  have insideRead :
      (∫ y : ℝ in (q * Real.exp (-shift))..q, f (Real.exp shift * y)) =
        -(Real.exp (-shift / 2) : ℂ) *
          ∫ y : ℝ in (q * Real.exp (-shift))..q,
            star (positionSource coordinate y) * positionSource coordinate (Real.exp shift * y) := by
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_of_le interval, intervalIntegral.integral_of_le interval]
    apply integral_congr_ae
    filter_upwards [negativePositionColumn_band_read coordinate shift,
      ae_restrict_mem measurableSet_Ioc] with y read inside
    have outside : q < Real.exp shift * y := by
      rw [← endpoint]
      exact mul_lt_mul_of_pos_left inside.1 (Real.exp_pos shift)
    change star (positionColumn coordinate (-shift) (Real.exp shift * y)) *
      positionTail coordinate (Real.exp shift * y) = _
    rw [read, positionTail_positive coordinate outside]
    simp only [star_mul, star_neg, Complex.star_def, Complex.conj_ofReal]
    ring
  have exponential : (Real.exp shift : ℂ) * (Real.exp (-shift / 2) : ℂ) =
      (Real.exp (shift / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, show shift + (-shift / 2) = shift / 2 by ring]
  rw [annularRead, positionColumn_integral_zero, fourierColumn_integral_zero,
    star_zero, mul_zero, mul_zero, zero_add, zero_add,
    exteriorRead_zero_of_quarter _ _ (fourierColumn_negative_quarter coordinate shift nonnegative), add_zero]
  change (∫ x : ℝ in (symmetricInterval q)ᶜ, f x) = _
  rw [scaled, insideRead]
  linear_combination -(2 : ℂ) *
    (∫ y : ℝ in (q * Real.exp (-shift))..q,
      star (positionSource coordinate y) * positionSource coordinate (Real.exp shift * y)) * exponential

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.ProbeCutoffValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFiniteColumns

open Complex MeasureTheory Set
open OriginalPaPhysicalGreen
noncomputable section

theorem cutoff_eq_self_of_ae_zero (radius : ℝ) (value : BurnolL2)
    (outside : ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval radius → value x = 0) :
    originalPhysicalCutoff radius value = value := by
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn radius value, outside] with x read zero
  rw [read]
  by_cases inside : x ∈ symmetricInterval radius
  · exact Set.indicator_of_mem inside _
  · rw [Set.indicator_of_notMem inside, zero inside]

theorem integrable_of_cutoff_eq_self (radius : ℝ) (value : BurnolL2)
    (supported : originalPhysicalCutoff radius value = value) : Integrable value := by
  rw [← supported]
  exact originalPhysicalCutoff_integrable radius value

theorem firstMoment_of_cutoff_eq_self (radius : ℝ) (value : BurnolL2)
    (supported : originalPhysicalCutoff radius value = value) :
    MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume := by
  rw [← supported]
  exact originalPhysicalCutoff_firstMoment radius value

theorem cutoff_smul_self (radius : ℝ) (value : BurnolL2) (coefficient : ℂ)
    (supported : originalPhysicalCutoff radius value = value) :
    originalPhysicalCutoff radius (coefficient • value) = coefficient • value := by
  change (burnolRadiusZeroExtension radius).comp (burnolRadiusRestriction radius)
    (coefficient • value) = _
  rw [map_smul]
  exact congrArg (fun v : BurnolL2 => coefficient • v) supported

theorem intervalIntegral_cutoff_self (radius : ℝ) (value : ℝ → BurnolL2) (left right : ℝ)
    (integrable : IntervalIntegrable value volume left right)
    (supported : ∀ time ∈ Set.uIcc left right,
      originalPhysicalCutoff radius (value time) = value time) :
    originalPhysicalCutoff radius (∫ time : ℝ in left..right, value time) =
      ∫ time : ℝ in left..right, value time := by
  let cut : BurnolL2 →L[ℂ] BurnolL2 :=
    (burnolRadiusZeroExtension radius).comp (burnolRadiusRestriction radius)
  change cut (∫ time : ℝ in left..right, value time) = _
  rw [← cut.intervalIntegral_comp_comm integrable]
  apply intervalIntegral.integral_congr
  intro time inside
  exact supported time inside

end
end OriginalRieszFiniteColumns
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

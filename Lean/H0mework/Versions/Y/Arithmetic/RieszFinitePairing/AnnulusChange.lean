import H0mework.Versions.Y.Arithmetic.RieszFinitePairing.Annular

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing

open Classical Complex Filter MeasureTheory Set
open scoped InnerProductSpace
open OriginalPaPhysicalGreen

noncomputable section
local notation "q" => (1 / 4 : ℝ)

theorem cutoff_ae_zero (radius : ℝ) (value : BurnolL2)
    (supported : originalPhysicalCutoff radius value = value) :
    ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval radius → value x = 0 := by
  have read := burnolRadiusZeroExtension_coe (burnolRadiusRestriction radius value)
  change (originalPhysicalCutoff radius value : ℝ → ℂ) =ᵐ[volume] _ at read
  rw [supported] at read
  filter_upwards [read] with x actual outside
  rw [actual, indicator_of_notMem outside]

theorem exteriorRead_zero_of_quarter (column : BurnolL2) (raw : ℝ → ℂ)
    (supported : originalPhysicalCutoff q column = column) : exteriorRead column raw = 0 := by
  unfold exteriorRead
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae (cutoff_ae_zero q column supported),
    ae_restrict_mem (measurableSet_symmetricInterval q).compl] with x zero outside
  rw [zero outside, star_zero, zero_mul]
  rfl

theorem exterior_integrable (column value : BurnolL2) (raw tail : ℝ → ℂ) (mean : ℂ)
    (regular : Integrable (column : ℝ → ℂ)) (read : (value : ℝ → ℂ) =ᵐ[volume] raw)
    (split : ∀ x : ℝ, raw x = mean + if x ∈ symmetricInterval q then 0 else tail x) :
    IntegrableOn (fun x : ℝ => star (column x) * tail x) (symmetricInterval q)ᶜ := by
  have product : Integrable (fun x : ℝ => star (column x) * raw x) := by
    apply (L2.integrable_inner (𝕜 := ℂ) column value).congr
    filter_upwards [read] with x actual
    rw [actual]
    simp only [RCLike.inner_apply, starRingEnd_apply, mul_comm]
  have conjugate : Integrable (fun x : ℝ => star (column x)) :=
    (@RCLike.conjLIE ℂ _).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp regular
  apply (integrable_indicator_iff (measurableSet_symmetricInterval q).compl).mp
  apply (product.sub (conjugate.const_mul mean)).congr
  filter_upwards with x
  change star (column x) * raw x - mean * star (column x) = _
  rw [split x]
  by_cases inside : x ∈ symmetricInterval q
  · rw [if_pos inside, indicator_of_notMem (show x ∉ (symmetricInterval q)ᶜ from not_not_intro inside)]
    ring
  · rw [if_neg inside, indicator_of_mem (show x ∈ (symmetricInterval q)ᶜ from inside)]
    ring

theorem exterior_integral_eq_scaled (shift : ℝ) (nonnegative : 0 ≤ shift) (f : ℝ → ℂ)
    (regular : IntegrableOn f (symmetricInterval q)ᶜ)
    (even : (fun x : ℝ => f (-x)) =ᵐ[volume] f)
    (supported : ∀ᵐ x : ℝ ∂volume, x ∉ symmetricInterval (q * Real.exp shift) → f x = 0) :
    (∫ x : ℝ in (symmetricInterval q)ᶜ, f x) =
      (2 : ℂ) * (Real.exp shift : ℂ) *
        ∫ y : ℝ in (q * Real.exp (-shift))..q, f (Real.exp shift * y) := by
  have leftSubset : Iio (-q) ⊆ (symmetricInterval q)ᶜ := by
    intro x hx inside
    exact not_lt_of_ge inside.1 hx
  have rightSubset : Ioi q ⊆ (symmetricInterval q)ᶜ := by
    intro x hx inside
    exact not_lt_of_ge inside.2 hx
  have reflection : (fun x : ℝ => (Iio (-q)).indicator f (-x)) =ᵐ[volume]
      (Ioi q).indicator f := by
    filter_upwards [even] with x same
    by_cases positive : q < x
    · rw [indicator_of_mem (show -x ∈ Iio (-q) by change -x < -q; linarith),
        indicator_of_mem (show x ∈ Ioi q from positive), same]
    · rw [indicator_of_notMem (show -x ∉ Iio (-q) by change ¬ -x < -q; linarith),
        indicator_of_notMem (show x ∉ Ioi q from positive)]
  have negative : (∫ x : ℝ in Iio (-q), f x) = ∫ x : ℝ in Ioi q, f x := by
    calc
      _ = ∫ x : ℝ, (Iio (-q)).indicator f x := (integral_indicator measurableSet_Iio).symm
      _ = ∫ x : ℝ, (Iio (-q)).indicator f (-x) :=
        (integral_neg_eq_self ((Iio (-q)).indicator f) volume).symm
      _ = ∫ x : ℝ, (Ioi q).indicator f x := integral_congr_ae reflection
      _ = _ := integral_indicator measurableSet_Ioi
  have positiveBand : (∫ x : ℝ in Ioi q, f x) =
      ∫ x : ℝ in Ioc q (q * Real.exp shift), f x := by
    apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioi.nullMeasurableSet
      Ioc_subset_Ioi_self
    filter_upwards [supported] with x zero inside
    apply zero
    intro inRadius
    exact inside.2 ⟨inside.1, inRadius.2⟩
  have disjoint : Disjoint (Iio (-q)) (Ioi q) := by
    apply Set.disjoint_left.mpr
    intro x negative positive
    change x < -q at negative
    change q < x at positive
    linarith
  have interval : q ≤ q * Real.exp shift := by
    nlinarith [Real.one_le_exp_iff.mpr nonnegative]
  have endpoints : Real.exp shift * (q * Real.exp (-shift)) = q := by
    rw [Real.exp_neg]
    field_simp
  have scaled := intervalIntegral.integral_comp_mul_left f (Real.exp_ne_zero shift)
    (a := q * Real.exp (-shift)) (b := q)
  rw [endpoints, mul_comm (Real.exp shift) q,
    intervalIntegral.integral_of_le interval] at scaled
  rw [show (symmetricInterval q)ᶜ = Iio (-q) ∪ Ioi q by
    ext x
    simp only [symmetricInterval, mem_compl_iff, mem_Icc, mem_union, mem_Iio, mem_Ioi,
      not_and_or, not_le],
    setIntegral_union disjoint measurableSet_Ioi (regular.mono_set leftSubset) (regular.mono_set rightSubset),
    negative, positiveBand, scaled]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  field_simp
  ring

end
end OriginalRieszFinitePairing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

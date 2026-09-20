import H0mework.Realization.Relaxation.P225

/-!
# Proposition 226: scalar parameter non-uniqueness for target-general relaxation

P225 proves the target-general scalar law

  `x -> x + sigma * (target - x)`.

This file proves a deliberately small parameter-relativity fact: the scalar
law and its interval-safety condition do not select a unique rate.  Even in the
same interval, for the same `x` and `target`, both endpoint rates `0` and `1`
are valid, and when `x ≠ target` they produce different transitions.

Boundary: this is not a derivation of physical constants, a standard-model
claim, or a proof that all physical constants are instantiation settings.  It
only formalizes the local scalar point that the relaxation form constrains
rates without uniquely fixing them.
-/

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Valid scalar rates -/

/-- A scalar rate is valid for interval-preserving relaxation when it lies in
`[0, 1]`. -/
def ValidRate (sigma : ℝ) : Prop :=
  0 <= sigma ∧ sigma <= 1

theorem validRate_zero : ValidRate 0 := by
  constructor <;> norm_num

theorem validRate_one : ValidRate 1 := by
  constructor <;> norm_num

/-- The scalar interval-safety law admits at least two distinct valid rates. -/
theorem validRate_nonunique : ∃ sigma tau : ℝ,
    ValidRate sigma ∧ ValidRate tau ∧ sigma ≠ tau := by
  refine ⟨0, 1, validRate_zero, validRate_one, ?_⟩
  norm_num

/-! ## The same law allows distinct transitions -/

/-- Endpoint rates produce different transitions whenever the point has not
already reached the target. -/
theorem endpoint_rates_produce_distinct_relaxations
    (target x : ℝ) (hx : x ≠ target) :
    relaxTo target 0 x ≠ relaxTo target 1 x := by
  simpa [relaxTo_zero, relaxTo_one] using hx

/-- In any interval containing both `x` and `target`, the interval-preserving
scalar law admits two distinct valid instantiations of the rate.

This is the local algebraic content of "the law fixes the form but does not
choose a unique parameter value." -/
theorem interval_law_admits_distinct_rate_instantiations
    (lo hi target x : ℝ)
    (hx_ne_target : x ≠ target)
    (hx0 : lo <= x) (hx1 : x <= hi)
    (ht0 : lo <= target) (ht1 : target <= hi) :
    ∃ sigma tau : ℝ,
      ValidRate sigma ∧ ValidRate tau ∧ sigma ≠ tau ∧
      (lo <= relaxTo target sigma x ∧ relaxTo target sigma x <= hi) ∧
      (lo <= relaxTo target tau x ∧ relaxTo target tau x <= hi) ∧
      relaxTo target sigma x ≠ relaxTo target tau x := by
  refine ⟨0, 1, validRate_zero, validRate_one, ?_, ?_, ?_, ?_⟩
  · norm_num
  · exact relaxTo_mem_Icc lo hi target 0 x hx0 hx1 ht0 ht1
      validRate_zero.1 validRate_zero.2
  · exact relaxTo_mem_Icc lo hi target 1 x hx0 hx1 ht0 ht1
      validRate_one.1 validRate_one.2
  · exact endpoint_rates_produce_distinct_relaxations target x hx_ne_target

/-!
  Summary:
  - P225 fixes the scalar target-general relaxation law.
  - P226 shows that this law, plus `[0, 1]` interval safety, does not by itself
    select a unique scalar rate.
  - Parameter values therefore require extra instantiation data or extra
    physical constraints; they are not forced by the scalar relaxation syntax
    alone.
-/


end AffineRelaxation
end SaturationMonoid

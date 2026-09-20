import H0mework.Realization.RelaxationFlow.P500

/-!
# Proposition 501: runtime/inverse-valid intersection is only the boundary

P500 classifies when the noisy-OR field inverse is runtime-valid.  This file
packages the immediate intersection consequence:

* in the nonabsorbing domain, a runtime-valid rate whose inverse is also
  runtime-valid must be exactly `0`;
* if one does not exclude the absorbing boundary `1`, Lean's totalized field
  division adds the expected artifact `1`.

This is the small algebraic guardrail behind the prose distinction between
positive anti-nag runtime flow and inverse-branch projection/growth.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Intersection of runtime-valid and inverse-valid branches -/

/-- THEOREM 1: the field inverse of zero is zero. -/
theorem satOrFieldInv_zero :
    SatOrFieldAlgebra.satOrFieldInv (0 : ℝ) = 0 := by
  unfold SatOrFieldAlgebra.satOrFieldInv
  norm_num

/-- THEOREM 2: Lean's totalized field inverse sends the absorbing boundary to
zero.  Algebraically, `sigma=1` is excluded from the nonabsorbing inverse
group; this theorem records only the totalized-field computation. -/
theorem satOrFieldInv_one_totalized :
    SatOrFieldAlgebra.satOrFieldInv (1 : ℝ) = 0 := by
  unfold SatOrFieldAlgebra.satOrFieldInv
  norm_num

/-- THEOREM 3: in the nonabsorbing domain, the runtime-valid branch and the
inverse-valid branch intersect exactly at the no-op boundary `0`. -/
theorem runtime_valid_and_inverse_valid_nonabsorbing_iff_zero
    {sigma : ℝ} (hne : sigma ≠ 1) :
    (ValidRate sigma ∧
      ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)) ↔
      sigma = 0 := by
  constructor
  · intro h
    have hnonpos :=
      nonpos_of_validRate_satOrFieldInv_of_ne_one hne h.2
    have hnonneg : 0 <= sigma := h.1.1
    linarith
  · intro hzero
    subst sigma
    constructor
    · exact validRate_zero
    · simpa [satOrFieldInv_zero] using validRate_zero

/-- THEOREM 4: without excluding `sigma=1`, the totalized-field intersection is
`{0,1}`.  The `1` case is an absorbing-boundary artifact of totalized division,
not a genuine nonabsorbing inverse. -/
theorem runtime_valid_and_inverse_valid_iff_zero_or_absorbing_totalized
    {sigma : ℝ} :
    (ValidRate sigma ∧
      ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)) ↔
      sigma = 0 ∨ sigma = 1 := by
  constructor
  · intro h
    by_cases hone : sigma = 1
    · exact Or.inr hone
    · left
      exact
        (runtime_valid_and_inverse_valid_nonabsorbing_iff_zero hone).mp h
  · intro h
    rcases h with hzero | hone
    · subst sigma
      constructor
      · exact validRate_zero
      · simpa [satOrFieldInv_zero] using validRate_zero
    · subst sigma
      constructor
      · exact validRate_one
      · simpa [satOrFieldInv_one_totalized] using validRate_zero

/-- THEOREM 5: every strictly positive nonabsorbing runtime-valid scalar is
disjoint from the inverse-valid branch. -/
theorem positive_runtime_valid_disjoint_from_inverse_valid
    {sigma : ℝ} (_hvalid : ValidRate sigma) (hpos : 0 < sigma)
    (hne : sigma ≠ 1) :
    ¬ ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma) := by
  exact satOrFieldInv_not_validRate_of_pos_ne_one hpos hne

/-! ## Bundled receipt -/

/-- Compact receipt for the runtime/inverse intersection boundary. -/
structure RuntimeInverseIntersectionBoundaryReceipt : Prop where
  inverse_zero :
    SatOrFieldAlgebra.satOrFieldInv (0 : ℝ) = 0
  inverse_one_totalized :
    SatOrFieldAlgebra.satOrFieldInv (1 : ℝ) = 0
  nonabsorbing_intersection_zero :
    ∀ sigma : ℝ, sigma ≠ 1 ->
      ((ValidRate sigma ∧
        ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)) ↔
        sigma = 0)
  totalized_intersection_zero_or_one :
    ∀ sigma : ℝ,
      ((ValidRate sigma ∧
        ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)) ↔
        sigma = 0 ∨ sigma = 1)
  positive_nonabsorbing_disjoint :
    ∀ sigma : ℝ, ValidRate sigma -> 0 < sigma -> sigma ≠ 1 ->
      ¬ ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)

/-- THEOREM 6: the only safe overlap between the runtime branch and inverse
branch is the boundary recorded above. -/
theorem runtimeInverseIntersectionBoundaryReceipt :
    RuntimeInverseIntersectionBoundaryReceipt where
  inverse_zero := satOrFieldInv_zero
  inverse_one_totalized := satOrFieldInv_one_totalized
  nonabsorbing_intersection_zero := fun _ hne =>
    runtime_valid_and_inverse_valid_nonabsorbing_iff_zero hne
  totalized_intersection_zero_or_one := fun _ =>
    runtime_valid_and_inverse_valid_iff_zero_or_absorbing_totalized
  positive_nonabsorbing_disjoint := fun _ hvalid hpos hne =>
    positive_runtime_valid_disjoint_from_inverse_valid hvalid hpos hne

end AffineRelaxation
end SaturationMonoid

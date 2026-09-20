import H0mework.Realization.RelaxationFlow.P499

/-!
# Proposition 500: exact runtime-validity classification for inverse rates

P499 proves the safety-critical direction: a genuine positive anti-nag rate
`0 < sigma < 1` has a noisy-OR field inverse outside the runtime-safe rate
interval `[0,1]`.

This file closes the small remaining gap.  Away from the absorbing boundary
`sigma = 1`, the field inverse

```lean
SatOrFieldAlgebra.satOrFieldInv sigma = sigma / (sigma - 1)
```

is runtime-valid exactly when the original rate is nonpositive.  Thus the
inverse branch is a field/projection branch, not a positive runtime salience
update branch.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Safe inverse rates are exactly the nonpositive branch -/

/-- THEOREM 1: if the original scalar is nonpositive, its noisy-OR field
inverse is a runtime-valid rate. -/
theorem validRate_satOrFieldInv_of_nonpos
    {sigma : ℝ} (hσ : sigma <= 0) :
    ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma) := by
  unfold SatOrFieldAlgebra.satOrFieldInv ValidRate
  constructor
  · exact div_nonneg_of_nonpos hσ (by linarith)
  · exact div_le_one_of_ge (by linarith) (by linarith)

/-- THEOREM 2: away from the absorbing boundary, runtime-validity of the
field inverse forces the original scalar to be nonpositive. -/
theorem nonpos_of_validRate_satOrFieldInv_of_ne_one
    {sigma : ℝ} (hne : sigma ≠ 1)
    (hvalid : ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)) :
    sigma <= 0 := by
  by_contra hnot
  have hpos : 0 < sigma := lt_of_not_ge hnot
  by_cases hlt : sigma < 1
  · exact (satOrFieldInv_not_validRate_of_mem_Ioo hpos hlt) hvalid
  · have hgt : 1 < sigma := by
      exact lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hne)
    have hdenpos : 0 < sigma - 1 := by
      linarith
    have hinv_gt_one :
        1 < SatOrFieldAlgebra.satOrFieldInv sigma := by
      unfold SatOrFieldAlgebra.satOrFieldInv
      rw [lt_div_iff₀ hdenpos]
      linarith
    exact (not_le_of_gt hinv_gt_one) hvalid.2

/-- THEOREM 3: exact nonabsorbing classification.  The noisy-OR field inverse
is runtime-valid iff the original scalar is nonpositive. -/
theorem satOrFieldInv_validRate_iff_nonpos_of_ne_one
    {sigma : ℝ} (hne : sigma ≠ 1) :
    ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma) ↔ sigma <= 0 := by
  constructor
  · exact nonpos_of_validRate_satOrFieldInv_of_ne_one hne
  · exact validRate_satOrFieldInv_of_nonpos

/-- THEOREM 4: positive nonabsorbing scalars have invalid inverse rates.  This
extends P499 from `(0,1)` to all `0 < sigma`, `sigma ≠ 1`. -/
theorem satOrFieldInv_not_validRate_of_pos_ne_one
    {sigma : ℝ} (hpos : 0 < sigma) (hne : sigma ≠ 1) :
    ¬ ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma) := by
  intro hvalid
  have hnonpos :=
    nonpos_of_validRate_satOrFieldInv_of_ne_one hne hvalid
  linarith

/-! ## Bundled receipt -/

/-- Compact receipt for the inverse-domain classification. -/
structure InverseBranchRuntimeValidityClassificationReceipt : Prop where
  valid_inverse_of_nonpos :
    ∀ sigma : ℝ, sigma <= 0 ->
      ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)
  nonpos_of_valid_inverse_nonabsorbing :
    ∀ sigma : ℝ, sigma ≠ 1 ->
      ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma) ->
        sigma <= 0
  valid_inverse_iff_nonpos_nonabsorbing :
    ∀ sigma : ℝ, sigma ≠ 1 ->
      (ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma) ↔ sigma <= 0)
  positive_nonabsorbing_inverse_not_valid :
    ∀ sigma : ℝ, 0 < sigma -> sigma ≠ 1 ->
      ¬ ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)
  positive_runtime_inverse_not_valid :
    ∀ sigma : ℝ, 0 < sigma -> sigma < 1 ->
      ¬ ValidRate (SatOrFieldAlgebra.satOrFieldInv sigma)

/-- THEOREM 5: the inverse branch is runtime-valid exactly on the nonpositive
nonabsorbing side. -/
theorem inverseBranchRuntimeValidityClassificationReceipt :
    InverseBranchRuntimeValidityClassificationReceipt where
  valid_inverse_of_nonpos := fun _ hσ =>
    validRate_satOrFieldInv_of_nonpos hσ
  nonpos_of_valid_inverse_nonabsorbing := fun _ hne hvalid =>
    nonpos_of_validRate_satOrFieldInv_of_ne_one hne hvalid
  valid_inverse_iff_nonpos_nonabsorbing := fun _ hne =>
    satOrFieldInv_validRate_iff_nonpos_of_ne_one hne
  positive_nonabsorbing_inverse_not_valid := fun _ hpos hne =>
    satOrFieldInv_not_validRate_of_pos_ne_one hpos hne
  positive_runtime_inverse_not_valid := fun _ hpos hlt =>
    satOrFieldInv_not_validRate_of_mem_Ioo hpos hlt

end AffineRelaxation
end SaturationMonoid

import H0mework.Physics.AlphaSources.P529

/-!
# Proposition 530: exact alpha_s partial-source accounting

P529 proves that the explicit four-source `alpha_s` receipt is the exact normal
form of the residual-gap producer.  This file adds the accounting law that makes
that normal form producer-facing:

* a selected subfamily closes the displayed residual exactly iff the omitted
  source contributions sum to zero;
* therefore no partial calculation may silently claim closure unless it also
  proves the omitted sector is null.

This is still not the numerical threshold / three-loop / extra-representation
calculation.  It is the machine-checked conservation law that such a calculation
must satisfy.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open scoped BigOperators

namespace AlphaStrongFourSourceClosureReceipt

/-! ## Selected and omitted source sums -/

/-- Contribution function that keeps exactly the selected source families. -/
def selectedContribution
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool) :
    AlphaStrongResidualSource -> ℚ :=
  fun s => if selected s then R.contribution s else 0

/-- Contribution function that keeps exactly the omitted source families. -/
def omittedContribution
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool) :
    AlphaStrongResidualSource -> ℚ :=
  fun s => if selected s then 0 else R.contribution s

/-- Sum of the selected physical source families. -/
def selectedSum
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool) : ℚ :=
  ∑ s : AlphaStrongResidualSource, R.selectedContribution selected s

/-- Sum of the omitted physical source families. -/
def omittedSum
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool) : ℚ :=
  ∑ s : AlphaStrongResidualSource, R.omittedContribution selected s

/-- THEOREM 1: selected and omitted contributions recombine pointwise to the
original four-source contribution. -/
theorem selectedContribution_add_omittedContribution
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool)
    (s : AlphaStrongResidualSource) :
    R.selectedContribution selected s +
        R.omittedContribution selected s =
      R.contribution s := by
  cases h : selected s <;>
    simp [selectedContribution, omittedContribution, h]

/-- THEOREM 2: selected and omitted sums recombine to the alpha-level residual
gap. -/
theorem selectedSum_add_omittedSum_eq_gap
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool) :
    R.selectedSum selected + R.omittedSum selected =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
  unfold selectedSum omittedSum
  rw [← Finset.sum_add_distrib]
  calc
    (∑ s : AlphaStrongResidualSource,
        (R.selectedContribution selected s +
          R.omittedContribution selected s)) =
        ∑ s : AlphaStrongResidualSource, R.contribution s := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact R.selectedContribution_add_omittedContribution selected s
    _ = alphaStrongTwoLoopSMDisplayedGap ℚ := R.univ_sum_eq_gap

/-- THEOREM 3: if the selected source families already close the alpha-level
residual, the omitted contribution must be exactly zero. -/
theorem omittedSum_eq_zero_of_selectedSum_eq_gap
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool)
    (hselected :
      R.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ) :
    R.omittedSum selected = 0 := by
  have hsplit := R.selectedSum_add_omittedSum_eq_gap selected
  linarith

/-- THEOREM 4: if the omitted source families sum to zero, the selected source
families close the alpha-level residual. -/
theorem selectedSum_eq_gap_of_omittedSum_eq_zero
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool)
    (homitted : R.omittedSum selected = 0) :
    R.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ := by
  have hsplit := R.selectedSum_add_omittedSum_eq_gap selected
  linarith

/-- THEOREM 5: exact partial-source accounting.  A partial source selection can
claim alpha-level closure iff the omitted source families are null. -/
theorem selectedSum_eq_gap_iff_omittedSum_eq_zero
    (R : AlphaStrongFourSourceClosureReceipt)
    (selected : AlphaStrongResidualSource -> Bool) :
    R.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ ↔
      R.omittedSum selected = 0 :=
  ⟨R.omittedSum_eq_zero_of_selectedSum_eq_gap selected,
    R.selectedSum_eq_gap_of_omittedSum_eq_zero selected⟩

/-- THEOREM 6: the empty selected family cannot close the alpha-level residual. -/
theorem selectedSum_empty_ne_gap
    (R : AlphaStrongFourSourceClosureReceipt) :
    R.selectedSum (fun _ => false) ≠ alphaStrongTwoLoopSMDisplayedGap ℚ := by
  intro hselected
  have homitted := R.omittedSum_eq_zero_of_selectedSum_eq_gap
    (fun _ => false) hselected
  have hgap : R.omittedSum (fun _ => false) =
      alphaStrongTwoLoopSMDisplayedGap ℚ := by
    unfold omittedSum omittedContribution
    simp [alphaStrongResidualSource_univ_sum]
    simpa [alphaStrongResidualSource_univ_sum] using R.univ_sum_eq_gap
  have hpos : 0 < alphaStrongTwoLoopSMDisplayedGap ℚ :=
    alphaStrongTwoLoopSMDisplayedGap_pos
  linarith

end AlphaStrongFourSourceClosureReceipt

/-! ## Bundled accounting certificate -/

/-- Compact accounting certificate for partial alpha_s source calculations. -/
structure AlphaStrongPartialSourceAccountingCertificate where
  selected_plus_omitted :
    ∀ (R : AlphaStrongFourSourceClosureReceipt)
      (selected : AlphaStrongResidualSource -> Bool),
      R.selectedSum selected + R.omittedSum selected =
        alphaStrongTwoLoopSMDisplayedGap ℚ
  partial_closure_iff_omitted_null :
    ∀ (R : AlphaStrongFourSourceClosureReceipt)
      (selected : AlphaStrongResidualSource -> Bool),
      R.selectedSum selected = alphaStrongTwoLoopSMDisplayedGap ℚ ↔
        R.omittedSum selected = 0
  empty_selection_never_closes :
    ∀ R : AlphaStrongFourSourceClosureReceipt,
      R.selectedSum (fun _ => false) ≠
        alphaStrongTwoLoopSMDisplayedGap ℚ

/-- THEOREM 7: the exact partial-source accounting certificate. -/
theorem alphaStrongPartialSourceAccountingCertificate :
    AlphaStrongPartialSourceAccountingCertificate where
  selected_plus_omitted := fun R selected =>
    R.selectedSum_add_omittedSum_eq_gap selected
  partial_closure_iff_omitted_null := fun R selected =>
    R.selectedSum_eq_gap_iff_omittedSum_eq_zero selected
  empty_selection_never_closes := fun R =>
    R.selectedSum_empty_ne_gap

end StandardModelConstraint
end SaturationMonoid

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.BudgetMap
import Mathlib.Order.Lattice.Nat

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot CategoryTheory

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
  (cut : Nat) (original : rows root boundary cut)

def values : Set Nat := {value | ∃ j, ∃ h : cut ≤ j,
  ((diagram root boundary).map (homOfLE h) original).progressBudget = value}

def minimumBudget := sInf (values root boundary cut original)

theorem actual_budget_values_are_nonempty : (values root boundary cut original).Nonempty :=
  ⟨_,cut,Nat.le_refl cut,rfl⟩

theorem the_minimum_budget_is_actually_attained :
    ∃ j, ∃ h : cut ≤ j, ((diagram root boundary).map (homOfLE h) original).progressBudget =
      minimumBudget root boundary cut original :=
  Nat.sInf_mem (actual_budget_values_are_nonempty root boundary cut original)

theorem the_minimum_is_below_every_actual_descendant (j : Nat) (h : cut ≤ j) :
    minimumBudget root boundary cut original ≤ ((diagram root boundary).map (homOfLE h) original).progressBudget :=
  Nat.sInf_le ⟨j,h,rfl⟩

theorem the_minimum_cannot_create_new_credit : minimumBudget root boundary cut original ≤ original.progressBudget := by
  have initial := the_minimum_is_below_every_actual_descendant root boundary cut original cut (Nat.le_refl cut)
  rw [the_zero_length_arrow_is_the_original_row] at initial
  exact initial

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

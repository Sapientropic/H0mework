import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Minimum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot CategoryTheory

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

theorem the_attained_budget_is_independent_of_the_actual_cut
    (i j : Nat) (hij : i ≤ j) (original : rows root boundary i) :
    minimumBudget root boundary j ((diagram root boundary).map (homOfLE hij) original) =
      minimumBudget root boundary i original := by
  apply Nat.le_antisymm
  · obtain ⟨k,hik,attained⟩ := the_minimum_budget_is_actually_attained root boundary i original
    have aboveJ := Nat.le_max_left j k
    have aboveK := Nat.le_max_right j k
    have bound := the_minimum_is_below_every_actual_descendant root boundary j
      ((diagram root boundary).map (homOfLE hij) original) (max j k) aboveJ
    have spent := every_canonical_past_arrow_preserves_the_original_budget_bound root boundary
      k (max j k) aboveK ((diagram root boundary).map (homOfLE hik) original)
    have same := (actual_arrows_compose root boundary i j (max j k) hij aboveJ original).symm.trans
      (actual_arrows_compose root boundary i k (max j k) hik aboveK original)
    rw [same] at bound
    exact bound.trans (spent.trans_eq attained)
  · obtain ⟨k,hjk,attained⟩ := the_minimum_budget_is_actually_attained root boundary j
      ((diagram root boundary).map (homOfLE hij) original)
    have bound := the_minimum_is_below_every_actual_descendant root boundary i original k (hij.trans hjk)
    rw [actual_arrows_compose root boundary i j k hij hjk] at bound
    exact bound.trans_eq attained

def budgetTransformation : diagram root boundary ⟶ (Functor.const ℕ).obj Nat :=
  NatTrans.ofSequence (fun n => TypeCat.ofHom (minimumBudget root boundary n)) (by
    intro n
    rw [show (diagram root boundary).map (homOfLE (Nat.le_add_right n 1)) =
      TypeCat.ofHom (step root boundary n) from Functor.ofSequence_map_homOfLE_succ _ n]
    ext original
    have compatible := the_attained_budget_is_independent_of_the_actual_cut root boundary n (n + 1)
      (Nat.le_add_right n 1) original
    rw [show (diagram root boundary).map (homOfLE (Nat.le_add_right n 1)) =
      TypeCat.ofHom (step root boundary n) from Functor.ofSequence_map_homOfLE_succ _ n] at compatible
    exact compatible)

def budgetCocone : (diagram root boundary).CoconeTypes where
  pt := Nat
  ι := minimumBudget root boundary
  ι_naturality := by
    intro i j arrow
    funext original
    exact congrArg (fun h : rows root boundary i ⟶ Nat => h original)
      ((budgetTransformation root boundary).naturality arrow)

def budget : Carrier root boundary → Nat := (diagram root boundary).descColimitType (budgetCocone root boundary)

theorem the_completion_reads_the_attained_original_budget (cut : Nat) (original : rows root boundary cut) :
    budget root boundary (includeRow root boundary cut original) = minimumBudget root boundary cut original := rfl

theorem completed_original_budgets_never_refill (cut : Nat) (original : rows root boundary cut) :
    budget root boundary (includeRow root boundary cut original) ≤ original.progressBudget :=
  the_minimum_cannot_create_new_credit root boundary cut original

theorem paid_original_rows_stay_paid_in_the_completion (cut : Nat) (original : rows root boundary cut)
    (paid : original.progressBudget = 0) : budget root boundary (includeRow root boundary cut original) = 0 := by
  have bound := completed_original_budgets_never_refill root boundary cut original
  rw [paid] at bound
  exact Nat.eq_zero_of_le_zero bound

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

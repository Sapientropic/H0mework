import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Diagram

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot CategoryTheory

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

theorem the_zero_length_arrow_is_the_original_row (i : Nat) (original : rows root boundary i) :
    (diagram root boundary).map (homOfLE (Nat.le_refl i)) original = original := by
  rw [show (homOfLE (Nat.le_refl i) : i ⟶ i) = 𝟙 i from rfl,
    (diagram root boundary).map_id i]
  rfl

theorem actual_arrows_compose (i j k : Nat) (hij : i ≤ j) (hjk : j ≤ k)
    (original : rows root boundary i) :
    (diagram root boundary).map (homOfLE (hij.trans hjk)) original =
      (diagram root boundary).map (homOfLE hjk) ((diagram root boundary).map (homOfLE hij) original) := by
  rw [show (homOfLE (hij.trans hjk) : i ⟶ k) = homOfLE hij ≫ homOfLE hjk from Subsingleton.elim _ _,
    (diagram root boundary).map_comp]
  rfl

theorem every_canonical_past_arrow_preserves_the_original_budget_bound
    (i j : Nat) (h : i ≤ j) (original : rows root boundary i) :
    ((diagram root boundary).map (homOfLE h) original).progressBudget ≤ original.progressBudget := by
  induction j,h using Nat.le_induction with
  | base =>
      rw [the_zero_length_arrow_is_the_original_row]
  | succ j h earlier =>
      have arrow : (homOfLE (Nat.le.step h) : i ⟶ j + 1) =
          homOfLE h ≫ homOfLE (Nat.le_add_right j 1) := Subsingleton.elim _ _
      have evaluated : (diagram root boundary).map (homOfLE (Nat.le.step h)) original =
          step root boundary j ((diagram root boundary).map (homOfLE h) original) := by
        rw [arrow,Functor.map_comp]
        rw [show (diagram root boundary).map (homOfLE (Nat.le_add_right j 1)) =
          TypeCat.ofHom (step root boundary j) from Functor.ofSequence_map_homOfLE_succ _ j]
        rfl
      rw [evaluated]
      exact (the_original_compiler_keeps_the_same_claim_and_never_refills root
        (.finite (boundary.history.visitAt j)) (boundary.history.next_eq_at_visit j)
        ((diagram root boundary).map (homOfLE h) original)).2.trans earlier

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

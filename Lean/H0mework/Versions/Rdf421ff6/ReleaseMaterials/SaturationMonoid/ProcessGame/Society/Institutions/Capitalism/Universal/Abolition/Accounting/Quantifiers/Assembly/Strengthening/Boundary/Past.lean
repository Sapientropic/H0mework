import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Successor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
  (cut : Nat)
  (original : OpenResponsibilityAt N (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt cut).current))

/-- Rows are restrictions of this already emitted cofinal event's canonical
past, never a supplied future family or a new admission at its landing. -/
def pastRow : (n : Nat) → OpenResponsibilityAt N (root.toAuthoritativeRoot.toRoot.supportAt (boundary.history.visitAt (cut + n)).current)
  | 0 => original
  | n + 1 => root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (boundary.history.next_eq_at_visit (cut + n)) (pastRow n)

theorem every_past_row_keeps_its_original_claim (n : Nat) : (pastRow root boundary cut original n).claim = original.claim := by
  induction n with
  | zero => rfl
  | succ n earlier =>
      exact (the_original_compiler_keeps_the_same_claim_and_never_refills root (.finite (boundary.history.visitAt (cut + n)))
        (boundary.history.next_eq_at_visit (cut + n)) (pastRow root boundary cut original n)).1.trans earlier

theorem the_next_past_row_has_no_free_renewal (n : Nat) :
    (pastRow root boundary cut original (n + 1)).progressBudget ≤ (pastRow root boundary cut original n).progressBudget :=
  (the_original_compiler_keeps_the_same_claim_and_never_refills root (.finite (boundary.history.visitAt (cut + n)))
    (boundary.history.next_eq_at_visit (cut + n)) (pastRow root boundary cut original n)).2

theorem every_past_budget_is_bounded_by_its_own_original_row (n : Nat) :
    (pastRow root boundary cut original n).progressBudget ≤ original.progressBudget := by
  induction n with
  | zero => exact le_rfl
  | succ n earlier => exact (the_next_past_row_has_no_free_renewal root boundary cut original n).trans earlier

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary

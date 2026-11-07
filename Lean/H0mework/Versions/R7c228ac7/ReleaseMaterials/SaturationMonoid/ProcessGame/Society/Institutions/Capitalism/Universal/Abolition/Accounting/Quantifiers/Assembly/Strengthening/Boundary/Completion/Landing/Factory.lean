import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Root
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Inventory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Emission
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.WriteBack
import H0mework.Versions.R2.Foundation.Authority.EntryDisposition

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

structure CompleteAt : Type where
  private mk ::
  compatible : Compatible root boundary

/-- Source coordinates select registration or the exact original failure.
No landing entry, compatible family, compiler or success certificate is input. -/
def registerFromActualEvent : CompleteAt root boundary ⊕ LineageFailure root boundary :=
  match inspectCompatibility root boundary with
  | .inl evidence => .inl ⟨evidence.down⟩
  | .inr failure => .inr failure

namespace CompleteAt
variable {root boundary}

def entry (admitted : CompleteAt root boundary) (point : Carrier root boundary) :=
  landingRow root boundary point (admitted.compatible point)

def row (admitted : CompleteAt root boundary) (point : Carrier root boundary) :=
  generatedRow root boundary (.cofinal (actualVisit root boundary)) (admitted.entry point)

def authority (admitted : CompleteAt root boundary) (point : Carrier root boundary) :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromCofinalRow
    (completedRoot root boundary) (actualVisit root boundary) (admitted.entry point) (admitted.row point)

def answerAndNext (admitted : CompleteAt root boundary) (point : Carrier root boundary) :=
  (completedRoot root boundary).generatedCausalEntryAnswerAndNextAt (.cofinal (actualVisit root boundary))
    (admitted.entry point) (admitted.authority point)

theorem answer_is_the_same_source_generated_next (admitted : CompleteAt root boundary) (point : Carrier root boundary) :
    (admitted.answerAndNext point).nextCurrent = (completedRoot root boundary).generatedNextCurrentAt
      (.cofinal (actualVisit root boundary)) := rfl

theorem every_original_claim_is_registered_without_refill (admitted : CompleteAt root boundary)
    (cut : Nat) (original : rows root boundary cut) :
    (admitted.entry (includeRow root boundary cut original)).claim = original.claim ∧
      (admitted.entry (includeRow root boundary cut original)).progressBudget ≤ original.progressBudget :=
  ⟨the_completion_reads_each_literal_original_claim root boundary cut original,
    completed_original_budgets_never_refill root boundary cut original⟩

theorem every_original_landing_row_is_retained (admitted : CompleteAt root boundary)
    (original : OldLanding root boundary) :
    (completePresentation root boundary admitted.compatible).backward
      ((completePresentation root boundary admitted.compatible).forward (.inl original)) = .inl original := rfl

end CompleteAt
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

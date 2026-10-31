import H0mework.Foundation.Cofinal.TemporalAnswer
import H0mework.Checks.Runtime.RootNativeLedgerCompilerRegression

/-!
# No-Free Starvation regression

A live entry may remain present at arbitrarily many fresh causal visits, but
presence is not operational standing authority.  Without a source-native
incidence row, terminal row, maintenance debit, or another typed disposition,
no visit can renew the exact entry.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace NoFreeStarvationRegression

open ConstructiveRoot
open SourceNativeLedgerCompilerRegression

/-- The fixture is a genuine self-loop with a nonempty world ledger.  Each
successor is nevertheless a fresh causal root visit. -/
def visitAt : Nat → RootVisit root.toRoot
  | 0 => root.toRoot.initialVisit
  | n + 1 => (visitAt n).next rfl

@[simp] theorem visitAt_current (n : Nat) : (visitAt n).current = () := by
  induction n with
  | zero => rfl
  | succ n _induction => rfl

/-- Every visit receives its own visit-indexed root receipt. -/
def authorityAt (n : Nat) :
    SourceNativeTemporalVisitGeneratedEvolutionAt root (.finite (visitAt n)) :=
  root.generatedAtTemporalVisit (.finite (visitAt n))

/-- The same open responsibility remains a member of each visit's structural
ledger.  This membership alone carries no transition receipt. -/
theorem live_entry_exists_at_every_visit (n : Nat) :
    Nonempty (root.toRoot.ledgerAt (visitAt n).current).Entry := by
  rw [visitAt_current]
  exact ⟨falseEntry⟩

/-- The source-native row law emits no incidence occurrence capable of paying
the `falseEntry → falseEntry` carry. -/
theorem no_exact_incidence_event_pays_the_carry :
    IsEmpty
      (writeRowSource.IncidenceOccurrenceAt
        (emitted ()) falseEntry falseEntry) := by
  constructor
  intro event
  exact nomatch event

/-- Each visit uses the same empty finite patch; no changed row is hidden in
an independently supplied whole-ledger receipt. -/
theorem every_visit_uses_empty_identity_patch (n : Nat) :
    (authorityAt n).currentPatch = root.generatedPatchAt () := by
  rw [(authorityAt n).currentPatch_eq]
  have current_eq := visitAt_current n
  cases current_eq
  rfl

/-- Consequently no fresh visit grants generated exact-entry authority for
the merely present responsibility. -/
theorem no_visit_grants_entry_authority (n : Nat) :
    IsEmpty ((authorityAt n).GeneratedEntryRowAt falseEntry) := by
  constructor
  intro authority
  exact Fin.elim0 authority.sourceRow.1

/-- Arbitrarily long finite presence remains distinct from generated
exact-entry authority. -/
theorem arbitrary_finite_unpaid_presence :
    ∀ n,
      Nonempty (root.toRoot.ledgerAt (visitAt n).current).Entry ∧
      IsEmpty ((authorityAt n).GeneratedEntryRowAt falseEntry) :=
  fun n => ⟨live_entry_exists_at_every_visit n,
    no_visit_grants_entry_authority n⟩

end NoFreeStarvationRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

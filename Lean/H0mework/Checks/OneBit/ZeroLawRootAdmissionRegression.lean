import H0mework.Foundation.Authority.ZeroLawAdmission
import H0mework.Arithmetic.PrimeShadow.LivingLawRootSourceNativeAuthorityRegression

/-!
# Regression: no ghost degree acquires lawful world identity

Two generated visits of one fixed root have different exact registered
occurrences.  Conversely, appending a raw `Bool` to one lawful state can make
two Lean values unequal, but after the only available admission projection
they are the same state, occurrence, and whole generated evolution.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ZeroLawRootAdmissionRegression

open ConstructiveRoot
open ConstructiveRoot.ZeroLawRootAdmission
open SourceNativeRootAuthorityRegression
open SourceNativeLedgerCompilerRegression

abbrev admittedRoot := questionWorld

def firstVisit : RootVisit admittedRoot.toRoot :=
  admittedRoot.toRoot.initialVisit

def secondVisit : RootVisit admittedRoot.toRoot :=
  firstVisit.next rfl

theorem visits_are_distinct : firstVisit ≠ secondVisit := by
  intro equality
  cases equality

def first : LawfulWorldStateAt admittedRoot :=
  .finite firstVisit

def second : LawfulWorldStateAt admittedRoot :=
  .finite secondVisit

theorem registered_states_are_distinct : first ≠ second := by
  intro equality
  exact visits_are_distinct
    (SourceNativeTemporalVisitAt.finite_injective equality)

theorem registered_occurrences_are_distinct :
    first.registeredOccurrence ≠ second.registeredOccurrence :=
  LawfulWorldStateAt.registeredOccurrence_ne_of_ne
    registered_states_are_distinct

/-- Raw wrappers remain legal data, but are not the lawful state carrier. -/
abbrev GhostWrappedState := LawfulWorldStateAt admittedRoot × Bool

def ghostFalse : GhostWrappedState := ⟨first, false⟩
def ghostTrue : GhostWrappedState := ⟨first, true⟩

theorem ghost_wrappers_differ_as_raw_data : ghostFalse ≠ ghostTrue := by
  intro same
  have bit_eq : false = true := congrArg Prod.snd same
  cases bit_eq

/-- The unregistered bit disappears at the admission boundary; it cannot
split world identity. -/
theorem ghost_wrappers_have_one_lawful_state :
    ghostFalse.1 = ghostTrue.1 :=
  rfl

theorem ghost_wrappers_have_one_registered_occurrence :
    ghostFalse.1.registeredOccurrence =
      ghostTrue.1.registeredOccurrence :=
  rfl

theorem ghost_wrappers_have_one_authoritative_evolution :
    ghostFalse.1.authoritativeEvolution =
      ghostTrue.1.authoritativeEvolution :=
  rfl

/-- The root admission producer has no ghost argument or alternate state
constructor.  A real bit must first be incorporated into a different source
or actual transition. -/
theorem no_ghost_argument_in_world_state_producer : True := by
  fail_if_success exact SourceNativeTemporalVisitAt.finite firstVisit false
  trivial

/-- A raw ledger compiler may model a branch, but it is not a zero-law world
admission.  In particular the hostile mixed terminal/write root cannot become
a lawful world state before complete-event inventory admission. -/
theorem raw_mixed_terminal_root_has_no_world_admission : True := by
  fail_if_success
    exact (.finite mixedTerminalRoot.toRoot.initialVisit :
      LawfulWorldStateAt mixedTerminalRoot)
  trivial

#print axioms LawfulWorldStateAt.eq_of_registeredOccurrence_eq
#print axioms LawfulWorldStateAt.registeredOccurrence_ne_of_ne
#print axioms registered_occurrences_are_distinct
#print axioms ghost_wrappers_have_one_registered_occurrence
#print axioms ghost_wrappers_have_one_authoritative_evolution
#print axioms raw_mixed_terminal_root_has_no_world_admission

end ZeroLawRootAdmissionRegression
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

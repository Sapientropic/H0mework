import H0mework.Foundation.Cofinal.ProductiveHistory
import H0mework.Versions.R2.Foundation.Arithmetic.TerminalAuthority

/-!
# Productive fixed-root arithmetic continuation

A source-owned productive fixed-root history already proves that the exact
root compiler emits a successor at every current.  This kernel rejects a
terminal directly at the same exact emitted root occurrence; it introduces
no second continuation carrier.

For every concrete finite visit, the root evolution and productive history
name the same next current.  Hence a source-native arithmetic terminal at that
same visit is empty.  The conclusion is pointwise in `Nat`: no completed
future-state field or caller-selected occurrence is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

open RootArithmeticTerminalAuthority

universe u

namespace ProductiveFiniteRootHistoryAt

variable
  {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {root : SourceNativeAuthoritativeRootClosure N V}

/-- Fixed-root productive history and root-local arithmetic index agree at
every finite visit. -/
theorem visitAt_arithmeticIndex
    (history : ProductiveFiniteRootHistoryAt root.toLedgerRoot)
    (n : Nat) :
    rootVisitArithmeticIndex (history.visitAt n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [history.visitAt_succ]
      rw [RootVisit.next_arithmeticIndex, ih]

/-- A productive fixed root has no source-native arithmetic terminal at any
of its concretely generated finite visits. -/
theorem noArithmeticTerminalAt
    (history : ProductiveFiniteRootHistoryAt root.toLedgerRoot)
    (n : Nat) :
    IsEmpty (GeneratedRootArithmeticTerminalAt root (history.visitAt n)) :=
  ⟨fun terminal => by
    have next_eq := history.next_eq_at_visit n
    change
      (root.source.restructuringSource.source.toRootSource.actual.compile
        (root.emitted (history.visitAt n).current)).nextCurrent? =
          some (history.currentAt (n + 1)) at next_eq
    rw [terminal.structural_eq] at next_eq
    cases next_eq⟩

/-- The root-native terminal classifier is definitionally empty at every
productive finite visit.  No registration court participates in this
classification. -/
theorem canonicalTerminalClassifier_eq_none
    (history : ProductiveFiniteRootHistoryAt root.toLedgerRoot)
    (n : Nat) :
    generateRootArithmeticTerminalAt? root (history.visitAt n) = none := by
  match classifier_eq :
      generateRootArithmeticTerminalAt? root (history.visitAt n) with
  | none => rfl
  | some terminal =>
      exact False.elim <| (history.noArithmeticTerminalAt n).false terminal

end ProductiveFiniteRootHistoryAt
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

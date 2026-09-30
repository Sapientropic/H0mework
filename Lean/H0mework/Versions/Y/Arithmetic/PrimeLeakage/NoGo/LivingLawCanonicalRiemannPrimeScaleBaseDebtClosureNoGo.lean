import H0mework.Foundation.Responsibility.NoetherianClosure
import H0mework.Versions.Y.Arithmetic.PrimeLeakage.PrimeScaleCofinalClosedEffect

/-!
# The closed prime effect is not a debt on the canonical base row

The joint faithful authority reuses the canonical arithmetic ledger source.
That base row has budget zero, has no faithful terminal and is transported by
budget equality.  Instantiating the generic Noetherian no-go therefore rules
out treating the already closed `.sourceBoundary` trace event as a finite debt
on that row.

This does not reject a genuinely source-generated activated debt with its own
positive budget, strict payment and exact terminal.  It rejects only the lost-
premise route that relabels the old zero-budget row as such a debt.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open CanonicalUnitArithmeticRoot

noncomputable section

def runtimeJointFaithfulTemporalDepth?
    (current : SourceNativeLivingRootCurrentAt N) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

@[simp] theorem runtimeJointFaithfulVisitAt_depth
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    runtimeJointFaithfulTemporalDepth?
      ⟨V, runtimeJointFaithfulRoot observation nontrivial,
        runtimeJointFaithfulVisitAt observation nontrivial depth⟩ = some depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change some (ProductiveFiniteRootHistoryAt.causalDepth
        (CanonicalUnitArithmeticRoot.finiteVisit depth).history + 1) =
          some (depth + 1)
      have prior : ProductiveFiniteRootHistoryAt.causalDepth
          (CanonicalUnitArithmeticRoot.finiteVisit depth).history = depth := by
        change some (ProductiveFiniteRootHistoryAt.causalDepth
          (CanonicalUnitArithmeticRoot.finiteVisit depth).history) = some depth
            at inductionHypothesis
        exact Option.some.inj inductionHypothesis
      rw [prior]

/-- The existing faithful joint root as one exact living process. -/
def runtimeJointFaithfulProcess
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeLivingRootProcess N where
  State := Nat
  stateAt := fun depth =>
    ⟨V, runtimeJointFaithfulRoot observation nontrivial,
      runtimeJointFaithfulVisitAt observation nontrivial depth⟩
  stateAt_injective := by
    intro left right equality
    have depth_eq := congrArg runtimeJointFaithfulTemporalDepth? equality
    rw [runtimeJointFaithfulVisitAt_depth observation nontrivial left,
      runtimeJointFaithfulVisitAt_depth observation nontrivial right] at depth_eq
    exact Option.some.inj depth_eq
  initial := 0
  successorAt := fun depth => ⟨depth + 1, rfl, by rfl⟩

/-- The only pre-existing canonical ledger row, viewed at the joint root's
initial current. -/
def runtimeJointFaithfulBaseDebtCurrent
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeRootDebtCurrentAt
      (runtimeJointFaithfulProcess observation nontrivial)
      (rootLedgerEntry initialCurrent) where
  state := (runtimeJointFaithfulProcess observation nontrivial).initial
  entry := rootLedgerEntry initialCurrent
  sameDebt := ⟨rfl, rfl⟩

theorem runtimeJointFaithfulBaseDebtCurrent_budget_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    (runtimeJointFaithfulBaseDebtCurrent observation nontrivial).budget = 0 := by
  rfl

abbrev runtimeJointFaithfulBaseDebtCurrent_noLocalTerminal
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IsEmpty (SourceNativeRootDebtLocalTerminalAt
      (runtimeJointFaithfulBaseDebtCurrent observation nontrivial)) :=
  { false := fun terminal => nomatch terminal.terminal }

abbrev runtimeJointFaithfulBaseDebtCurrent_noPaidContinuation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IsEmpty (SourceNativePaidRootDebtMacroContinuationAt
      (runtimeJointFaithfulBaseDebtCurrent observation nontrivial)) :=
  no_paidRootDebtMacroContinuation_of_budget_eq_zero
    (runtimeJointFaithfulBaseDebtCurrent observation nontrivial)
    (runtimeJointFaithfulBaseDebtCurrent_budget_eq_zero observation nontrivial)

/-- The old canonical row cannot be promoted to a total paid-debt lifecycle.
The underlying generic no-go is axiom-free; this exact-root specialization
retains the surrounding standard T1 provenance. -/
abbrev runtimeJointFaithfulBaseDebtCurrent_noNoetherianClosure
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IsEmpty (SourceNativeNoetherianDebtClosureLaw
      (runtimeJointFaithfulProcess observation nontrivial)
      (rootLedgerEntry initialCurrent)) :=
  no_noetherianDebtClosureLaw_of_budget_eq_zero_of_noLocalTerminal
    (runtimeJointFaithfulBaseDebtCurrent observation nontrivial)
    (runtimeJointFaithfulBaseDebtCurrent_budget_eq_zero observation nontrivial)
    (runtimeJointFaithfulBaseDebtCurrent_noLocalTerminal observation nontrivial)

end
end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

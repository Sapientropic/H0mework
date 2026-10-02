import H0mework.Versions.R2.Arithmetic.Goldbach.EffectiveDisposition

/-!
# Exact-occurrence additive calculation unfolding

The historical finite calculation fixed `initialStep`.  This producer keeps
the same generated target arithmetic while indexing every calculation node by
the exact occurrence currently read by a runtime projection.  No root equality
is used as a substitute for occurrence identity.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticExactOccurrenceAdditiveProducer

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticRoot
open RootArithmeticUnfoldingFace

universe u

/-- One calculation point whose root occurrence is definitionally selected by
the enclosing runtime projection. -/
structure ExactOccurrenceAdditivePointAt
    {Occurrence : Type u} (occurrence : Occurrence) : Type u where
  private mk ::
  rootOccurrence : Occurrence
  rootOccurrence_eq : rootOccurrence = occurrence
  payload : UnitHistory

def exactAdditivePoint {Occurrence : Type u}
    (occurrence : Occurrence) (history : UnitHistory) :
    ExactOccurrenceAdditivePointAt occurrence :=
  ⟨occurrence, rfl, history⟩

def calculationOccurrenceFrom {Occurrence : Type u}
    (occurrence : Occurrence) (history : UnitHistory) : Nat →
      RootedAccountedUnfolding (ExactOccurrenceAdditivePointAt occurrence)
  | 0 => RootedAccountedUnfolding.zero
      (exactAdditivePoint occurrence history)
  | fuel + 1 =>
      .occur (exactAdditivePoint occurrence history) <|
        .singleton
          (calculationOccurrenceFrom occurrence
            (CanonicalUnitArithmeticRoot.next history) fuel)

def terminalHistoryAlgebra {Occurrence : Type u}
    {occurrence : Occurrence}
    (point : ExactOccurrenceAdditivePointAt occurrence)
    (children : List UnitHistory) : UnitHistory :=
  match children with
  | [] => point.payload
  | head :: _tail => head

theorem fold_calculationOccurrenceFrom_eq_generatedTargetFrom
    {Occurrence : Type u} (occurrence : Occurrence)
    (history : UnitHistory) (fuel : Nat) :
    (calculationOccurrenceFrom occurrence history fuel).fold
        terminalHistoryAlgebra =
      generatedTargetFrom history fuel := by
  induction fuel generalizing history with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      change
        (calculationOccurrenceFrom occurrence
            (CanonicalUnitArithmeticRoot.next history) fuel).fold
              terminalHistoryAlgebra =
          generatedTargetFrom
            (CanonicalUnitArithmeticRoot.next history) fuel
      exact inductionHypothesis _

def evenTargetOccurrenceAt {Occurrence : Type u}
    (occurrence : Occurrence) (index : Nat) :
    RootedAccountedUnfolding (ExactOccurrenceAdditivePointAt occurrence) :=
  calculationOccurrenceFrom occurrence unitHistory (evenTargetFuel index)

def evenTargetHistoryAt {Occurrence : Type u}
    (occurrence : Occurrence) (index : Nat) : UnitHistory :=
  (evenTargetOccurrenceAt occurrence index).fold terminalHistoryAlgebra

theorem evenTargetHistoryAt_eq {Occurrence : Type u}
    (occurrence : Occurrence) (index : Nat) :
    evenTargetHistoryAt occurrence index = evenTargetHistory index := by
  calc
    evenTargetHistoryAt occurrence index =
        generatedTargetFrom unitHistory (evenTargetFuel index) :=
      fold_calculationOccurrenceFrom_eq_generatedTargetFrom
        occurrence unitHistory (evenTargetFuel index)
    _ = evenTargetHistory index := by
      rw [evenTargetHistory, evenTargetOccurrence,
        CanonicalUnitArithmeticEffectiveAdditiveProducer.fold_calculationOccurrenceFrom_eq_generatedTargetFrom]

theorem evenTargetHistoryAt_eq_generate {Occurrence : Type u}
    (occurrence : Occurrence) (index : Nat) :
    evenTargetHistoryAt occurrence index =
      UnitHistory.generate (2 * (index + 1)) := by
  rw [evenTargetHistoryAt_eq, evenTargetHistory_eq_generate]

theorem calculation_points_share_exact_occurrence
    {Occurrence : Type u} {occurrence : Occurrence}
    (point : ExactOccurrenceAdditivePointAt occurrence) :
    point.rootOccurrence = occurrence :=
  point.rootOccurrence_eq

theorem evenTargetOccurrenceAt_root_is_exact
    {Occurrence : Type u} (occurrence : Occurrence) (index : Nat) :
    (evenTargetOccurrenceAt occurrence index).root.rootOccurrence = occurrence :=
  calculation_points_share_exact_occurrence _

end CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

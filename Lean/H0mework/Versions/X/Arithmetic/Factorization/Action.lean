import H0mework.Versions.X.Arithmetic.UnitArithmetic.Factorization

/-! The original factorial joint step generates its complete valuation increment. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFactorizationAction

open ArithmeticGeneration CanonicalUnitArithmeticFactorizationOccurrence

noncomputable section

def increment (history : UnitHistory) : Nat →₀ Nat :=
  history.next.cardinalShadow.factorization

theorem source_step (history : UnitHistory) :
    factorization history.next = factorization history + increment history := by
  change (factorialHistory history.next).cardinalShadow.factorization =
    (factorialHistory history).cardinalShadow.factorization + history.next.cardinalShadow.factorization
  rw [factorialHistory, UnitHistory.cardinalShadow_joint]
  exact Nat.factorization_mul
    (by rw [factorialHistory_cardinalShadow]; exact Nat.factorial_ne_zero _)
    (by change history.cardinalShadow + 1 ≠ 0; omega)

theorem source_two_steps (history : UnitHistory) :
    factorization history.next.next = factorization history + (increment history + increment history.next) := by
  rw [source_step, source_step, add_assoc]

theorem old_material_retained (history : UnitHistory) :
    factorization history ≤ factorization history.next := by
  rw [source_step]
  intro prime
  exact Nat.le_add_right _ _

theorem source_step_at (history : UnitHistory) (prime : Nat) :
    factorization history.next prime = factorization history prime + increment history prime :=
  DFunLike.congr_fun (source_step history) prime

end
end SourceFactorizationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

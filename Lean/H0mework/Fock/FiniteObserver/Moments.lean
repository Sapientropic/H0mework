import H0mework.Fock.FiniteObserver.Gram

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

def weight (bound : Nat) (actor : Fin (bound + 1)) : ℚ := (actor.val + 1 : Nat)

def count (bound : Nat) : ℚ := bound + 1

def firstMoment (bound : Nat) : ℚ := ∑ actor, weight bound actor

def secondMoment (bound : Nat) : ℚ := ∑ actor, weight bound actor ^ 2

def determinant (bound scale : Nat) : ℚ :=
  (count bound + 1) * (1 + (scale : ℚ) ^ 2 * secondMoment bound) - (scale : ℚ) ^ 2 * firstMoment bound ^ 2

theorem moment_cauchy (bound : Nat) : firstMoment bound ^ 2 ≤ count bound * secondMoment bound := by
  have paid := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (bound + 1)))
    (fun _ => (1 : ℚ)) (weight bound)
  simpa only [firstMoment, secondMoment, count, one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] using paid

theorem determinant_positive (bound scale : Nat) : 0 < determinant bound scale := by
  have cauchy := moment_cauchy bound
  have nonnegative : 0 ≤ secondMoment bound := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have correction : 0 ≤ (count bound + 1) * secondMoment bound - firstMoment bound ^ 2 := by
    nlinarith only [cauchy, nonnegative]
  have positive : 0 < count bound + 1 := by unfold count; positivity
  have paid := mul_nonneg (sq_nonneg (scale : ℚ)) correction
  unfold determinant
  nlinarith only [positive, paid]

end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

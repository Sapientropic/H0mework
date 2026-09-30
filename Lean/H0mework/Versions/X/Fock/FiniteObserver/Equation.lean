import H0mework.Versions.X.Fock.FiniteObserver.Solve

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

theorem sum_solve (bound scale : Nat) (response : Fin (bound + 1) → ℚ) :
    (∑ actor, solve bound scale response actor) = massAnswer bound scale response := by
  have source : (∑ actor, solve bound scale response actor) =
      responseSum bound response - count bound * massAnswer bound scale response -
        (scale : ℚ) ^ 2 * firstMoment bound * clockAnswer bound scale response := by
    simp only [solve, responseSum, count, firstMoment, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    push_cast
    ring
  have paid := first_equation bound scale response
  rw [source]
  nlinarith only [paid]

theorem moment_solve (bound scale : Nat) (response : Fin (bound + 1) → ℚ) :
    (∑ actor, weight bound actor * solve bound scale response actor) = clockAnswer bound scale response := by
  have source : (∑ actor, weight bound actor * solve bound scale response actor) =
      responseMoment bound response - firstMoment bound * massAnswer bound scale response -
        (scale : ℚ) ^ 2 * secondMoment bound * clockAnswer bound scale response := by
    calc
      _ = ∑ actor, (weight bound actor * response actor - weight bound actor * massAnswer bound scale response -
        ((scale : ℚ) ^ 2 * clockAnswer bound scale response) * weight bound actor ^ 2) := by
          apply Finset.sum_congr rfl
          intro actor _
          unfold solve
          ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib]
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        change responseMoment bound response - firstMoment bound * massAnswer bound scale response -
          ((scale : ℚ) ^ 2 * clockAnswer bound scale response) * secondMoment bound = _
        ring
  have paid := second_equation bound scale response
  rw [source]
  nlinarith only [paid]

theorem solve_equation (bound scale : Nat) (response : Fin (bound + 1) → ℚ) (actor : Fin (bound + 1)) :
    solve bound scale response actor + (∑ source, solve bound scale response source) +
      (scale : ℚ) ^ 2 * weight bound actor * (∑ source, weight bound source * solve bound scale response source) = response actor := by
  rw [sum_solve, moment_solve, solve]
  ring

end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

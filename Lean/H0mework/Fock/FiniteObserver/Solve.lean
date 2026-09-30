import H0mework.Fock.FiniteObserver.Moments

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

def responseSum (bound : Nat) (response : Fin (bound + 1) → ℚ) : ℚ := ∑ actor, response actor

def responseMoment (bound : Nat) (response : Fin (bound + 1) → ℚ) : ℚ :=
  ∑ actor, weight bound actor * response actor

def massAnswer (bound scale : Nat) (response : Fin (bound + 1) → ℚ) : ℚ :=
  ((1 + (scale : ℚ) ^ 2 * secondMoment bound) * responseSum bound response -
    (scale : ℚ) ^ 2 * firstMoment bound * responseMoment bound response) / determinant bound scale

def clockAnswer (bound scale : Nat) (response : Fin (bound + 1) → ℚ) : ℚ :=
  ((count bound + 1) * responseMoment bound response - firstMoment bound * responseSum bound response) / determinant bound scale

def solve (bound scale : Nat) (response : Fin (bound + 1) → ℚ) (actor : Fin (bound + 1)) : ℚ :=
  response actor - massAnswer bound scale response - (scale : ℚ) ^ 2 * weight bound actor * clockAnswer bound scale response

theorem first_equation (bound scale : Nat) (response : Fin (bound + 1) → ℚ) :
    (count bound + 1) * massAnswer bound scale response + (scale : ℚ) ^ 2 * firstMoment bound * clockAnswer bound scale response =
      responseSum bound response := by
  unfold massAnswer clockAnswer
  field_simp [ne_of_gt (determinant_positive bound scale)]
  unfold determinant
  ring

theorem second_equation (bound scale : Nat) (response : Fin (bound + 1) → ℚ) :
    firstMoment bound * massAnswer bound scale response + (1 + (scale : ℚ) ^ 2 * secondMoment bound) * clockAnswer bound scale response =
      responseMoment bound response := by
  unfold massAnswer clockAnswer
  field_simp [ne_of_gt (determinant_positive bound scale)]
  unfold determinant
  ring

end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

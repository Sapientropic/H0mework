import H0mework.Fock.CopyFiniteComplete.Observation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNormalInverse

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceConditionalCorrection (one clockMean ratio direction)
open scoped InnerProductSpace
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def massSolve (bound : Nat) (query : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) query)) : Space (observed (historyPMF bound) query) :=
  value - ((ratio bound : ℂ) * inner ℂ (one bound query) value) • one bound query

theorem mass_solve_clock (bound : Nat) (query : Fin (bound + 1) → Observed) :
    massSolve bound query (clockMean bound query) = direction bound query := rfl

theorem mass_equation (bound : Nat) (query : Fin (bound + 1) → Observed)
    (value : Space (observed (historyPMF bound) query)) :
    massSolve bound query value +
      ((bound + 1 : ℂ) * inner ℂ (one bound query) (massSolve bound query value)) • one bound query = value := by
  have unit : inner ℂ (one bound query) (one bound query) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, SourceConditionalCorrection.one_norm]
    norm_num
  unfold massSolve
  rw [inner_sub_right, inner_smul_right, unit, mul_one, sub_eq_add_neg, ← neg_smul, add_assoc, ← add_smul]
  have coefficient : -((ratio bound : ℂ) * inner ℂ (one bound query) value) +
      (bound + 1 : ℂ) * (inner ℂ (one bound query) value -
        (ratio bound : ℂ) * inner ℂ (one bound query) value) = 0 := by
    unfold ratio
    push_cast
    have denominator : (bound + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : bound + 2 ≠ 0)
    field_simp
    ring
  rw [coefficient, zero_smul, add_zero]

end
end SourceNormalInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

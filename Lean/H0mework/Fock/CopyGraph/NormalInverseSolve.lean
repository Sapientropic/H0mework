import H0mework.Fock.CopyGraph.NormalInverseMass

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceNormalInverse

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceConditionalCorrection (one clockMean direction strength denominator)
open SourceCopyProgram (Index scale)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def solve (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (forcing : Space (observed (historyPMF bound) query)) : Space (observed (historyPMF bound) query) :=
  massSolve bound query forcing -
    ((strength depth bound index : ℂ) / (denominator depth bound index query : ℂ) *
      inner ℂ (clockMean bound query) (massSolve bound query forcing)) • direction bound query

theorem strength_coe (depth bound : Nat) (index : Index depth) :
    (strength depth bound index : ℂ) = (scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) := by
  unfold strength
  push_cast
  rfl

theorem denominator_coe (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    (denominator depth bound index query : ℂ) =
      1 + (strength depth bound index : ℂ) * (SourceConditionalCorrection.coupling bound query : ℂ) := by
  unfold denominator
  push_cast
  rfl

variable [MeasurableSingletonClass Observed]

theorem gram_mass (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (forcing : Space (observed (historyPMF bound) query)) :
    (SourceConditionalGraphDecoder.action depth bound index query).adjoint
      (SourceConditionalGraphDecoder.action depth bound index query (massSolve bound query forcing)) =
        forcing + ((strength depth bound index : ℂ) * inner ℂ (clockMean bound query) (massSolve bound query forcing)) •
          clockMean bound query := by
  rw [SourceConditionalCorrection.gram, mass_equation, strength_coe]

theorem gram_direction (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    (SourceConditionalGraphDecoder.action depth bound index query).adjoint
      (SourceConditionalGraphDecoder.action depth bound index query (direction bound query)) =
        (denominator depth bound index query : ℂ) • clockMean bound query := by
  rw [SourceConditionalCorrection.gram, SourceConditionalCorrection.direction_law, SourceConditionalCorrection.direction_pairing,
    ← strength_coe, denominator_coe, add_smul, one_smul]

theorem solve_equation (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (forcing : Space (observed (historyPMF bound) query)) :
    (SourceConditionalGraphDecoder.action depth bound index query).adjoint
      (SourceConditionalGraphDecoder.action depth bound index query (solve depth bound index query forcing)) = forcing := by
  rw [solve, map_sub, map_sub, map_smul, map_smul, gram_mass, gram_direction, smul_smul]
  have nonzero : (denominator depth bound index query : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (SourceConditionalCorrection.denominator_pos depth bound index query).ne'
  have coefficient : ((strength depth bound index : ℂ) / (denominator depth bound index query : ℂ) *
      inner ℂ (clockMean bound query) (massSolve bound query forcing)) * (denominator depth bound index query : ℂ) =
        (strength depth bound index : ℂ) * inner ℂ (clockMean bound query) (massSolve bound query forcing) := by
    field_simp
  rw [coefficient, add_sub_cancel_right]

end
end SourceNormalInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

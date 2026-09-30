import H0mework.Fock.CopyGraph.CorrectionDirection

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceConditionalGraphDecoder (action decode)
open SourceCopyProgram (Index scale)
noncomputable section
universe u
variable {Observed : Type u} [MeasurableSpace Observed]

def strength (depth bound : Nat) (index : Index depth) : ℝ := (scale depth index : ℝ) ^ 2 * (bound + 1 : ℝ)

def denominator (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) : ℝ :=
  1 + strength depth bound index * coupling bound query

def coefficient (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) : ℂ :=
  ((strength depth bound index : ℂ) * clockPair bound query value) / (denominator depth bound index query : ℂ)

def update (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) : Space (observed (historyPMF bound) query) :=
  coefficient depth bound index query value • direction bound query

theorem strength_pos (depth bound : Nat) (index : Index depth) : 0 < strength depth bound index := by
  unfold strength
  have positive : (0 : ℝ) < scale depth index := by exact_mod_cast SourceCopyProgram.scale_pos depth index
  exact mul_pos (sq_pos_of_pos positive) (by positivity)

theorem denominator_pos (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed) :
    0 < denominator depth bound index query := by
  unfold denominator
  have nonnegative := mul_nonneg (strength_pos depth bound index).le (coupling_nonneg bound query)
  linarith only [nonnegative]

theorem coefficient_balance (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    coefficient depth bound index query value + coefficient depth bound index query value *
      ((scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * (coupling bound query : ℂ)) =
        (scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * clockPair bound query value := by
  have nonzero : (denominator depth bound index query : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (denominator_pos depth bound index query).ne'
  have scaleRead : (strength depth bound index : ℂ) = (scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) := by
    unfold strength
    push_cast
    rfl
  have denominatorRead : (denominator depth bound index query : ℂ) =
      1 + (scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * (coupling bound query : ℂ) := by
    unfold denominator
    push_cast
    rw [scaleRead]
  unfold coefficient
  rw [scaleRead]
  rw [← mul_one_add]
  have total : 1 + (scale depth index : ℂ) ^ 2 * (bound + 1 : ℂ) * (coupling bound query : ℂ) =
      (denominator depth bound index query : ℂ) := denominatorRead.symm
  rw [total, div_mul_cancel₀ _ nonzero]

variable [MeasurableSingletonClass Observed]

theorem update_equation (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    (action depth bound index query).adjoint (action depth bound index query (update depth bound index query value)) =
      (action depth bound index query).adjoint
        (SourceConditionalGraph.copyRead depth bound index (residual (historyPMF bound) query value)) := by
  unfold update
  rw [map_smul, map_smul, gram, direction_law, direction_pairing, forcing,
    smul_add, smul_smul, ← add_smul, coefficient_balance]

theorem correction_is_update (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) : correction depth bound index query value = update depth bound index query value := by
  have generated := (source_equation depth bound index query value).trans (update_equation depth bound index query value).symm
  exact ((action depth bound index query).adjoint_comp_self_injective_iff.mpr
    (SourceConditionalGraphDecoder.source_injective depth bound index query)) generated

theorem decoder_formula (depth bound : Nat) (index : Index depth) (query : Fin (bound + 1) → Observed)
    (value : Space (historyPMF bound)) :
    decode depth bound index query (SourceConditionalGraph.copyRead depth bound index value) =
      transfer (historyPMF bound) query value + update depth bound index query value := by
  have generated := correction_is_update depth bound index query value
  change _ - _ = _ at generated
  exact (sub_eq_iff_eq_add.mp generated).trans (add_comm _ _)

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Fock.CopyGraph.TimeGramPairing

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyTimeGram

open SourceCopyProgram (Index scale)
open scoped Classical
noncomputable section

def meanPhase (depth : Nat) (index : Index depth) : ℝ :=
  (∑ phase : Fin (index.val + 1), (phase.val : ℝ)) / (scale depth index : ℝ)

def spread (depth : Nat) (index : Index depth) : ℝ :=
  ∑ phase : Fin (index.val + 1), ((phase.val : ℝ) - meanPhase depth index) ^ 2

def normalizer (depth : Nat) (index : Index depth) : ℝ :=
  (scale depth index : ℝ) + spread depth index / (scale depth index : ℝ) ^ 2

theorem scale_real_nonzero (depth : Nat) (index : Index depth) : (scale depth index : ℝ) ≠ 0 := by
  exact_mod_cast (SourceCopyProgram.scale_pos depth index).ne'

theorem phase_sum (depth : Nat) (index : Index depth) :
    (∑ phase : Fin (index.val + 1), (phase.val : ℝ)) = (scale depth index : ℝ) * meanPhase depth index := by
  unfold meanPhase
  field_simp [scale_real_nonzero depth index]

theorem square_sum (depth : Nat) (index : Index depth) :
    (∑ phase : Fin (index.val + 1), (phase.val : ℝ) ^ 2) =
      spread depth index + (scale depth index : ℝ) * meanPhase depth index ^ 2 := by
  have expanded : spread depth index =
      (∑ phase : Fin (index.val + 1), (phase.val : ℝ) ^ 2) -
        2 * meanPhase depth index * (∑ phase : Fin (index.val + 1), (phase.val : ℝ)) +
        (scale depth index : ℝ) * meanPhase depth index ^ 2 := by
    unfold spread
    calc
      (∑ phase : Fin (index.val + 1), ((phase.val : ℝ) - meanPhase depth index) ^ 2) =
          ∑ phase : Fin (index.val + 1), ((phase.val : ℝ) ^ 2 - 2 * meanPhase depth index * (phase.val : ℝ) + meanPhase depth index ^ 2) :=
        Finset.sum_congr rfl fun phase _ => by ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← SourceCopyProgram.scale_source depth index]
  rw [phase_sum] at expanded
  nlinarith only [expanded]

theorem normalizer_pos (depth : Nat) (index : Index depth) : 0 < normalizer depth index := by
  have size : (0 : ℝ) < scale depth index := by exact_mod_cast SourceCopyProgram.scale_pos depth index
  have variance : 0 ≤ spread depth index := Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold normalizer
  positivity

theorem normalizer_nonzero (depth : Nat) (index : Index depth) : (normalizer depth index : ℂ) ≠ 0 := by
  exact_mod_cast (normalizer_pos depth index).ne'

theorem phase_sum_complex (depth : Nat) (index : Index depth) :
    (∑ phase : Fin (index.val + 1), (phase.val : ℂ)) = (scale depth index : ℂ) * (meanPhase depth index : ℂ) := by
  exact_mod_cast phase_sum depth index

theorem square_sum_complex (depth : Nat) (index : Index depth) :
    (∑ phase : Fin (index.val + 1), (phase.val : ℂ) ^ 2) =
      (spread depth index : ℂ) + (scale depth index : ℂ) * (meanPhase depth index : ℂ) ^ 2 := by
  exact_mod_cast square_sum depth index

theorem normalizer_complex (depth : Nat) (index : Index depth) :
    (normalizer depth index : ℂ) =
      (scale depth index : ℂ) + (spread depth index : ℂ) / (scale depth index : ℂ) ^ 2 := by
  unfold normalizer
  push_cast
  rfl

end
end SourceCopyTimeGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Physics.LowEnergy.Quantum.FockFilteredWords
import H0mework.Physics.LowEnergy.Quantum.FockRaisingAudit

/-! Noncommuting grade-zero factors cannot invalidate the particle bound. -/
set_option autoImplicit false
namespace SourceFockFilteredWordsAudit
open SaturationMonoid.PhysicsCore
open LowEnergy QuantizationCheck.Fermion SourceFockRaising SourceFockRaisingAudit
open SourceFockFilteredWords
noncomputable section

abbrev D : End (ι := Fin 4) := grade target
abbrev R : End (ι := Fin 4) := Fermion.quantize raisingMatrix

theorem diagonal_preserves_number : total * D = D * total := by
  apply LinearMap.ext
  intro ψ
  funext s
  simp only [D, Module.End.mul_apply, total_apply, grade_apply]
  ring

theorem incoming_grade_zero : D incoming = 0 := by
  have h := basis_eigenstate (fun i : Fin 4 => if i ∈ target then (1 : ℂ) else 0)
    ({0, 1} : Finset (Fin 4))
  have coefficient : (∑ i ∈ ({0, 1} : Finset (Fin 4)),
      if i ∈ target then (1 : ℂ) else 0) = 0 := by
    norm_num [target]
    decide
  rw [coefficient, zero_smul] at h
  exact h

theorem actual_interleaved_second_word_nonzero : (R * D * R) incoming ≠ 0 := by
  have raises := quantize_raises_grade target raisingMatrix actual_matrix_raises
  have h := congrArg (fun T : End (ι := Fin 4) => T incoming) raises
  simp only [Module.End.mul_apply, LinearMap.add_apply, incoming_grade_zero, map_zero,
    zero_add] at h
  simpa only [Module.End.mul_apply, h] using actual_second_word_nonzero

theorem actual_interleaved_third_word_zero : (R * D * R * D * R) incoming = 0 := by
  have h := weighted_word_vanishes target [(1, R), (0, D), (1, R), (0, D), (1, R)]
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals first | exact quantize_preserves_number raisingMatrix | exact diagonal_preserves_number)
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact (by
            simp only [Nat.cast_one, one_smul]
            exact quantize_raises_grade target raisingMatrix actual_matrix_raises)
        | simp [D])
    2 (by decide) incoming incoming_number_sector
  simpa [List.prod_cons, mul_assoc] using h

#print axioms SourceFockFilteredWords.homogeneous_eigenstate
#print axioms SourceFockFilteredWords.word_eigenstate
#print axioms SourceFockFilteredWords.weighted_word_vanishes
#print axioms SourceFockFilteredWords.weighted_tensor_word_vanishes
#print axioms actual_interleaved_second_word_nonzero
#print axioms actual_interleaved_third_word_zero
end
end SourceFockFilteredWordsAudit

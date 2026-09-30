import H0mework.Physics.LowEnergy.Quantum.WavepacketInteraction

/-! Genuine two-body real-momentum consumers. Equal internal labels at
different momenta remain admissible. These waves are algebraic functions;
compact support, smooth-domain closure and time integrals are not assumed. -/
set_option autoImplicit false
namespace SourceWavepacketAudit
open SourceWavepacketInteraction
open scoped BigOperators
noncomputable section

abbrev Config := Configuration ℝ (Fin 2) 2
abbrev TestWave := Wave ℝ (Fin 2) ℂ 2

def sameInternalWave (x : Config) : ℂ :=
  if (x 0).2 = 0 ∧ (x 1).2 = 0 then ((x 0).1 - (x 1).1 : ℝ) else 0

theorem same_internal_is_alternating : Alternating sameInternalWave := by
  intro e
  have cases : e = 1 ∨ e = Equiv.swap 0 1 := by
    have all : ∀ p : Equiv.Perm (Fin 2), p = 1 ∨ p = Equiv.swap 0 1 := by decide
    exact all e
  rcases cases with rfl | rfl
  · ext x
    simp [permute]
  · ext x
    simp only [permute, LinearMap.coe_mk, AddHom.coe_mk, sameInternalWave,
      Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Equiv.Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide),
      Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      Pi.smul_apply, smul_eq_mul]
    by_cases h : (x 0).2 = 0 ∧ (x 1).2 = 0
    · rw [if_pos h, if_pos h.symm]
      push_cast
      ring
    · have reverse : ¬((x 1).2 = 0 ∧ (x 0).2 = 0) := fun h' => h h'.symm
      simp [h, reverse]

theorem same_internal_different_momenta_nonzero :
    sameInternalWave ![(1, 0), (0, 0)] = 1 := by
  norm_num [sameInternalWave]

theorem same_configuration_zero (p : ℝ) : sameInternalWave ![(p, 0), (p, 0)] = 0 := by
  simp [sameInternalWave]

def target : Finset (Fin 2) := {1}

def sourceMatrix (t p : ℝ) (i j : Fin 2) : ℂ :=
  if i = 1 ∧ j = 0 then ((t + p + 1 : ℝ) : ℂ) else 0

def shifts (_t : ℝ) (_a : Fin 1) (p : ℝ) : ℝ := p - 1

def kernels (t : ℝ) (_a : Fin 1) : ℝ → Fin 2 → Fin 2 → Module.End ℂ ℂ :=
  scalarKernel (sourceMatrix t) (LinearMap.id : Module.End ℂ ℂ)

theorem source_matrix_grade (t p : ℝ) (i j : Fin 2) :
    ((if i ∈ target then 1 else 0 : ℂ) -
      (if j ∈ target then 1 else 0 : ℂ) - 1) * sourceMatrix t p i j = 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [target, sourceMatrix, Fin.ext_iff]

theorem actual_kernel_support (t : ℝ) (a : Fin 1) (p : ℝ) (i j : Fin 2) :
    kernels t a p i j ≠ 0 → i ∈ target ∧ j ∉ target := by
  exact scalarKernel_support target (sourceMatrix t) LinearMap.id (source_matrix_grade t) p i j

theorem actual_family_preserves_alternating (t : ℝ) :
    Alternating (familyInteraction (shifts t) (kernels t) sameInternalWave) :=
  family_preserves_alternating (shifts t) (kernels t) sameInternalWave
    same_internal_is_alternating

theorem actual_three_time_word_zero (t u v : ℝ) :
    ([t, u, v].map (fun r => familyInteraction (N := 2) (shifts r) (kernels r))).prod = 0 := by
  exact time_ordered_family_word_zero target shifts kernels actual_kernel_support
    [t, u, v] (by simp)

theorem actual_two_insertions_survive :
    (familyInteraction (shifts 0) (kernels 0)
      (familyInteraction (shifts 0) (kernels 0) sameInternalWave))
        ![(2, 1), (0, 1)] = 12 := by
  norm_num [familyInteraction, interaction, lineAction, kernels, scalarKernel,
    sourceMatrix, shifts, sameInternalWave, Fin.sum_univ_one, Fin.sum_univ_two,
    Function.update_apply]

#print axioms SourceWavepacketGrade.finite_grade_decomposition
#print axioms SourceWavepacketGrade.eigenstate_above_bound
#print axioms SourceWavepacketGrade.word_eigenstate
#print axioms SourceWavepacketGrade.bounded_grade_word_zero
#print axioms SourceWavepacketInteraction.occupation_bound
#print axioms SourceWavepacketInteraction.occupation_update
#print axioms SourceWavepacketInteraction.line_raises_occupation
#print axioms SourceWavepacketInteraction.interaction_raises_occupation
#print axioms SourceWavepacketInteraction.ordered_wavepacket_word_zero
#print axioms SourceWavepacketInteraction.line_permutation
#print axioms SourceWavepacketInteraction.interaction_permutation
#print axioms SourceWavepacketInteraction.interaction_preserves_alternating
#print axioms SourceWavepacketInteraction.scalarKernel_support
#print axioms SourceWavepacketInteraction.family_raises_occupation
#print axioms SourceWavepacketInteraction.time_ordered_family_word_zero
#print axioms SourceWavepacketInteraction.family_preserves_alternating
#print axioms same_internal_is_alternating
#print axioms same_internal_different_momenta_nonzero
#print axioms same_configuration_zero
#print axioms source_matrix_grade
#print axioms actual_kernel_support
#print axioms actual_family_preserves_alternating
#print axioms actual_three_time_word_zero
#print axioms actual_two_insertions_survive

end
end SourceWavepacketAudit

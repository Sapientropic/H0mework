import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeCell.ReplayConditioning

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

open SourceSignedEvaluator ContinuousChart
open scoped BigOperators

theorem initial_error_recomputed : ∀ i j : Fin 3, initialError i j = reportedInitialError i j := by decide +kernel
theorem slack_recomputed : ∀ i : Fin 3, calculatedSlack i = reportedSlack i := by decide +kernel
theorem slack_equation : ∀ i : Fin 3, (∑ j : Fin 3, slackSystem i j * reportedSlack j) = 1 := by decide +kernel
theorem slack_positive : ∀ i : Fin 3, 0 < reportedSlack i := by decide +kernel
theorem weights_recomputed : ∀ i : Fin 3, calculatedWeights i = weights i := by decide +kernel
theorem weights_positive : ∀ i : Fin 3, 0 < weights i := by decide +kernel
theorem preconditioner_recomputed : ∀ i j : Fin 3, calculatedPreconditioner i j = preconditioner i j := by decide +kernel
theorem error_recomputed : ∀ i j : Fin 3, errorBox i j = reportedError i j := by decide +kernel
theorem norm_bound_recomputed : calculatedNormBound = normBound := by decide +kernel
theorem norm_bound_exact : normBound = (1005359 / 1048576 : ℚ) := by decide +kernel
theorem norm_bound_nonnegative : 0 ≤ normBound := by decide +kernel
theorem norm_bound_lt_one : normBound < 1 := by decide +kernel
theorem error_rows_small : ∀ i : Fin 3, (∑ j : Fin 3, magnitude (errorBox i j)) ≤ normBound := by
  intro i
  simp_rw [error_recomputed]
  fin_cases i <;> decide +kernel

theorem source_conditioning_calculated :
    type_of% initial_error_recomputed ∧ type_of% slack_recomputed ∧ type_of% slack_equation ∧
    type_of% slack_positive ∧ type_of% weights_recomputed ∧ type_of% weights_positive ∧
    type_of% preconditioner_recomputed ∧ type_of% error_recomputed ∧ type_of% norm_bound_recomputed ∧
    normBound = (1005359 / 1048576 : ℚ) ∧ 0 ≤ normBound ∧ normBound < 1 ∧ type_of% error_rows_small :=
  ⟨initial_error_recomputed, slack_recomputed, slack_equation, slack_positive, weights_recomputed,
    weights_positive, preconditioner_recomputed, error_recomputed, norm_bound_recomputed,
    norm_bound_exact, norm_bound_nonnegative, norm_bound_lt_one, error_rows_small⟩

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeCellReplay

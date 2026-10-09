import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.DiagonalRead

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Donor Propagation.Interface Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
attribute [local irreducible] E actualTopState originalTopProjector calculatedTopProjector originalToCalculated transformedOriginal

theorem actual_top_original_energy : (transformedOriginal*actualTopState).trace =
    (Preparation.sourceEnergies originalTop : ℂ) := by
  rw [← same_source_Hamiltonian]
  unfold actualTopState
  rw [BasisInverse.conjugation_pair,original_top_hamiltonian,Matrix.trace_smul]
  unfold originalTopProjector
  rw [Spectrum.basisPure_trace]
  simp

theorem recorded_diagonal_source : E = Matrix.diagonal (fun i => (calculatedEnergy i : ℂ)) := by
  unfold E calculatedEnergy
  push_cast
  rfl

theorem diagonal_top_remainder_norm : ‖Matrix.diagonal (fun i : Basis =>
    ((calculatedEnergy i-calculatedEnergy calculatedTop : ℝ) : ℂ))‖ ≤ 38 := by
  have identity : Matrix.diagonal (fun i : Basis => ((calculatedEnergy i-calculatedEnergy calculatedTop : ℝ) : ℂ)) =
      E-(calculatedEnergy calculatedTop : ℂ) • 1 := by
    rw [recorded_diagonal_source]
    ext i j
    by_cases same : i=j
    · subst j; simp
    · simp [same]
  have entry : ‖(calculatedEnergy calculatedTop : ℂ)‖ ≤ 19 := by
    have h := (matrix_entry_norm_le E calculatedTop calculatedTop).trans diagonal_norm
    rw [recorded_diagonal_source,Matrix.diagonal_apply_eq] at h
    exact h
  rw [identity]
  apply (norm_sub_le _ _).trans
  rw [norm_smul,norm_one,mul_one]
  linarith [diagonal_norm]

theorem actual_top_diagonal_energy_error :
    ‖(E*actualTopState).trace-(calculatedEnergy calculatedTop : ℂ)‖ ≤ (1/10^12 : ℝ) := by
  have h := diagonal_expectation_error (fun i => (calculatedEnergy i : ℂ)) actualTopState
    actual_top_state_positive actual_top_state_idempotent actual_top_state_trace calculatedTop
  rw [← recorded_diagonal_source,← calculatedTopProjector] at h
  have remainder : ‖Matrix.diagonal (fun i : Basis => (calculatedEnergy i : ℂ)-(calculatedEnergy calculatedTop : ℂ))‖ ≤ 38 := by
    simpa only [Complex.ofReal_sub] using diagonal_top_remainder_norm
  have leak := actual_top_complement_error
  have square := pow_le_pow_left₀ (norm_nonneg _) leak 2
  rw [show Fintype.card Basis = 98 from Fintype.card_fin 98] at h
  norm_num only [Nat.cast_ofNat] at h
  apply h.trans
  have count : 0 ≤ (98 : ℝ)*‖(1-calculatedTopProjector)*actualTopState‖^2 := by positivity
  have bound := mul_le_mul_of_nonneg_right remainder count
  nlinarith

theorem actual_top_energy_error : |Preparation.sourceEnergies originalTop-calculatedEnergy calculatedTop| ≤
    (22/10^12 : ℝ) := by
  have cost := complex_trace_norm_mass (transformedOriginal-E) actualTopState actual_top_state_positive
  rw [actual_top_state_trace,Complex.one_re,mul_one,Matrix.sub_mul,Matrix.trace_sub,actual_top_original_energy] at cost
  have source : ‖transformedOriginal-E‖ ≤ (21/10^12 : ℝ) := by
    unfold transformedOriginal
    exact actual_source_diagonal_error
  have triangle := norm_sub_le_norm_sub_add_norm_sub (Preparation.sourceEnergies originalTop : ℂ) (E*actualTopState).trace
    (calculatedEnergy calculatedTop : ℂ)
  have bound : ‖(Preparation.sourceEnergies originalTop : ℂ)-(calculatedEnergy calculatedTop : ℂ)‖ ≤
      (22/10^12 : ℝ) := by linarith [cost.trans source,actual_top_diagonal_energy_error]
  simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using bound

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

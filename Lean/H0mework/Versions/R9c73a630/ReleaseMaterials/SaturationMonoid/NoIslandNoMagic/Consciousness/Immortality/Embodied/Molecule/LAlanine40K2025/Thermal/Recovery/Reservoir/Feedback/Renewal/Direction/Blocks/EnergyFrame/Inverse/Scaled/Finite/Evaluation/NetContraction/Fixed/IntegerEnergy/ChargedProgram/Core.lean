import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.BlockPulseMultiply
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators

variable {α β γ δ : Type*}

theorem select_integer_columns [Fintype β]
    (A : MatrixInt α β) (B : MatrixInt β γ) (f : δ → γ) :
    submatrix (multiply A B) id f = multiply A (submatrix B id f) := by
  rcases A with ⟨ar,ai⟩
  rcases B with ⟨br,bi⟩
  rfl

theorem select_integer_rows [Fintype β]
    (A : MatrixInt α β) (B : MatrixInt β γ) (f : δ → α) :
    submatrix (multiply A B) f id = multiply (submatrix A f id) B := by
  rcases A with ⟨ar,ai⟩
  rcases B with ⟨br,bi⟩
  rfl

def pairRows (U L : MatrixInt α β) : MatrixInt (α ⊕ α) β :=
  ⟨fun i j => match i with | .inl x => U.re x j | .inr x => L.re x j,
   fun i j => match i with | .inl x => U.im x j | .inr x => L.im x j⟩

def pairCols (U L : MatrixInt α β) : MatrixInt α (β ⊕ β) :=
  ⟨fun i j => match j with | .inl x => U.re i x | .inr x => L.re i x,
   fun i j => match j with | .inl x => U.im i x | .inr x => L.im i x⟩

theorem pair_rows_decomposition (E : MatrixInt (α ⊕ α) β) :
    pairRows (submatrix E Sum.inl id) (submatrix E Sum.inr id) = E := by
  rcases E with ⟨er,ei⟩
  unfold pairRows submatrix
  congr 1 <;> funext i j <;> cases i <;> rfl

theorem pair_cols_decomposition (E : MatrixInt α (β ⊕ β)) :
    pairCols (submatrix E id Sum.inl) (submatrix E id Sum.inr) = E := by
  rcases E with ⟨er,ei⟩
  unfold pairCols submatrix
  congr 1 <;> funext i j <;> cases j <;> rfl

def chargedStep [Fintype α] (A D : MatrixInt α α)
    (E : MatrixInt (α ⊕ α) β) : MatrixInt (α ⊕ α) β :=
  pairRows (multiply A (submatrix E Sum.inl id))
    (multiply D (submatrix E Sum.inr id))

theorem charged_step_exact [Fintype α] (A D : MatrixInt α α)
    (E : MatrixInt (α ⊕ α) β) :
    chargedStep A D E =
      multiply (intFourBlocks A zeroIntBlock zeroIntBlock D) E := by
  apply matrix_int_eq_of_sum_submatrices
  · rw [block_pulse_multiply_upper]
    rfl
  · rw [block_pulse_multiply_lower]
    rfl

theorem adjoint_pair_rows (U L : MatrixInt α β) :
    adjoint (pairRows U L) = pairCols (adjoint U) (adjoint L) := by
  rcases U with ⟨ur,ui⟩
  rcases L with ⟨lr,li⟩
  unfold adjoint pairRows pairCols
  congr 1
  · funext i j
    cases j <;> rfl

theorem weighted_pair_columns [Fintype α]
    (U L : MatrixInt β α) (P : MatrixInt α α) :
    multiply (pairCols U L)
      (intFourBlocks P zeroIntBlock zeroIntBlock P) =
        pairCols (multiply U P) (multiply L P) := by
  apply matrix_int_eq_of_sum_columns
  · rw [multiply_block_pulse_upper]
    rfl
  · rw [multiply_block_pulse_lower]
    rfl

theorem cross_arm_rounding_not_additive :
    round (scale/2+scale/2) ≠ round (scale/2)+round (scale/2) := by
  decide +kernel

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

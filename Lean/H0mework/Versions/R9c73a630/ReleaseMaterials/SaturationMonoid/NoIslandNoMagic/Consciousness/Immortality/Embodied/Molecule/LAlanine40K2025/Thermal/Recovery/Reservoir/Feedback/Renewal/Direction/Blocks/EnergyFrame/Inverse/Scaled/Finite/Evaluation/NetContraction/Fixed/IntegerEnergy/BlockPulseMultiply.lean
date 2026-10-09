import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformStagedGain

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source
open scoped BigOperators

variable {α γ : Type*} [Fintype α]

def zeroIntBlock : MatrixInt α α := ⟨0,0⟩

/-- A block pulse rounds after each 32-dimensional dot product, exactly as the
    original 64-dimensional multiplication rounds after its zero block. -/
theorem block_pulse_multiply_upper (A D : MatrixInt α α)
    (E : MatrixInt (α ⊕ α) γ) :
    submatrix (multiply (intFourBlocks A zeroIntBlock zeroIntBlock D) E) Sum.inl id =
      multiply A (submatrix E Sum.inl id) := by
  rcases A with ⟨ar,ai⟩
  rcases D with ⟨dr,di⟩
  rcases E with ⟨er,ei⟩
  unfold submatrix multiply intFourBlocks zeroIntBlock
  congr 1 <;> ext i j
  all_goals simp [Matrix.submatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem block_pulse_multiply_lower (A D : MatrixInt α α)
    (E : MatrixInt (α ⊕ α) γ) :
    submatrix (multiply (intFourBlocks A zeroIntBlock zeroIntBlock D) E) Sum.inr id =
      multiply D (submatrix E Sum.inr id) := by
  rcases A with ⟨ar,ai⟩
  rcases D with ⟨dr,di⟩
  rcases E with ⟨er,ei⟩
  unfold submatrix multiply intFourBlocks zeroIntBlock
  congr 1 <;> ext i j
  all_goals simp [Matrix.submatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem multiply_block_pulse_upper (A D : MatrixInt α α)
    (E : MatrixInt γ (α ⊕ α)) :
    submatrix (multiply E (intFourBlocks A zeroIntBlock zeroIntBlock D)) id Sum.inl =
      multiply (submatrix E id Sum.inl) A := by
  rcases A with ⟨ar,ai⟩
  rcases D with ⟨dr,di⟩
  rcases E with ⟨er,ei⟩
  unfold submatrix multiply intFourBlocks zeroIntBlock
  congr 1 <;> ext i j
  all_goals simp [Matrix.submatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks]

theorem multiply_block_pulse_lower (A D : MatrixInt α α)
    (E : MatrixInt γ (α ⊕ α)) :
    submatrix (multiply E (intFourBlocks A zeroIntBlock zeroIntBlock D)) id Sum.inr =
      multiply (submatrix E id Sum.inr) D := by
  rcases A with ⟨ar,ai⟩
  rcases D with ⟨dr,di⟩
  rcases E with ⟨er,ei⟩
  unfold submatrix multiply intFourBlocks zeroIntBlock
  congr 1 <;> ext i j
  all_goals simp [Matrix.submatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks]

omit [Fintype α] in
theorem matrix_int_eq_of_sum_submatrices {δ : Type*}
    {X Y : MatrixInt (α ⊕ α) δ}
    (upper : submatrix X Sum.inl id = submatrix Y Sum.inl id)
    (lower : submatrix X Sum.inr id = submatrix Y Sum.inr id) : X = Y := by
  cases X with | mk xr xi =>
  cases Y with | mk yr yi =>
  congr 1
  · funext i j
    cases i with
    | inl i =>
        have h := congrArg (fun M : MatrixInt α δ => M.re i j) upper
        simpa [submatrix] using h
    | inr i =>
        have h := congrArg (fun M : MatrixInt α δ => M.re i j) lower
        simpa [submatrix] using h
  · funext i j
    cases i with
    | inl i =>
        have h := congrArg (fun M : MatrixInt α δ => M.im i j) upper
        simpa [submatrix] using h
    | inr i =>
        have h := congrArg (fun M : MatrixInt α δ => M.im i j) lower
        simpa [submatrix] using h

omit [Fintype α] in
theorem matrix_int_eq_of_sum_columns {δ : Type*}
    {X Y : MatrixInt δ (α ⊕ α)}
    (upper : submatrix X id Sum.inl = submatrix Y id Sum.inl)
    (lower : submatrix X id Sum.inr = submatrix Y id Sum.inr) : X = Y := by
  cases X with | mk xr xi =>
  cases Y with | mk yr yi =>
  congr 1
  · funext i j
    cases j with
    | inl j =>
        have h := congrArg (fun M : MatrixInt δ α => M.re i j) upper
        simpa [submatrix] using h
    | inr j =>
        have h := congrArg (fun M : MatrixInt δ α => M.re i j) lower
        simpa [submatrix] using h
  · funext i j
    cases j with
    | inl j =>
        have h := congrArg (fun M : MatrixInt δ α => M.im i j) upper
        simpa [submatrix] using h
    | inr j =>
        have h := congrArg (fun M : MatrixInt δ α => M.im i j) lower
        simpa [submatrix] using h

theorem ordinary_pointer_pulse_quantize_blocks
    (A B : MatrixQ OrdinaryFull OrdinaryFull) :
    quantize (ordinaryPointerPulseQ A B) =
      intFourBlocks (quantize A) (quantize (0 : MatrixQ OrdinaryFull OrdinaryFull))
        (quantize (0 : MatrixQ OrdinaryFull OrdinaryFull))
        (quantize (qscale phaseQ B)) := by
  unfold quantize ordinaryPointerPulseQ intFourBlocks
  congr 1 <;> (funext i j; cases i <;> cases j <;> rfl)

theorem quantize_block_diagonal (A D : MatrixQ OrdinaryFull OrdinaryFull) :
    quantize (Matrix.fromBlocks A 0 0 D) =
      intFourBlocks (quantize A) (quantize (0 : MatrixQ OrdinaryFull OrdinaryFull))
        (quantize (0 : MatrixQ OrdinaryFull OrdinaryFull)) (quantize D) := by
  unfold quantize intFourBlocks
  congr 1 <;> (funext i j; cases i <;> cases j <;> rfl)

theorem quantize_zero_int_block :
    quantize (0 : MatrixQ OrdinaryFull OrdinaryFull) =
      (zeroIntBlock : MatrixInt OrdinaryFull OrdinaryFull) := by
  unfold quantize zeroIntBlock
  congr 1 <;> (funext i j; simp [quantizeScalar, roundRatio, scale])

theorem ordinary_supply_pulse_blocks (a b : Basis) (ordered : a < b) :
    quantize (ordinaryPointerSupplyQ a b ordered) =
      intFourBlocks (quantize (ordinaryLoadFullQ a b ordered))
        zeroIntBlock zeroIntBlock
        (quantize (qscale phaseQ (ordinarySupplyQ a b ordered))) := by
  rw [ordinaryPointerSupplyQ, ordinary_pointer_pulse_quantize_blocks,
    quantize_zero_int_block]

theorem ordinary_load_pulse_blocks (a b : Basis) (ordered : a < b) :
    quantize (ordinaryPointerLoadQ a b ordered) =
      intFourBlocks (quantize (ordinaryLoadFullQ a b ordered))
        zeroIntBlock zeroIntBlock
        (quantize (qscale phaseQ (ordinaryLoadFullQ a b ordered))) := by
  rw [ordinaryPointerLoadQ, ordinary_pointer_pulse_quantize_blocks,
    quantize_zero_int_block]

theorem ordinary_weak_pulse_blocks (a b : Basis) (ordered : a < b) :
    quantize (ordinaryPointerWeakQ a b ordered) =
      intFourBlocks (quantize (ordinaryLoadFullQ a b ordered))
        zeroIntBlock zeroIntBlock
        (quantize (qscale phaseQ (ordinaryWeakFullQ a b ordered))) := by
  rw [ordinaryPointerWeakQ, ordinary_pointer_pulse_quantize_blocks,
    quantize_zero_int_block]

theorem ordinary_pc_pointer_blocks (a b : Basis) :
    sourceOrdinaryPCInt a b =
      intFourBlocks (quantize (ordinaryPCFullQ a b)) zeroIntBlock zeroIntBlock
        (quantize (ordinaryPCFullQ a b)) := by
  rw [sourceOrdinaryPCInt, ordinaryPCPointerQ, quantize_block_diagonal,
    quantize_zero_int_block]

theorem ordinary_supply_pulse_multiply_upper (a b : Basis) (ordered : a < b)
    (E : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) γ) :
    submatrix (multiply (quantize (ordinaryPointerSupplyQ a b ordered)) E)
      Sum.inl id =
    multiply (quantize (ordinaryLoadFullQ a b ordered))
      (submatrix E Sum.inl id) := by
  rw [ordinary_supply_pulse_blocks]
  exact block_pulse_multiply_upper _ _ _

theorem ordinary_supply_pulse_multiply_lower (a b : Basis) (ordered : a < b)
    (E : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) γ) :
    submatrix (multiply (quantize (ordinaryPointerSupplyQ a b ordered)) E)
      Sum.inr id =
    multiply (quantize (qscale phaseQ (ordinarySupplyQ a b ordered)))
      (submatrix E Sum.inr id) := by
  rw [ordinary_supply_pulse_blocks]
  exact block_pulse_multiply_lower _ _ _

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.ConcreteDiagonal.PC

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Contraction Evaluate
open scoped Matrix BigOperators
noncomputable section

def diagonalLoadFullQ (a : Basis) : MatrixQ DiagonalFull DiagonalFull :=
  roleBlocksQ
    (bodyLiftQ (diagonalLoadQ a) (oneDiagonalQ 97))
    (donorLiftQ (diagonalLoadQ 97) (oneDiagonalQ a))

def diagonalSupplyFullQ (a : Basis) : MatrixQ DiagonalFull DiagonalFull :=
  roleMixQ SquareRoot.Full.cosine SquareRoot.Full.sine
    (qkron (qkron (oneDiagonalQ a) (oneDiagonalQ 97)) freeEnvironmentQ)

def diagonalWeakFullQ (a : Basis) : MatrixQ DiagonalFull DiagonalFull :=
  roleMixQ SquareRoot.Full.sine SquareRoot.Full.cosine
    (qkron (qkron (oneDiagonalQ a) (oneDiagonalQ 97)) freeEnvironmentQ)

theorem diagonal_load_full_source (a : Basis) (different : a ≠ 97) :
    Spec.load.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val) = diagonalLoadFullQ a :=
  diagonal_load_source a different

theorem diagonal_supply_full_source (a : Basis) (different : a ≠ 97) :
    Spec.supply.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val) = diagonalSupplyFullQ a :=
  diagonal_supply_restriction a different

theorem diagonal_weak_full_source (a : Basis) (different : a ≠ 97) :
    Spec.weak.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val) = diagonalWeakFullQ a :=
  diagonal_weak_restriction a different

def diagonalPointerPulseQ (A B : MatrixQ DiagonalFull DiagonalFull) :
    MatrixQ (DiagonalFull ⊕ DiagonalFull) (DiagonalFull ⊕ DiagonalFull) :=
  Matrix.fromBlocks A 0 0 (qscale phaseQ B)

private theorem pointer_pulse_restrict (a : Basis) (different : a ≠ 97)
    (A B : MatrixQ Current.FullIndex Current.FullIndex)
    (A' B' : MatrixQ DiagonalFull DiagonalFull)
    (ha : A.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val) = A')
    (hb : B.submatrix (fun i => (diagonalFullEquiv a different i).val)
      (fun i => (diagonalFullEquiv a different i).val) = B') :
    (Matrix.fromBlocks A 0 0 (qscale phaseQ B)).submatrix
      (diagonalPointerAddress a different) (diagonalPointerAddress a different) =
      diagonalPointerPulseQ A' B' := by
  funext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals simp only [diagonalPointerAddress,diagonalPointerPulseQ,
    Matrix.submatrix_apply,Matrix.fromBlocks]
  · exact congrFun (congrFun ha i) j
  · rfl
  · rfl
  · exact congrArg (Scalar.multiply phaseQ) (congrFun (congrFun hb i) j)

def diagonalPointerLoadQ (a : Basis) :=
  diagonalPointerPulseQ (diagonalLoadFullQ a) (diagonalLoadFullQ a)
def diagonalPointerSupplyQ (a : Basis) :=
  diagonalPointerPulseQ (diagonalLoadFullQ a) (diagonalSupplyFullQ a)
def diagonalPointerWeakQ (a : Basis) :=
  diagonalPointerPulseQ (diagonalLoadFullQ a) (diagonalWeakFullQ a)

theorem diagonal_pointer_load_source (a : Basis) (different : a ≠ 97) :
    Spec.pointerLoad.submatrix (diagonalPointerAddress a different)
      (diagonalPointerAddress a different) = diagonalPointerLoadQ a :=
  pointer_pulse_restrict a different _ _ _ _
    (diagonal_load_full_source a different) (diagonal_load_full_source a different)

theorem diagonal_pointer_supply_source (a : Basis) (different : a ≠ 97) :
    Spec.pointerSupply.submatrix (diagonalPointerAddress a different)
      (diagonalPointerAddress a different) = diagonalPointerSupplyQ a :=
  pointer_pulse_restrict a different _ _ _ _
    (diagonal_load_full_source a different) (diagonal_supply_full_source a different)

theorem diagonal_pointer_weak_source (a : Basis) (different : a ≠ 97) :
    Spec.pointerWeak.submatrix (diagonalPointerAddress a different)
      (diagonalPointerAddress a different) = diagonalPointerWeakQ a :=
  pointer_pulse_restrict a different _ _ _ _
    (diagonal_load_full_source a different) (diagonal_weak_full_source a different)

theorem source_diagonal_load_concrete (a : Basis) (different : a ≠ 97) :
    sourceDiagonalLoadInt a different = quantize (diagonalPointerLoadQ a) := by
  change quantize (Spec.pointerLoad.submatrix (diagonalPointerAddress a different)
    (diagonalPointerAddress a different)) = _
  rw [diagonal_pointer_load_source a different]

theorem source_diagonal_supply_concrete (a : Basis) (different : a ≠ 97) :
    sourceDiagonalSupplyInt a different = quantize (diagonalPointerSupplyQ a) := by
  change quantize (Spec.pointerSupply.submatrix (diagonalPointerAddress a different)
    (diagonalPointerAddress a different)) = _
  rw [diagonal_pointer_supply_source a different]

theorem source_diagonal_weak_concrete (a : Basis) (different : a ≠ 97) :
    sourceDiagonalWeakInt a different = quantize (diagonalPointerWeakQ a) := by
  change quantize (Spec.pointerWeak.submatrix (diagonalPointerAddress a different)
    (diagonalPointerAddress a different)) = _
  rw [diagonal_pointer_weak_source a different]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

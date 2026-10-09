import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformRotationNorm
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourceOrdinaryFreeInt (a b : Basis) (ordered : a < b) :
    MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  quantize (qkron (onePCQ a b ordered) freeEnvironmentQ)

def sourceOrdinaryRootRotatedInt (a b : Basis) (ordered : a < b) :
    MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  rotateInt (sourceOrdinaryFreeInt a b ordered) (sourceOrdinaryRootInt a b ordered)

def sourceOrdinaryComplementRotatedInt (a b : Basis) (ordered : a < b) :
    MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  rotateInt (sourceOrdinaryFreeInt a b ordered)
    (sourceOrdinaryComplementInt a b ordered)

theorem source_ordinary_rotated_errors (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryRootRotatedInt a b ordered)-
      qvalue (ordinaryRootRotatedQ a b ordered)‖ ≤ (1/10^18 : ℝ) ∧
    ‖value (sourceOrdinaryComplementRotatedInt a b ordered)-
      qvalue (ordinaryComplementRotatedQ a b ordered)‖ ≤ (1/10^18 : ℝ) := by
  let UQ := qkron (onePCQ a b ordered) freeEnvironmentQ
  have freeError := ordinary_free_quantize_error a b ordered
  have freeBound := ordinary_free_norm_six a b ordered
  have rootBounds := ordinary_root_norms_four a b ordered
  constructor
  · change ‖value (rotateInt (sourceOrdinaryFreeInt a b ordered)
        (sourceOrdinaryRootInt a b ordered))-qvalue (rotateQ UQ
        (rootOrdinaryQ a b ordered))‖ ≤ _
    rw [rotateQ,qvalue_multiply,qvalue_multiply,qvalue_adjoint]
    exact rotate_int_bound (sourceOrdinaryFreeInt a b ordered)
      (sourceOrdinaryRootInt a b ordered) (qvalue UQ)
      (qvalue (rootOrdinaryQ a b ordered)) (by decide)
      freeError (source_ordinary_root_int_error a b ordered)
      (freeBound.trans (by norm_num)) (rootBounds.1.trans (by norm_num))
  · change ‖value (rotateInt (sourceOrdinaryFreeInt a b ordered)
        (sourceOrdinaryComplementInt a b ordered))-qvalue (rotateQ UQ
        (complementOrdinaryQ a b ordered))‖ ≤ _
    rw [rotateQ,qvalue_multiply,qvalue_multiply,qvalue_adjoint]
    exact rotate_int_bound (sourceOrdinaryFreeInt a b ordered)
      (sourceOrdinaryComplementInt a b ordered) (qvalue UQ)
      (qvalue (complementOrdinaryQ a b ordered)) (by decide)
      freeError (source_ordinary_complement_int_error a b ordered)
      (freeBound.trans (by norm_num)) (rootBounds.2.trans (by norm_num))

theorem source_first_free_same :
    sourceOrdinaryFreeInt (0 : Basis) (1 : Basis) (by decide)=sourceFirstFreeInt := rfl

theorem source_first_rotated_same :
    sourceOrdinaryRootRotatedInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstRootRotatedInt ∧
    sourceOrdinaryComplementRotatedInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstComplementRotatedInt := ⟨rfl,rfl⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

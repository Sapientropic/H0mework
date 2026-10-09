import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformColumnsConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEntrance.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourceOrdinaryReceivedInt (a b : Basis) (ordered : a < b) :
    MatrixInt LoadPrimitive.NativeIndex LoadPrimitive.NativeIndex :=
  quantize (ordinaryReceivedQ a b ordered)

def sourceOrdinaryEntranceInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) LoadPrimitive.NativeIndex :=
  multiply (sourceOrdinaryColumnsInt a b ordered)
    (sourceOrdinaryReceivedInt a b ordered)

theorem source_ordinary_received_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinaryReceivedQ a b ordered)‖ ≤ (1001/1000 : ℝ) := by
  rw [ordinaryReceivedQ_value]
  have injective : Function.Injective (Scaled.Order.orbitPCE a b) := by
    intro i j h
    exact (Scaled.Order.offDiagonalPCEEquiv a b ordered.ne).injective
      (Subtype.val_injective h)
  exact (submatrix_norm_le LoadExecution.receivedWord _ _ injective injective).trans
    source_received_word_norm_sharp

theorem source_ordinary_columns_norm (a b : Basis) (ordered : a < b) :
    ‖qvalue (ordinarySourceColumnsQ a b ordered)‖ ≤ (5 : ℝ) := by
  rw [ordinarySourceColumnsQ,qvalue_multiply]
  have h := Matrix.l2_opNorm_mul
    (qvalue ((ordinaryPointerQ a b ordered).submatrix id Sum.inl))
    (qvalue ((ordinarySupplyQ a b ordered).submatrix id ordinaryInjection))
  have product := mul_le_mul (source_ordinary_pointer_columns_norm a b ordered)
    (source_ordinary_supply_charged_norm a b ordered) (norm_nonneg _)
    (by norm_num : (0 : ℝ) ≤ 2001/1000)
  exact h.trans (by nlinarith only [product])

theorem source_first_entrance_same :
    sourceOrdinaryEntranceInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstEntranceInt := rfl

theorem source_first_received_same :
    sourceOrdinaryReceivedInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstReceivedInt := rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

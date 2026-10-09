import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.SecondElevenConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.PCCore
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformGainSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Contraction

def sourceSecondPCCoreInt : MatrixInt OrdinaryFull OrdinaryFull :=
  quantize (ordinaryPCFullQ (0 : Basis) (2 : Basis))

private theorem second_pc_matrix_int_ext {α β : Type*} {A B : MatrixInt α β}
    (hRe : A.re = B.re) (hIm : A.im = B.im) : A = B := by
  cases A
  cases B
  cases hRe
  cases hIm
  rfl

theorem source_second_pc_blocks : sourceOrdinaryPCInt (0 : Basis) (2 : Basis) =
    intFourBlocks sourceSecondPCCoreInt sourceFirstZeroCoreInt
      sourceFirstZeroCoreInt sourceSecondPCCoreInt := by
  apply second_pc_matrix_int_ext <;> funext i j
  all_goals rcases i with (i | i) <;> rcases j with (j | j)
  all_goals simp [sourceOrdinaryPCInt,sourceSecondPCCoreInt,sourceFirstZeroCoreInt,
    ordinaryPCPointerQ,intFourBlocks,Matrix.fromBlocks,quantize,
    quantizeScalar,roundRatio,scale]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

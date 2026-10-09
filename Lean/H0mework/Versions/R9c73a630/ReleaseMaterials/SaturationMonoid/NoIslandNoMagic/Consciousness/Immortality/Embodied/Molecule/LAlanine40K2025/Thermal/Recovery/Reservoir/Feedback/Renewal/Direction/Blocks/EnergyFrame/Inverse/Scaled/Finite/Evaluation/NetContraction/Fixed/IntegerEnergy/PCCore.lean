import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.Base
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.PulseCoreConsumer
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate

def sourceFirstPCCoreInt : MatrixInt OrdinaryFull OrdinaryFull :=
  quantize (ordinaryPCFullQ (0 : Basis) (1 : Basis))

private theorem matrix_int_ext {α β : Type*} {A B : MatrixInt α β}
    (hRe : A.re=B.re) (hIm : A.im=B.im) : A=B := by
  cases A
  cases B
  cases hRe
  cases hIm
  rfl

theorem source_first_pc_blocks : sourceFirstPCInt =
    intFourBlocks sourceFirstPCCoreInt sourceFirstZeroCoreInt
      sourceFirstZeroCoreInt sourceFirstPCCoreInt := by
  apply matrix_int_ext <;> funext i j
  all_goals rcases i with (i | i) <;> rcases j with (j | j)
  all_goals simp [sourceFirstPCInt,sourceFirstPCCoreInt,sourceFirstZeroCoreInt,
    ordinaryPCPointerQ,intFourBlocks,Matrix.fromBlocks,quantize,
    quantizeScalar,roundRatio,scale]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

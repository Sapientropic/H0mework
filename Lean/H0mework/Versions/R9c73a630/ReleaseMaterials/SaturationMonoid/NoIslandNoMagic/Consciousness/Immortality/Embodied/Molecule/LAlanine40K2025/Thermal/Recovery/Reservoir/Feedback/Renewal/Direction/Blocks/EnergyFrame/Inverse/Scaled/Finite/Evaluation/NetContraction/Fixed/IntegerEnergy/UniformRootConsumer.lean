import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformRootSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPointer.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem source_ordinary_roots_actual (a b : Basis) (ordered : a < b) :
    ‖value (sourceOrdinaryRootInt a b ordered)-
      SquareRoot.Full.sourceRoot.submatrix (Scaled.Order.orbitPCE a b)
        (Scaled.Order.orbitPCE a b)‖ ≤ (1/10^25 : ℝ) ∧
    ‖value (sourceOrdinaryComplementInt a b ordered)-
      SquareRoot.Full.sourceComplement.submatrix (Scaled.Order.orbitPCE a b)
        (Scaled.Order.orbitPCE a b)‖ ≤ (1/10^25 : ℝ) := by
  constructor
  · simpa only [rootOrdinaryQ_value] using source_ordinary_root_int_error a b ordered
  · simpa only [complementOrdinaryQ_value] using
      source_ordinary_complement_int_error a b ordered

theorem source_first_root_same :
    sourceOrdinaryRootInt (0 : Basis) (1 : Basis) (by decide)=sourceFirstRootInt := rfl

theorem source_first_complement_same :
    sourceOrdinaryComplementInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstComplementInt := rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

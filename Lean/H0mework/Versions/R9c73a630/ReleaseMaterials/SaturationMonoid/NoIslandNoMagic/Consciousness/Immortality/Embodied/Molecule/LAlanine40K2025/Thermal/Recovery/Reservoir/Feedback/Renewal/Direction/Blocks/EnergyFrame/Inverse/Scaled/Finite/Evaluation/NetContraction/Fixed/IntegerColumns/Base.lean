import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPointer.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.SharpNorm
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix BigOperators Matrix.Norms.L2Operator

def sourceFirstSupplyInt : MatrixInt OrdinaryFull OrdinaryFull :=
  quantize (ordinarySupplyQ (0 : Basis) (1 : Basis) (by decide))

def sourceFirstPointerColumnsInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) OrdinaryFull :=
  submatrix sourceFirstPointerInt id Sum.inl

def sourceFirstSupplyChargedInt : MatrixInt OrdinaryFull ((Fin 2 × Fin 2) × Fin 2) :=
  submatrix sourceFirstSupplyInt id ordinaryInjection

def sourceFirstColumnsInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    ((Fin 2 × Fin 2) × Fin 2) :=
  multiply sourceFirstPointerColumnsInt sourceFirstSupplyChargedInt


end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

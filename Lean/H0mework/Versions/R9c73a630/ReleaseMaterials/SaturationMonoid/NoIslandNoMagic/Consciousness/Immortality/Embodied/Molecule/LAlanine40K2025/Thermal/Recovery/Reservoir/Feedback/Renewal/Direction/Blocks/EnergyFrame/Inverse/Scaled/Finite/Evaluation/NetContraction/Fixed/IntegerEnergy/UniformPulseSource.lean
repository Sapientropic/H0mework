import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.UniformEntranceConsumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerPulses.Base
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourceOrdinaryLoadPulseInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull) :=
  quantize (ordinaryPointerLoadQ a b ordered)

def sourceOrdinarySupplyPulseInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull) :=
  quantize (ordinaryPointerSupplyQ a b ordered)

def sourceOrdinaryWeakPulseInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (OrdinaryFull ⊕ OrdinaryFull) :=
  quantize (ordinaryPointerWeakQ a b ordered)

def sourceOrdinaryAfterSupply1Int (a b : Basis) (ordered : a < b) :=
  multiply (sourceOrdinarySupplyPulseInt a b ordered)
    (sourceOrdinaryEntranceInt a b ordered)

def sourceOrdinaryAfterSupply2Int (a b : Basis) (ordered : a < b) :=
  multiply (sourceOrdinarySupplyPulseInt a b ordered)
    (sourceOrdinaryAfterSupply1Int a b ordered)

def sourceOrdinaryNineInt (a b : Basis) (ordered : a < b) :=
  multiply (sourceOrdinaryLoadPulseInt a b ordered)
    (sourceOrdinaryAfterSupply2Int a b ordered)

def sourceOrdinaryAfterWeakInt (a b : Basis) (ordered : a < b) :=
  multiply (sourceOrdinaryWeakPulseInt a b ordered)
    (sourceOrdinaryNineInt a b ordered)

def sourceOrdinaryElevenInt (a b : Basis) (ordered : a < b) :=
  multiply (sourceOrdinaryLoadPulseInt a b ordered)
    (sourceOrdinaryAfterWeakInt a b ordered)

def sourceOrdinaryAfterSupply1Q (a b : Basis) (ordered : a < b) :=
  qmultiply (ordinaryPointerSupplyQ a b ordered) (ordinaryEntranceQ a b ordered)

def sourceOrdinaryAfterSupply2Q (a b : Basis) (ordered : a < b) :=
  qmultiply (ordinaryPointerSupplyQ a b ordered)
    (sourceOrdinaryAfterSupply1Q a b ordered)

def sourceOrdinaryAfterWeakQ (a b : Basis) (ordered : a < b) :=
  qmultiply (ordinaryPointerWeakQ a b ordered)
    (ordinaryNineColumnsQ a b ordered)

theorem source_first_pulses_same :
    sourceOrdinarySupplyPulseInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstSupplyPulseInt ∧
    sourceOrdinaryLoadPulseInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstLoadPulseInt ∧
    sourceOrdinaryWeakPulseInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstWeakPulseInt := ⟨rfl,rfl,rfl⟩

theorem source_first_arm_columns_same :
    sourceOrdinaryNineInt (0 : Basis) (1 : Basis) (by decide)=sourceFirstNineInt ∧
    sourceOrdinaryElevenInt (0 : Basis) (1 : Basis) (by decide)=
      sourceFirstElevenInt := ⟨rfl,rfl⟩

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

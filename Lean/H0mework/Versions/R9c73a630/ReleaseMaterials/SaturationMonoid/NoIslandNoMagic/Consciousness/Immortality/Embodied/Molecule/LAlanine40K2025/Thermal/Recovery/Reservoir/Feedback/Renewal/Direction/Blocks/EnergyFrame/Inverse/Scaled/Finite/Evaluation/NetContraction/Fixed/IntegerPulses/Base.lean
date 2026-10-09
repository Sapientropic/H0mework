import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEntrance.Source
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Load.Producer.StrictThermal Contraction Evaluate
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
local instance : Fintype (Sym2 Basis) := Fintype.ofFinite _

def sourceFirstLoadPulseInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  quantize (ordinaryPointerLoadQ (0 : Basis) (1 : Basis) (by decide))

def sourceFirstSupplyPulseInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  quantize (ordinaryPointerSupplyQ (0 : Basis) (1 : Basis) (by decide))

def sourceFirstWeakPulseInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  quantize (ordinaryPointerWeakQ (0 : Basis) (1 : Basis) (by decide))

def sourceFirstAfterSupply1Int : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex := multiply sourceFirstSupplyPulseInt sourceFirstEntranceInt

def sourceFirstAfterSupply2Int : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex := multiply sourceFirstSupplyPulseInt sourceFirstAfterSupply1Int

def sourceFirstNineInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex := multiply sourceFirstLoadPulseInt sourceFirstAfterSupply2Int

def sourceFirstAfterWeakInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex := multiply sourceFirstWeakPulseInt sourceFirstNineInt

def sourceFirstElevenInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex := multiply sourceFirstLoadPulseInt sourceFirstAfterWeakInt

def sourceFirstAfterSupply1Q : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex :=
  qmultiply (ordinaryPointerSupplyQ (0 : Basis) (1 : Basis) (by decide))
    (ordinaryEntranceQ (0 : Basis) (1 : Basis) (by decide))

def sourceFirstAfterSupply2Q : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex :=
  qmultiply (ordinaryPointerSupplyQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstAfterSupply1Q

def sourceFirstNineQ : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex :=
  qmultiply (ordinaryPointerLoadQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstAfterSupply2Q

def sourceFirstAfterWeakQ : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex :=
  qmultiply (ordinaryPointerWeakQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstNineQ

def sourceFirstElevenQ : MatrixQ (OrdinaryFull ⊕ OrdinaryFull)
    LoadPrimitive.NativeIndex :=
  qmultiply (ordinaryPointerLoadQ (0 : Basis) (1 : Basis) (by decide))
    sourceFirstAfterWeakQ

theorem source_first_nine_q_original : sourceFirstNineQ=
    ordinaryNineColumnsQ (0 : Basis) (1 : Basis) (by decide) := rfl

theorem source_first_eleven_q_original : sourceFirstElevenQ=
    ordinaryElevenColumnsQ (0 : Basis) (1 : Basis) (by decide) := rfl


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

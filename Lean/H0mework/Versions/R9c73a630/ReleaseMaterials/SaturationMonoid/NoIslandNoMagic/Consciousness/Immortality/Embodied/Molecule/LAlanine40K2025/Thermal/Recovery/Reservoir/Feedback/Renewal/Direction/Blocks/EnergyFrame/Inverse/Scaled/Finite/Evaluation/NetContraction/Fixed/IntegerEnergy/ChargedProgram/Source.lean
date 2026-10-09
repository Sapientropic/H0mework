import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.Core

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def chargedEntranceInt (a b : Basis) (ordered : a < b) :
    MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2) :=
  multiply (sourceOrdinaryColumnsInt a b ordered)
    (submatrix (sourceOrdinaryReceivedInt a b ordered) id chargedInjection)

theorem charged_entrance_original (a b : Basis) (ordered : a < b) :
    chargedEntranceInt a b ordered =
      submatrix (sourceOrdinaryEntranceInt a b ordered) id chargedInjection := by
  rw [sourceOrdinaryEntranceInt,select_integer_columns]
  rfl

def chargedSupplyStep (a b : Basis) (ordered : a < b)
    (E : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :=
  chargedStep (quantize (ordinaryLoadFullQ a b ordered))
    (quantize (qscale phaseQ (ordinarySupplyQ a b ordered))) E

def chargedLoadStep (a b : Basis) (ordered : a < b)
    (E : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :=
  chargedStep (quantize (ordinaryLoadFullQ a b ordered))
    (quantize (qscale phaseQ (ordinaryLoadFullQ a b ordered))) E

def chargedWeakStep (a b : Basis) (ordered : a < b)
    (E : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :=
  chargedStep (quantize (ordinaryLoadFullQ a b ordered))
    (quantize (qscale phaseQ (ordinaryWeakFullQ a b ordered))) E

theorem charged_supply_step_original (a b : Basis) (ordered : a < b)
    (E : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :
    chargedSupplyStep a b ordered E =
      multiply (sourceOrdinarySupplyPulseInt a b ordered) E := by
  rw [chargedSupplyStep,charged_step_exact,
    sourceOrdinarySupplyPulseInt,ordinary_supply_pulse_blocks]

theorem charged_load_step_original (a b : Basis) (ordered : a < b)
    (E : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :
    chargedLoadStep a b ordered E =
      multiply (sourceOrdinaryLoadPulseInt a b ordered) E := by
  rw [chargedLoadStep,charged_step_exact,
    sourceOrdinaryLoadPulseInt,ordinary_load_pulse_blocks]

theorem charged_weak_step_original (a b : Basis) (ordered : a < b)
    (E : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2)) :
    chargedWeakStep a b ordered E =
      multiply (sourceOrdinaryWeakPulseInt a b ordered) E := by
  rw [chargedWeakStep,charged_step_exact,
    sourceOrdinaryWeakPulseInt,ordinary_weak_pulse_blocks]

def chargedAfterSupply1Int (a b : Basis) (ordered : a < b) :=
  chargedSupplyStep a b ordered (chargedEntranceInt a b ordered)
def chargedAfterSupply2Int (a b : Basis) (ordered : a < b) :=
  chargedSupplyStep a b ordered (chargedAfterSupply1Int a b ordered)
def chargedNineInt (a b : Basis) (ordered : a < b) :=
  chargedLoadStep a b ordered (chargedAfterSupply2Int a b ordered)
def chargedAfterWeakInt (a b : Basis) (ordered : a < b) :=
  chargedWeakStep a b ordered (chargedNineInt a b ordered)
def chargedElevenInt (a b : Basis) (ordered : a < b) :=
  chargedLoadStep a b ordered (chargedAfterWeakInt a b ordered)

theorem charged_supply1_original (a b : Basis) (ordered : a < b) :
    chargedAfterSupply1Int a b ordered =
      submatrix (sourceOrdinaryAfterSupply1Int a b ordered) id chargedInjection := by
  rw [chargedAfterSupply1Int,charged_supply_step_original,charged_entrance_original,
    sourceOrdinaryAfterSupply1Int,select_integer_columns]

theorem charged_supply2_original (a b : Basis) (ordered : a < b) :
    chargedAfterSupply2Int a b ordered =
      submatrix (sourceOrdinaryAfterSupply2Int a b ordered) id chargedInjection := by
  rw [chargedAfterSupply2Int,charged_supply_step_original,charged_supply1_original,
    sourceOrdinaryAfterSupply2Int,select_integer_columns]

theorem charged_nine_original (a b : Basis) (ordered : a < b) :
    chargedNineInt a b ordered =
      sourceOrdinaryNineSelectedInt a b ordered := by
  rw [chargedNineInt,charged_load_step_original,charged_supply2_original,
    sourceOrdinaryNineSelectedInt,sourceOrdinaryNineInt,select_integer_columns]

theorem charged_weak_original (a b : Basis) (ordered : a < b) :
    chargedAfterWeakInt a b ordered =
      submatrix (sourceOrdinaryAfterWeakInt a b ordered) id chargedInjection := by
  rw [chargedAfterWeakInt,charged_weak_step_original,charged_nine_original,
    sourceOrdinaryAfterWeakInt,select_integer_columns]
  rfl

theorem charged_eleven_original (a b : Basis) (ordered : a < b) :
    chargedElevenInt a b ordered =
      sourceOrdinaryElevenSelectedInt a b ordered := by
  rw [chargedElevenInt,charged_load_step_original,charged_weak_original,
    sourceOrdinaryElevenSelectedInt,sourceOrdinaryElevenInt,select_integer_columns]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

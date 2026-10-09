import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.BlockPulseMultiply

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

/-- The original supply, load, and weak stages each act on two independent
    32-dimensional arms; every equality retains the original integer rounding. -/
theorem source_ordinary_after_supply1_arms (a b : Basis) (ordered : a < b) :
    submatrix (sourceOrdinaryAfterSupply1Int a b ordered) Sum.inl id =
      multiply (quantize (ordinaryLoadFullQ a b ordered))
        (submatrix (sourceOrdinaryEntranceInt a b ordered) Sum.inl id) ∧
    submatrix (sourceOrdinaryAfterSupply1Int a b ordered) Sum.inr id =
      multiply (quantize (qscale phaseQ (ordinarySupplyQ a b ordered)))
        (submatrix (sourceOrdinaryEntranceInt a b ordered) Sum.inr id) := by
  constructor
  · exact ordinary_supply_pulse_multiply_upper a b ordered _
  · exact ordinary_supply_pulse_multiply_lower a b ordered _

theorem source_ordinary_after_supply2_arms (a b : Basis) (ordered : a < b) :
    submatrix (sourceOrdinaryAfterSupply2Int a b ordered) Sum.inl id =
      multiply (quantize (ordinaryLoadFullQ a b ordered))
        (submatrix (sourceOrdinaryAfterSupply1Int a b ordered) Sum.inl id) ∧
    submatrix (sourceOrdinaryAfterSupply2Int a b ordered) Sum.inr id =
      multiply (quantize (qscale phaseQ (ordinarySupplyQ a b ordered)))
        (submatrix (sourceOrdinaryAfterSupply1Int a b ordered) Sum.inr id) := by
  constructor
  · exact ordinary_supply_pulse_multiply_upper a b ordered _
  · exact ordinary_supply_pulse_multiply_lower a b ordered _

theorem source_ordinary_nine_arms (a b : Basis) (ordered : a < b) :
    submatrix (sourceOrdinaryNineInt a b ordered) Sum.inl id =
      multiply (quantize (ordinaryLoadFullQ a b ordered))
        (submatrix (sourceOrdinaryAfterSupply2Int a b ordered) Sum.inl id) ∧
    submatrix (sourceOrdinaryNineInt a b ordered) Sum.inr id =
      multiply (quantize (qscale phaseQ (ordinaryLoadFullQ a b ordered)))
        (submatrix (sourceOrdinaryAfterSupply2Int a b ordered) Sum.inr id) := by
  constructor <;> rw [sourceOrdinaryNineInt, sourceOrdinaryLoadPulseInt,
    ordinary_load_pulse_blocks]
  · exact block_pulse_multiply_upper _ _ _
  · exact block_pulse_multiply_lower _ _ _

theorem source_ordinary_after_weak_arms (a b : Basis) (ordered : a < b) :
    submatrix (sourceOrdinaryAfterWeakInt a b ordered) Sum.inl id =
      multiply (quantize (ordinaryLoadFullQ a b ordered))
        (submatrix (sourceOrdinaryNineInt a b ordered) Sum.inl id) ∧
    submatrix (sourceOrdinaryAfterWeakInt a b ordered) Sum.inr id =
      multiply (quantize (qscale phaseQ (ordinaryWeakFullQ a b ordered)))
        (submatrix (sourceOrdinaryNineInt a b ordered) Sum.inr id) := by
  constructor <;> rw [sourceOrdinaryAfterWeakInt, sourceOrdinaryWeakPulseInt,
    ordinary_weak_pulse_blocks]
  · exact block_pulse_multiply_upper _ _ _
  · exact block_pulse_multiply_lower _ _ _

theorem source_ordinary_eleven_arms (a b : Basis) (ordered : a < b) :
    submatrix (sourceOrdinaryElevenInt a b ordered) Sum.inl id =
      multiply (quantize (ordinaryLoadFullQ a b ordered))
        (submatrix (sourceOrdinaryAfterWeakInt a b ordered) Sum.inl id) ∧
    submatrix (sourceOrdinaryElevenInt a b ordered) Sum.inr id =
      multiply (quantize (qscale phaseQ (ordinaryLoadFullQ a b ordered)))
        (submatrix (sourceOrdinaryAfterWeakInt a b ordered) Sum.inr id) := by
  constructor <;> rw [sourceOrdinaryElevenInt, sourceOrdinaryLoadPulseInt,
    ordinary_load_pulse_blocks]
  · exact block_pulse_multiply_upper _ _ _
  · exact block_pulse_multiply_lower _ _ _

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

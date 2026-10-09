import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.Entrance
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.LoadInput
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.SupplyPhaseInput
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.Energy

set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

def midSupply1Stage : MatrixInt (OrdinaryFull ⊕ OrdinaryFull) (Fin 2 × Fin 2) :=
  chargedStep
    (fromTable midLoadFullTable ordinaryFullFin ordinaryFullFin)
    (fromTable midPhaseSupplyTable ordinaryFullFin ordinaryFullFin)
    (fromTable midChargedEntranceTable pointerFin pairFin)

private theorem mid_entrance_matrix :
    chargedEntranceInt (0 : Basis) (6 : Basis) (by decide) =
      fromTable midChargedEntranceTable pointerFin pairFin := by
  calc
    _ = fromTable (toTable (chargedEntranceInt (0 : Basis) (6 : Basis) (by decide))
      pointerFin pairFin) pointerFin pairFin := (from_to_table _ _ _).symm
    _ = _ := by rw [mid_charged_entrance_original_literal]

private theorem mid_load_matrix :
    quantize (ordinaryLoadFullQ (0 : Basis) (6 : Basis) (by decide)) =
      fromTable midLoadFullTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (ordinaryLoadFullQ (0 : Basis) (6 : Basis) (by decide)))
      ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
        (from_to_table _ _ _).symm
    _ = _ := by rw [mid_load_full_source]

private theorem mid_phase_supply_matrix :
    quantize (qscale phaseQ (ordinarySupplyQ (0 : Basis) (6 : Basis) (by decide))) =
      fromTable midPhaseSupplyTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (qscale phaseQ
      (ordinarySupplyQ (0 : Basis) (6 : Basis) (by decide))))
      ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
        (from_to_table _ _ _).symm
    _ = _ := by rw [mid_phase_supply_source]

theorem mid_supply1_source :
    chargedAfterSupply1Int (0 : Basis) (6 : Basis) (by decide) = midSupply1Stage := by
  unfold chargedAfterSupply1Int chargedSupplyStep
  rw [mid_entrance_matrix, mid_load_matrix, mid_phase_supply_matrix]
  rfl

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

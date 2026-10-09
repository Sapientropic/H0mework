import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.LoadInput
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.SupplyPhaseInput
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.WeakPhaseInput
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.LoadPhaseInput
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidStage.PCInput

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Contraction Load.Source

theorem mid_load_input_matrix :
    quantize (ordinaryLoadFullQ (0 : Basis) (6 : Basis) (by decide)) =
      fromTable midLoadFullTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (ordinaryLoadFullQ (0 : Basis) (6 : Basis) (by decide)))
      ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
        (from_to_table _ _ _).symm
    _ = _ := by rw [mid_load_full_source]

theorem mid_phase_supply_input_matrix :
    quantize (qscale phaseQ (ordinarySupplyQ (0 : Basis) (6 : Basis) (by decide))) =
      fromTable midPhaseSupplyTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (qscale phaseQ (ordinarySupplyQ (0 : Basis) (6 : Basis) (by decide))))
      ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
        (from_to_table _ _ _).symm
    _ = _ := by rw [mid_phase_supply_source]

theorem mid_phase_weak_input_matrix :
    quantize (qscale phaseQ (ordinaryWeakFullQ (0 : Basis) (6 : Basis) (by decide))) =
      fromTable midPhaseWeakTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (qscale phaseQ (ordinaryWeakFullQ (0 : Basis) (6 : Basis) (by decide))))
      ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
        (from_to_table _ _ _).symm
    _ = _ := by rw [mid_phase_weak_source]

theorem mid_phase_load_input_matrix :
    quantize (qscale phaseQ (ordinaryLoadFullQ (0 : Basis) (6 : Basis) (by decide))) =
      fromTable midPhaseLoadTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (qscale phaseQ (ordinaryLoadFullQ (0 : Basis) (6 : Basis) (by decide))))
      ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
        (from_to_table _ _ _).symm
    _ = _ := by rw [mid_phase_load_source]

theorem mid_pc_input_matrix :
    quantize (ordinaryPCFullQ (0 : Basis) (6 : Basis)) =
      fromTable midPCFullTable ordinaryFullFin ordinaryFullFin := by
  calc
    _ = fromTable (toTable (quantize (ordinaryPCFullQ (0 : Basis) (6 : Basis)))
      ordinaryFullFin ordinaryFullFin) ordinaryFullFin ordinaryFullFin :=
        (from_to_table _ _ _).symm
    _ = _ := by rw [mid_pc_full_source]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.PhaseWeakLiteral
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Contraction Load.Source

theorem literal_load_core_table :
    toTable sourceFirstLoadCoreInt ordinaryFullFin ordinaryFullFin=literalLoadCoreTable :=
  int_table_ext literal_load_core_re literal_load_core_im

theorem literal_phaseload_core_table :
    toTable sourceFirstPhaseLoadCoreInt ordinaryFullFin ordinaryFullFin=
      literalPhaseLoadCoreTable :=
  int_table_ext literal_phaseload_core_re literal_phaseload_core_im

theorem literal_phasesupply_core_table :
    toTable sourceFirstPhaseSupplyCoreInt ordinaryFullFin ordinaryFullFin=
      literalPhaseSupplyCoreTable :=
  int_table_ext literal_phasesupply_core_re literal_phasesupply_core_im

theorem literal_phaseweak_core_table :
    toTable sourceFirstPhaseWeakCoreInt ordinaryFullFin ordinaryFullFin=
      literalPhaseWeakCoreTable :=
  int_table_ext literal_phaseweak_core_re literal_phaseweak_core_im

theorem literal_load_core_original :
    fromTable literalLoadCoreTable ordinaryFullFin ordinaryFullFin=sourceFirstLoadCoreInt := by
  rw [← literal_load_core_table]
  exact from_to_table _ _ _

theorem literal_phaseload_core_original :
    fromTable literalPhaseLoadCoreTable ordinaryFullFin ordinaryFullFin=
      sourceFirstPhaseLoadCoreInt := by
  rw [← literal_phaseload_core_table]
  exact from_to_table _ _ _

theorem literal_phasesupply_core_original :
    fromTable literalPhaseSupplyCoreTable ordinaryFullFin ordinaryFullFin=
      sourceFirstPhaseSupplyCoreInt := by
  rw [← literal_phasesupply_core_table]
  exact from_to_table _ _ _

theorem literal_phaseweak_core_original :
    fromTable literalPhaseWeakCoreTable ordinaryFullFin ordinaryFullFin=
      sourceFirstPhaseWeakCoreInt := by
  rw [← literal_phaseweak_core_table]
  exact from_to_table _ _ _

def literalLoadPulseInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  intFourBlocks
    (fromTable literalLoadCoreTable ordinaryFullFin ordinaryFullFin)
    sourceFirstZeroCoreInt sourceFirstZeroCoreInt
    (fromTable literalPhaseLoadCoreTable ordinaryFullFin ordinaryFullFin)

def literalSupplyPulseInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  intFourBlocks
    (fromTable literalLoadCoreTable ordinaryFullFin ordinaryFullFin)
    sourceFirstZeroCoreInt sourceFirstZeroCoreInt
    (fromTable literalPhaseSupplyCoreTable ordinaryFullFin ordinaryFullFin)

def literalWeakPulseInt : MatrixInt (OrdinaryFull ⊕ OrdinaryFull)
    (OrdinaryFull ⊕ OrdinaryFull) :=
  intFourBlocks
    (fromTable literalLoadCoreTable ordinaryFullFin ordinaryFullFin)
    sourceFirstZeroCoreInt sourceFirstZeroCoreInt
    (fromTable literalPhaseWeakCoreTable ordinaryFullFin ordinaryFullFin)

theorem literal_load_pulse_original : literalLoadPulseInt=sourceFirstLoadPulseInt := by
  rw [source_first_load_pulse_blocks,literalLoadPulseInt,
    literal_load_core_original,literal_phaseload_core_original]

theorem literal_supply_pulse_original : literalSupplyPulseInt=sourceFirstSupplyPulseInt := by
  rw [source_first_supply_pulse_blocks,literalSupplyPulseInt,
    literal_load_core_original,literal_phasesupply_core_original]

theorem literal_weak_pulse_original : literalWeakPulseInt=sourceFirstWeakPulseInt := by
  rw [source_first_weak_pulse_blocks,literalWeakPulseInt,
    literal_load_core_original,literal_phaseweak_core_original]

def literalLoadPulseTable : IntTable 64 64 :=
  toTable literalLoadPulseInt pointerFin pointerFin

def literalSupplyPulseTable : IntTable 64 64 :=
  toTable literalSupplyPulseInt pointerFin pointerFin

def literalWeakPulseTable : IntTable 64 64 :=
  toTable literalWeakPulseInt pointerFin pointerFin

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

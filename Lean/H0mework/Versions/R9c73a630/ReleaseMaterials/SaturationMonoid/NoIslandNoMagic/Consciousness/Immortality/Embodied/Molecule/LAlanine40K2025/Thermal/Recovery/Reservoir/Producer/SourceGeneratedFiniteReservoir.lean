import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedReservoirThermodynamics

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Producer

open Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Current

theorem initial_clock : initial.localClock = 4 * nativeClockStep := Recovery.Runtime.recoveryRuntime_firstClock

theorem first_clock : (supplyNext initial).localClock = 5 * nativeClockStep := by
  change initial.localClock + nativeClockStep = _
  rw [initial_clock]
  ring

theorem next_load_clock : (loadNext (supplyNext initial)).localClock = 6 * nativeClockStep := by
  change (supplyNext initial).localClock + nativeClockStep = _
  rw [first_clock]
  ring

theorem sourceGeneratedFiniteReservoir :
    type_of% initial_receives_actual ∧ type_of% initial_body ∧
    type_of% Native.sourceCoupling_positive ∧
    type_of% (Physical.pulse_is_full_flow (nativeClockStep : ℝ)) ∧
    type_of% (Physical.loadPulse_baseline (nativeClockStep : ℝ)) ∧
    type_of% Readout.first_pc_energy_gain ∧ type_of% Readout.first_pc_capacity_gain ∧
    type_of% Readout.first_donor_paid_gain ∧ type_of% Readout.first_donor_not_reset ∧
    type_of% (Readout.supply_paid_from_actual_remaining initial) ∧
    type_of% (EnergyLedger.sourceWork_abs_le_two initial) ∧
    type_of% Thermo.first_retains_paid_entropy ∧ type_of% (Thermo.supply_net_account initial) ∧
    type_of% (loadNext_body (supplyNext initial)) ∧ type_of% (EnergyLedger.load_donor_matrix (supplyNext initial)) ∧
    type_of% first_clock ∧ type_of% next_load_clock ∧
    ∀ left right, (supplyNext left).joint = (supplyNext right).joint → left.joint = right.joint :=
  ⟨initial_receives_actual, initial_body, Native.sourceCoupling_positive,
    Physical.pulse_is_full_flow _, Physical.loadPulse_baseline _, Readout.first_pc_energy_gain, Readout.first_pc_capacity_gain,
    Readout.first_donor_paid_gain, Readout.first_donor_not_reset, Readout.supply_paid_from_actual_remaining initial,
    EnergyLedger.sourceWork_abs_le_two initial, Thermo.first_retains_paid_entropy, Thermo.supply_net_account initial,
    loadNext_body _, EnergyLedger.load_donor_matrix _, first_clock, next_load_clock, supplyNext_reflects_joint⟩

end LAlanine40K2025.Thermal.Recovery.Reservoir.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Producer.SourceGeneratedPointerThermodynamics

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer

open Live
noncomputable section

theorem sourceGeneratedPointerInstrument :
    type_of% sourceHamiltonian_hermitian ∧ type_of% sourceHamiltonian_generates ∧
    type_of% sourceTarget_generated ∧ type_of% sourceTarget_memory ∧
    type_of% sourceTarget_backreaction ∧ type_of% sourceTarget_entropy ∧
    type_of% sourceTarget_binary ∧ type_of% sourceTarget_strict ∧
    type_of% sourceInitial_pointerEnergy ∧ type_of% sourceTarget_pointerEnergy ∧
    type_of% sourceTarget_not_prepared ∧ type_of% initial_joint ∧ type_of% first_joint ∧
    type_of% initial_clock ∧ type_of% first_clock ∧ type_of% next_not_reset ∧
    type_of% initial_entropyProduction ∧ type_of% initial_freeEnergy ∧
    (∀ current, type_of% (entropyProduction_disposition current)) ∧
    (∀ current, type_of% (entropyProduction_nonnegative current)) ∧
    (∀ current, type_of% (measurementWork_body_pointer current)) ∧
    (∀ current, type_of% (measureNext_net_account current)) ∧
    (∀ current, type_of% (loadNext_net_account current)) ∧
    (∀ current, type_of% (loadNext_body current)) ∧
    (∀ current, type_of% (loadNext_pointer_zero current)) ∧
    (∀ current, type_of% (loadNext_pointer_one current)) ∧
    (∀ time, type_of% (loadPulse_baseline time)) :=
  ⟨sourceHamiltonian_hermitian, sourceHamiltonian_generates, sourceTarget_generated,
    sourceTarget_memory, sourceTarget_backreaction, sourceTarget_entropy, sourceTarget_binary,
    sourceTarget_strict, sourceInitial_pointerEnergy, sourceTarget_pointerEnergy, sourceTarget_not_prepared,
    initial_joint, first_joint, initial_clock, first_clock, next_not_reset, initial_entropyProduction, initial_freeEnergy,
    entropyProduction_disposition, entropyProduction_nonnegative, measurementWork_body_pointer,
    measureNext_net_account, loadNext_net_account, loadNext_body, loadNext_pointer_zero,
    loadNext_pointer_one, loadPulse_baseline⟩

example : type_of% sourceGeneratedPointerInstrument := sourceGeneratedPointerInstrument

example : Collision.energy Load.Source.loadTotalHamiltonian Source.received.joint =
    Measurement.sourceMeasurementDecode Load.Source.loadTotalHamiltonian (zeroRead first.joint) := by
  rw [first_joint]
  exact sourceTarget_memory.symm

example : 0 < pointerEnergy first.joint := by rw [first_joint]; exact sourceTarget_pointerEnergy

example : entropyProduction initial = Load.Producer.loadEntropyProduction Source.received :=
  initial_entropyProduction.trans Thermo.first_retains_paid_entropy

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

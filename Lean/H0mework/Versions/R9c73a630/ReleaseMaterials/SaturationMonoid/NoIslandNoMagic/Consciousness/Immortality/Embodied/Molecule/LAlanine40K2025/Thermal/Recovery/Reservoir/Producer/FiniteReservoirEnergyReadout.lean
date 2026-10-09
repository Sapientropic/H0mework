import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedReservoirCurrent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Readout

open Collision Load.Source Load.Producer.StrictThermal Work.Capacity Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Current
open scoped Matrix ComplexOrder
noncomputable section

def pcMatrix (current : State) := Collision.systemReduce (Powered.Dynamics.systemReduce current.joint)
def donorMatrix (current : State) := Collision.bathReduce (Powered.Dynamics.systemReduce current.joint)

theorem pc_positive (current : State) : (pcMatrix current).PosSemidef :=
  Collision.systemReduce_posSemidef _ (Powered.Dynamics.systemReduce_posSemidef _ current.positive)

theorem pc_trace (current : State) : (pcMatrix current).trace = 1 :=
  (Collision.systemReduce_trace _).trans ((Powered.Dynamics.systemReduce_trace _).trans current.normalized)

theorem donor_positive (current : State) : (donorMatrix current).PosSemidef :=
  Collision.bathReduce_posSemidef _ (Powered.Dynamics.systemReduce_posSemidef _ current.positive)

theorem donor_trace (current : State) : (donorMatrix current).trace = 1 :=
  (Collision.bathReduce_trace _).trans ((Powered.Dynamics.systemReduce_trace _).trans current.normalized)

def pcEnergy (current : State) : ℝ := energy Powered.Producer.poweredTotalHamiltonian (pcMatrix current)
def donorEnergy (current : State) : ℝ := energy Powered.Producer.poweredTotalHamiltonian (donorMatrix current)
def pcCapacity (current : State) : ℝ := ergotropy Powered.Producer.poweredTotalHamiltonian (pcMatrix current)
  Powered.Producer.poweredTotalHamiltonian_hermitian (pc_positive current).isHermitian

def donorAvailable (current : State) : ℝ := donorEnergy current -
  Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.lastIndex (ι := PairController))

theorem initial_pc : pcMatrix initial = (Load.Producer.RecoveryLedger.pcRead Source.received).joint := by
  rw [pcMatrix, initial_pair, Source.pairOrigin, Collision.systemReduce_tensor, Source.donor_trace, one_smul]

theorem initial_donor : donorMatrix initial = Source.donor := by
  rw [donorMatrix, initial_pair, Source.pairOrigin, Collision.bathReduce_tensor,
    (Load.Producer.RecoveryLedger.pcRead Source.received).normalized, one_smul]

theorem first_pc_actual : pcMatrix (supplyNext initial) = Collision.systemReduce Native.pairTarget := by
  rw [pcMatrix, first_pair_actual]

theorem first_donor_actual : donorMatrix (supplyNext initial) = Collision.bathReduce Native.pairTarget := by
  rw [donorMatrix, first_pair_actual]

theorem first_pc_energy_gain : 6 < pcEnergy (supplyNext initial) - pcEnergy initial := by
  rw [pcEnergy, pcEnergy, first_pc_actual, initial_pc]
  exact Native.pc_energy_gain

theorem first_donor_paid_gain : 6 < donorEnergy initial - donorEnergy (supplyNext initial) := by
  rw [donorEnergy, donorEnergy, initial_donor, first_donor_actual]
  exact Native.donor_paid_gain

theorem first_pc_capacity_gain : 6 < pcCapacity (supplyNext initial) - pcCapacity initial := by
  unfold pcCapacity
  simp only [first_pc_actual, Native.pairTarget_pc, initial_pc]
  exact Native.pc_capacity_gain

theorem donor_available_range (current : State) :
    0 ≤ donorAvailable current ∧ donorAvailable current ≤
      Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.firstIndex (ι := PairController)) -
        Powered.Producer.poweredTotalHamiltonian_hermitian.eigenvalues (Spectrum.lastIndex (ι := PairController)) := by
  have bounds := Spectrum.energy_spectral_bounds Powered.Producer.poweredTotalHamiltonian (donorMatrix current)
    Powered.Producer.poweredTotalHamiltonian_hermitian (donor_positive current) (donor_trace current)
  constructor <;> dsimp only [donorAvailable, donorEnergy] <;> linarith [bounds.1, bounds.2]

theorem supply_energy_balance (current : State) :
    (pcEnergy (supplyNext current) - pcEnergy current) +
      (donorEnergy (supplyNext current) - donorEnergy current) = 0 := by
  have raw := Exchange.native_energy_balance Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian Native.sourceCoupling (nativeClockStep : ℝ)
    (Powered.Dynamics.systemReduce current.joint)
  change energy Powered.Producer.poweredTotalHamiltonian
      (Collision.systemReduce (Quantum.conjugation (Native.pairFlow (nativeClockStep : ℝ))
        (Powered.Dynamics.systemReduce current.joint))) +
    energy Powered.Producer.poweredTotalHamiltonian
      (Collision.bathReduce (Quantum.conjugation (Native.pairFlow (nativeClockStep : ℝ))
        (Powered.Dynamics.systemReduce current.joint))) = _ at raw
  rw [← supplyNext_pair] at raw
  change pcEnergy (supplyNext current) + donorEnergy (supplyNext current) =
    pcEnergy current + donorEnergy current at raw
  linarith

theorem supply_paid_from_actual_remaining (current : State) :
    pcEnergy (supplyNext current) - pcEnergy current ≤ donorAvailable current := by
  have balance := supply_energy_balance current
  have floor := (donor_available_range (supplyNext current)).1
  dsimp only [donorAvailable] at floor ⊢
  linarith

theorem first_donor_not_reset : donorMatrix (supplyNext initial) ≠ donorMatrix initial := by
  intro same
  have positive := first_donor_paid_gain
  unfold donorEnergy at positive
  rw [same, sub_self] at positive
  norm_num at positive

theorem actual_pc_is_body_read (current : State) :
    Powered.Dynamics.systemReduce (Incidence.bodyRead current.joint) = pcMatrix current :=
  Incidence.bodyRead_pc current.joint

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Readout
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

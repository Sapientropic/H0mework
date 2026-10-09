import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedReservoirHamiltonians
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.FiniteReservoirEnergyReadout

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.EnergyLedger

open Collision Load.Source Powered.Dynamics Work.Capacity
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Current
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Physical
open scoped Matrix ComplexOrder
noncomputable section

def environmentEnergy (current : State) : ℝ :=
  energy (controllerHamiltonian 2) (controllerReduce current.joint)

theorem environment_body (current : State) :
    environmentEnergy current = Load.Source.environmentEnergy (Incidence.bodyRead current.joint) := by
  change energy (controllerHamiltonian 2) (controllerReduce current.joint) =
    energy (controllerHamiltonian 2) (controllerReduce (Incidence.bodyRead current.joint))
  rw [Incidence.bodyRead_environment]

theorem supply_environment_energy (current : State) :
    environmentEnergy (supplyNext current) = environmentEnergy current := by
  unfold environmentEnergy
  rw [supplyNext_environment]
  let U := Load.Recovery.Control.environmentUnitary (Propagation.Producer.nativeClockStep : ℝ)
  have stationary : Unitary.conjStarAlgAut ℂ (Matrix (Fin 2) (Fin 2) ℂ) U (controllerHamiltonian 2) =
      controllerHamiltonian 2 := by
    rw [Unitary.conjStarAlgAut_apply, ← (Load.Recovery.Control.environmentUnitary_commutes _).eq,
      Matrix.mul_assoc, Unitary.mul_star_self_of_mem U.property, Matrix.mul_one]
  have preserved := energy_unitary_conjugation (controllerHamiltonian 2) (controllerReduce current.joint) U
  rw [stationary] at preserved
  exact preserved

theorem baseline_body (current : State) :
    baselineEnergy current = energy loadTotalHamiltonian (Incidence.bodyRead current.joint) + Readout.donorEnergy current :=
  Incidence.body_and_donor_energy loadTotalHamiltonian Powered.Producer.poweredTotalHamiltonian current.joint

theorem baseline_split (current : State) :
    baselineEnergy current = Readout.pcEnergy current + Readout.donorEnergy current +
      environmentEnergy current + Physical.boundaryEnergy current := by
  rw [baseline_body, Load.Source.totalEnergy_split, ← environment_body, ← Physical.boundary_read]
  have pc : Load.Source.pcEnergy (Incidence.bodyRead current.joint) = Readout.pcEnergy current := by
    change energy Powered.Producer.poweredTotalHamiltonian (systemReduce (Incidence.bodyRead current.joint)) =
      energy Powered.Producer.poweredTotalHamiltonian (Readout.pcMatrix current)
    rw [Readout.actual_pc_is_body_read]
  rw [pc]
  ring

theorem sourceWork_is_boundary_change (current : State) :
    sourceWork current = Physical.boundaryEnergy (supplyNext current) - Physical.boundaryEnergy current := by
  rw [sourceWork_actual, baseline_split, baseline_split, supply_environment_energy]
  linarith [Readout.supply_energy_balance current]

theorem sourceWork_abs_le_two (current : State) : |sourceWork current| ≤ 2 := by
  rw [sourceWork_is_boundary_change]
  have triangle : |Physical.boundaryEnergy (supplyNext current) - Physical.boundaryEnergy current| ≤
      |Physical.boundaryEnergy (supplyNext current)| + |Physical.boundaryEnergy current| := by
    simpa using abs_sub_le (Physical.boundaryEnergy (supplyNext current)) 0 (Physical.boundaryEnergy current)
  exact triangle.trans (by linarith [boundary_abs_le_one (supplyNext current), boundary_abs_le_one current])

theorem load_donor_matrix (current : State) : Readout.donorMatrix (loadNext current) =
    Quantum.conjugation (Native.freePCUnitary (Propagation.Producer.nativeClockStep : ℝ)) (Readout.donorMatrix current) := by
  rw [Readout.donorMatrix, Readout.donorMatrix, loadNext_joint, Incidence.localLift_donor]

theorem load_preserves_baseline (current : State) : baselineEnergy (loadNext current) = baselineEnergy current := by
  rw [baseline_body, baseline_body, loadNext_body]
  have preserved := totalEnergy_conserved Powered.Producer.poweredTotalHamiltonian 2 loadInteraction
    Powered.Producer.poweredTotalHamiltonian_hermitian loadInteraction_hermitian
    (Propagation.Producer.nativeClockStep : ℝ) (Incidence.bodyRead current.joint)
  change energy loadTotalHamiltonian (loadAdvance (Propagation.Producer.nativeClockStep : ℝ)
    (Incidence.bodyRead current.joint)) = energy loadTotalHamiltonian (Incidence.bodyRead current.joint) at preserved
  rw [preserved, Readout.donorEnergy, Readout.donorEnergy, load_donor_matrix, Native.freePC_energy]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.EnergyLedger
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

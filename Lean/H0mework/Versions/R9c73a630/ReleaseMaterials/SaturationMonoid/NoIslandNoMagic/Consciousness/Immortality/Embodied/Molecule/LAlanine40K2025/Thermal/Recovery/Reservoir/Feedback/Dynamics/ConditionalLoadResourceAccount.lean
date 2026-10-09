import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Dynamics.ConditionalReservoirSupply
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Source.SourceGeneratedReservoirHamiltonians
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Dynamics.TransitionProbability

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource

open Collision Load.Source Load.Producer.HeatProbability
open scoped Matrix ComplexOrder
noncomputable section

def boundaryEnergyOf (rho : Current.FullJoint) : ℝ := energy Physical.boundaryHamiltonian rho

theorem pc_body (rho : Current.FullJoint) : pcEnergy (Incidence.bodyRead rho) = pcEnergyOf rho := by
  change energy Powered.Producer.poweredTotalHamiltonian (Powered.Dynamics.systemReduce (Incidence.bodyRead rho)) = _
  rw [Incidence.bodyRead_pc]
  rfl

theorem environment_body (rho : Current.FullJoint) :
    environmentEnergy (Incidence.bodyRead rho) = environmentEnergyOf rho := by
  change energy (Powered.Dynamics.controllerHamiltonian 2) (Powered.Dynamics.controllerReduce (Incidence.bodyRead rho)) = _
  rw [Incidence.bodyRead_environment]
  rfl

theorem boundary_body (rho : Current.FullJoint) :
    boundaryEnergy (Incidence.bodyRead rho) = boundaryEnergyOf rho :=
  (Incidence.bodyObservable_energy loadInteraction rho).symm

theorem baseline_energy_split (rho : Current.FullJoint) :
    energy Physical.baselineHamiltonian rho =
      pcEnergyOf rho + donorEnergyOf rho + environmentEnergyOf rho + boundaryEnergyOf rho := by
  change energy (Incidence.bodyObservable loadTotalHamiltonian +
    Incidence.donorObservable Powered.Producer.poweredTotalHamiltonian) rho = _
  rw [Incidence.body_and_donor_energy, totalEnergy_split, pc_body, environment_body, boundary_body]
  change pcEnergyOf rho + environmentEnergyOf rho + boundaryEnergyOf rho + donorEnergyOf rho = _
  ring

theorem load_body (time : ℝ) (rho : Current.FullJoint) :
    Incidence.bodyRead (Quantum.conjugation (Current.loadPulse time) rho) =
      loadAdvance time (Incidence.bodyRead rho) :=
  Incidence.localLift_read (loadUnitary time) (Native.freePCUnitary time) rho

theorem load_donor (time : ℝ) (rho : Current.FullJoint) :
    donorMatrixOf (Quantum.conjugation (Current.loadPulse time) rho) =
      Quantum.conjugation (Native.freePCUnitary time) (donorMatrixOf rho) :=
  Incidence.localLift_donor (loadUnitary time) (Native.freePCUnitary time) rho

theorem load_donor_energy (time : ℝ) (rho : Current.FullJoint) :
    donorEnergyOf (Quantum.conjugation (Current.loadPulse time) rho) = donorEnergyOf rho := by
  simp only [donorEnergyOf, load_donor, Native.freePC_energy]

theorem load_pce_energy_balance (time : ℝ) (rho : Current.FullJoint) :
    (pcEnergyOf (Quantum.conjugation (Current.loadPulse time) rho) - pcEnergyOf rho) +
      (environmentEnergyOf (Quantum.conjugation (Current.loadPulse time) rho) - environmentEnergyOf rho) +
      (boundaryEnergyOf (Quantum.conjugation (Current.loadPulse time) rho) - boundaryEnergyOf rho) = 0 := by
  have balance := loadAdvance_energyBalance time (Incidence.bodyRead rho)
  rw [← load_body] at balance
  simpa only [pc_body, environment_body, boundary_body] using balance

theorem load_pce_energy (time : ℝ) (rho : Current.FullJoint) :
    pcEnergyOf (Quantum.conjugation (Current.loadPulse time) rho) +
      environmentEnergyOf (Quantum.conjugation (Current.loadPulse time) rho) +
      boundaryEnergyOf (Quantum.conjugation (Current.loadPulse time) rho) =
    pcEnergyOf rho + environmentEnergyOf rho + boundaryEnergyOf rho := by
  linarith [load_pce_energy_balance time rho]

theorem load_baseline_energy (time : ℝ) (rho : Current.FullJoint) :
    energy Physical.baselineHamiltonian (Quantum.conjugation (Current.loadPulse time) rho) =
      energy Physical.baselineHamiltonian rho := by
  rw [baseline_energy_split, baseline_energy_split, load_donor_energy]
  linarith [load_pce_energy time rho]

theorem pcEnergyOf_add (rho sigma : Current.FullJoint) :
    pcEnergyOf (rho + sigma) = pcEnergyOf rho + pcEnergyOf sigma := by
  simp only [pcEnergyOf, pcMatrixOf, map_add, energy_add_right]

theorem donorEnergyOf_add (rho sigma : Current.FullJoint) :
    donorEnergyOf (rho + sigma) = donorEnergyOf rho + donorEnergyOf sigma := by
  simp only [donorEnergyOf, donorMatrixOf, map_add, energy_add_right]

theorem environmentEnergyOf_add (rho sigma : Current.FullJoint) :
    environmentEnergyOf (rho + sigma) = environmentEnergyOf rho + environmentEnergyOf sigma := by
  simp only [environmentEnergyOf, map_add, energy_add_right]

theorem boundaryEnergyOf_add (rho sigma : Current.FullJoint) :
    boundaryEnergyOf (rho + sigma) = boundaryEnergyOf rho + boundaryEnergyOf sigma :=
  energy_add_right _ _ _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Resource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

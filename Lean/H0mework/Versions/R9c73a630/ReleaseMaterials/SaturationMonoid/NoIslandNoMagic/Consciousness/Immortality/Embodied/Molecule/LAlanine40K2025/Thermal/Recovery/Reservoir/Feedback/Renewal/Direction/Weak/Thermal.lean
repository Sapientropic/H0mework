import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Account
set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak

open Collision Resource Load.Source Powered.Dynamics
open scoped Matrix ComplexOrder
noncomputable section

/-- Both account presentations read the same environment marginal, including correlated states. -/
theorem environment_marginal {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (rho : Matrix ((ι × κ) ⊕ (ι × κ)) ((ι × κ) ⊕ (ι × κ)) ℂ) :
    controllerReduce (Environment.reframe rho)=controllerReduce (bodyRead rho) := by
  ext e f
  change (∑ i : ι ⊕ ι, Environment.reframe rho (i,e) (i,f))=
    ∑ i : ι, bodyRead rho (i,e) (i,f)
  simp [Environment.reframe, Environment.incidence, bodyRead,
    Fintype.sum_sum_type, Finset.sum_add_distrib, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂,
    Matrix.submatrix]

theorem environment_energy_same (current : Live.State) :
    Live.environmentEnergy current=environmentEnergyOf (bodyRead current.joint) := by
  unfold Live.environmentEnergy Live.thermalJoint environmentEnergyOf
  rw [environment_marginal]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [environmentEnergies, controllerHamiltonian]

theorem execution_heat_account :
    Live.entropyProduction execution-Live.entropyProduction origin=
      Live.systemEntropy execution-Live.systemEntropy origin+
      (environmentEnergyOf (bodyRead execution.joint)-
        environmentEnergyOf (bodyRead origin.joint)) := by
  rw [Live.entropy_energy_read, Live.entropy_energy_read,
    environment_energy_same, environment_energy_same]
  ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

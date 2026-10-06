import H0mework.Versions.AB.Physics.LowEnergy.Electromagnetic.ActionUnits
import H0mework.Versions.AB.Physics.LowEnergy.Electromagnetic.ExternalState

/-! The original normalized canonical state reads the original quantum energy.
Its amplified classical action and the initial-slice Poisson coefficient return
through the same source phase unit. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalQuantumUnits
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open Stage10.ChargedPreparation Stage10.ActionNormalization
open YangMills.FullPairing
open NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open UnifiedAction.AtomicScales
open scoped InnerProductSpace
noncomputable section

/-- This is the existing physical-background Hamiltonian on the actual state. -/
def energyRead (point : BasePoint) (momentum : Fin 3 → ℝ) : ℝ :=
  (inner ℂ (CanonicalParticle.state point momentum)
    (operator (FullQuantum.hamiltonian Stage10.Runtime.configuration point momentum)
      (CanonicalParticle.state point momentum))).re

theorem source_energy_read (point : BasePoint) (momentum : Fin 3 → ℝ) :
    energyRead point momentum = CanonicalParticle.energy momentum := by
  have eigen : operator (FullQuantum.hamiltonian Stage10.Runtime.configuration point momentum)
      (CanonicalParticle.state point momentum) =
      (CanonicalParticle.energy momentum : ℂ) • CanonicalParticle.state point momentum := by
    simp only [CanonicalParticle.state, operator_coordinates,
      CanonicalParticle.normalized_full_hamiltonian, map_smul]
  rw [energyRead, eigen, inner_smul_right, CanonicalParticle.state_unit, mul_one]
  rfl

theorem original_action_energy_read (point : BasePoint) (momentum : Fin 3 → ℝ) :
    preparedActionEnergy point momentum = phaseMomentum * energyRead point momentum := by
  rw [source_energy_read]
  exact CanonicalParticle.Plane.complete_hamiltonian_difference momentum point

theorem same_source_phase (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    FullQuantum.evolution Stage10.Runtime.configuration point momentum time
      (CanonicalParticle.state point momentum) =
      Complex.exp (-Complex.I * (time : ℂ) * (energyRead point momentum : ℂ)) •
        CanonicalParticle.state point momentum := by
  rw [source_energy_read]
  exact CanonicalParticle.original_evolution point momentum time

/-- Both initial-slice external vertices are converted to their unit-N1 readout. -/
theorem unit_leg_initial_coulomb :
    canonicalCoulomb / phaseMomentum^2 = 1 / (8 * Real.pi * lapse) := by
  rw [original_coulomb_coefficient, phaseMomentum_source]
  field_simp [spinScale_pos.ne']

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalQuantumUnits

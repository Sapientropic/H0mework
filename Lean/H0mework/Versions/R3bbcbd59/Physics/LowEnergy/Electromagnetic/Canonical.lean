import H0mework.Versions.R3bbcbd59.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Action.CanonicalUnits
import H0mework.Physics.LowEnergy.Electromagnetic.Units

/-! The actual prepared state's phase fixes the action unit of the canonical
Coulomb coefficient. The speed remains an explicit readout until the complete
electromagnetic response supplies it. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open Stage10.ActionNormalization Stage10.ChargedPreparation Stage10.StaticHamiltonian
open NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open UnifiedAction UnifiedAction.AtomicScales
noncomputable section

/-- Physical action energy of the existing prepared state, with its common
background subtracted exactly as in the original Hamiltonian consumer. -/
def preparedActionEnergy (point : BasePoint) (momentum : Fin 3 → ℝ) : ℝ :=
  hamiltonianDensity Stage10.Runtime.source (CanonicalParticle.Plane.fields momentum) point -
    hamiltonianDensity Stage10.Runtime.source CanonicalParticle.Plane.reference point

/-- The original time evolution consumes the Hamiltonian divided by the
phase momentum. This identifies the action-unit role, without an SI input. -/
theorem original_action_phase (point : BasePoint) (momentum : Fin 3 → ℝ) (time : ℝ) :
    FullQuantum.evolution Stage10.Runtime.configuration point momentum time
        (CanonicalParticle.state point momentum) =
      Complex.exp (-Complex.I * (time : ℂ) *
        ((preparedActionEnergy point momentum / phaseMomentum : ℝ) : ℂ)) •
          CanonicalParticle.state point momentum := by
  have energy : preparedActionEnergy point momentum / phaseMomentum =
      CanonicalParticle.energy momentum := by
    rw [preparedActionEnergy, CanonicalParticle.Plane.complete_hamiltonian_difference,
      mul_div_cancel_left₀ _ phaseMomentum_positive.ne']
  rw [energy]
  exact CanonicalParticle.original_evolution point momentum time

/-- The already generated Coulomb coefficient expressed in the very same
action unit and a specified physical speed. Its channel remains canonical Y. -/
def canonicalChannelRatio (speed : ℝ) : ℝ :=
  couplingRatio canonicalCoulomb phaseMomentum speed

theorem canonical_channel_ratio (speed : ℝ) :
    canonicalChannelRatio speed = coulombCoefficient / speed := by
  unfold canonicalChannelRatio couplingRatio canonicalCoulomb
  exact mul_div_mul_left _ _ phaseMomentum_positive.ne'

theorem original_pole_normalization :
    canonicalCoulomb = poleCoulomb phaseMomentum (2 * lapse)⁻¹ := by
  unfold poleCoulomb
  rw [original_coulomb_coefficient, phaseMomentum_source]
  ring

theorem canonical_channel_explicit (speed : ℝ) :
    canonicalChannelRatio speed = spinScale / (2 * Real.pi * lapse * speed) := by
  rw [canonicalChannelRatio, couplingRatio, original_coulomb_coefficient, phaseMomentum_source]
  field_simp [spinScale_pos.ne']
  ring

/-- Gauge-principal and matter-principal speed choices have distinct ratios
in the original common coordinates; neither is silently named alpha(0). -/
theorem common_clock_ratios :
    canonicalChannelRatio lapse⁻¹ = spinScale / (2 * Real.pi) ∧
    canonicalChannelRatio lapse =
      (125 / 54 : ℝ) * (spinScale / (2 * Real.pi)) := by
  constructor
  · rw [canonical_channel_explicit]
    field_simp [lapse_pos.ne']
  · rw [canonical_channel_explicit]
    field_simp [Real.pi_pos.ne', lapse_pos.ne']
    rw [lapse_sq]
    ring

/-- Bohr and Hartree are consistent action units, not extra coupling inputs. -/
theorem atomic_ratio_preserved (speed : ℝ) :
    (canonicalCoulomb / (canonicalHartree * sourceLength)) /
      ((phaseMomentum / (canonicalHartree * sourceTime)) *
        (speed * sourceTime / sourceLength)) = canonicalChannelRatio speed := by
  unfold canonicalChannelRatio couplingRatio
  field_simp [canonical_hartree_positive.ne', length_positive.ne', time_positive.ne']

end
end SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic

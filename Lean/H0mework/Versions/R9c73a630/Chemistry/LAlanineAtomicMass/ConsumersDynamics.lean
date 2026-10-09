import H0mework.Versions.R9c73a630.Chemistry.LAlanineAtomicMass.SourceMassNumber
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNuclearKinematics
import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNuclearKinetic

/-!
# Original dynamics consume the isotope mass with its residual

The recovered mass feeds the original Verlet update and all 39 momentum coordinates.
The actual nitrogen momentum also separates the mass from its integer-mass replacement.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.AtomicMass.Dynamics

open Force.Interface Inertia.Mechanics Inertia.SourceParsing
noncomputable section

def reconstructedReference : PhasePoint :=
  verletStep Source.reconstructedMass Reentry.Source.stepReadout.nuclear.duration
    Reentry.Source.stepReadout.nuclear.current.force Reentry.Source.stepReadout.nuclear.target.force
    Reentry.Source.stepReadout.nuclear.current.phase

theorem reconstructedReference_eq_original :
    reconstructedReference = Reentry.Producer.nuclearReference := by
  unfold reconstructedReference
  rw [Source.reconstructedMass_eq_actual]
  rfl

theorem actual_target_from_isotope_mass : Reentry.Source.stepReadout.nuclear.target.phase =
    addResidual reconstructedReference Reentry.Producer.nuclearResidual := by
  rw [reconstructedReference_eq_original]
  exact Reentry.Producer.nuclearPhase_reconstruction

/-- All target momentum coordinates use their own reconstructed source mass. -/
def reconstructedKinetic : ℚ :=
  ∑ atom : Atom, (∑ axis : Axis, Reentry.Source.stepReadout.nuclear.target.momentum atom axis ^ 2) /
    (2 * Source.reconstructedMass atom)

theorem reconstructedKinetic_eq_original :
    reconstructedKinetic = Reentry.Producer.targetMomentumKinetic := by
  unfold reconstructedKinetic
  rw [Source.reconstructedMass_eq_actual]
  rfl

theorem actual_kinetic_from_isotope_mass : Reentry.Source.stepReadout.nuclear.target.kinetic =
    reconstructedKinetic + Reentry.Producer.targetKineticResidual := by
  rw [reconstructedKinetic_eq_original]
  exact Reentry.Producer.targetKinetic_reconstruction

theorem actual_energy_from_isotope_mass : Reentry.Source.stepReadout.nuclear.target.total =
    reconstructedKinetic + Reentry.Source.stepReadout.nuclear.target.potential +
      Reentry.Producer.targetKineticResidual := by
  rw [reconstructedKinetic_eq_original]
  exact Reentry.Producer.targetMechanicalEnergyWholeAccount

/-- Momentum is the original nitrogen coordinate at the 2q input of this occurrence. -/
def nitrogenVelocityAtMass (mass : ℚ) : ℚ :=
  Reentry.Source.stepReadout.nuclear.current.momentum 2 0 / mass

theorem actual_nitrogen_momentum_nonzero :
    Reentry.Source.stepReadout.nuclear.current.momentum 2 0 ≠ 0 := by
  change rationalRead _ ≠ 0
  norm_num [rationalRead]

theorem nitrogenVelocityAtMass_injective : Function.Injective nitrogenVelocityAtMass := by
  intro left right same
  apply inv_injective
  apply mul_left_cancel₀ actual_nitrogen_momentum_nonzero
  simpa only [nitrogenVelocityAtMass, div_eq_mul_inv] using same

theorem integer_mass_changes_actual_velocity :
    nitrogenVelocityAtMass (Source.actualMass 2) ≠
      nitrogenVelocityAtMass (14 * Source.preparation.conversion) := by
  intro same
  exact (ne_of_gt Source.nitrogen_mass_exceeds_integer) (nitrogenVelocityAtMass_injective same)

end
end LAlanine40K2025.AtomicMass.Dynamics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

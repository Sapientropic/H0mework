import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Source.SourceGeneratedPointerLoadPulse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Dynamics.PointerControlWork

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback

open Powered.Dynamics Collision Load.Producer.StrictThermal
open scoped Matrix ComplexOrder Matrix.Norms.Operator
noncomputable section

def feedbackPulse (time : ℝ) : Matrix.unitaryGroup PointerIndex ℂ :=
  blockUnitary (Current.loadPulse time) (freePhase time • Current.pulse time)

def feedbackHamiltonian : PointerJoint :=
  Matrix.fromBlocks Physical.baselineHamiltonian 0 0 (Physical.controlHamiltonian + (2 : ℂ) • 1)

theorem controlHamiltonian_hermitian : Physical.controlHamiltonian.IsHermitian :=
  bareHamiltonian_hermitian Physical.pairHamiltonian 2 Physical.pairHamiltonian_hermitian

theorem feedbackHamiltonian_hermitian : feedbackHamiltonian.IsHermitian :=
  oldBaseline_hermitian.fromBlocks (by simp)
    (controlHamiltonian_hermitian.add (Matrix.isHermitian_one.smul (by simp)))

theorem controlPulse_eq_exp (time : ℝ) :
    (Current.pulse time : Current.FullJoint) =
      NormedSpace.exp (time • (-Complex.I • Physical.controlHamiltonian)) := by
  rw [← Physical.pulse_is_full_flow, flowUnitary_matrix_exp]
  simp only [Physical.controlHamiltonian, totalHamiltonian, add_zero]

attribute [local irreducible] Physical.baselineHamiltonian Physical.controlHamiltonian
  Current.loadPulse Current.pulse

theorem feedbackPulse_eq_exp (time : ℝ) :
    (feedbackPulse time : PointerJoint) =
      NormedSpace.exp (time • (-Complex.I • feedbackHamiltonian)) := by
  have generator : time • (-Complex.I • feedbackHamiltonian) =
      Matrix.fromBlocks (time • (-Complex.I • Physical.baselineHamiltonian)) 0 0
        (time • (-Complex.I • (Physical.controlHamiltonian + (2 : ℂ) • 1))) := by
    simp only [feedbackHamiltonian, Matrix.fromBlocks_smul, smul_zero]
  rw [generator, exp_fromBlocks_diagonal, shifted_exponential,
    ← Physical.loadPulse_baseline, ← controlPulse_eq_exp]
  rfl

theorem feedbackPulse_commutes (time : ℝ) :
    Commute feedbackHamiltonian (feedbackPulse time : PointerJoint) := by
  rw [feedbackPulse_eq_exp]
  exact matrix_generator_commutes feedbackHamiltonian time

theorem feedbackControl_conserves (time : ℝ) (joint : PointerJoint) :
    energy feedbackHamiltonian (Quantum.conjugation (feedbackPulse time) joint) =
      energy feedbackHamiltonian joint := by
  simpa only [Quantum.conjugation_apply] using
    Recovery.PreparationEnergy.commuting_energy feedbackHamiltonian joint
      (feedbackPulse time) (feedbackPulse_commutes time)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

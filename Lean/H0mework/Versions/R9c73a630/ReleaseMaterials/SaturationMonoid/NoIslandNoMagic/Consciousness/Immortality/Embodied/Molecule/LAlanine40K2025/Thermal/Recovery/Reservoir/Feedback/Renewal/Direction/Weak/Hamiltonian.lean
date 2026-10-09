import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.WeakSupply
set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak

open Collision Resource Propagation.Producer Load.Source Load.Producer.StrictThermal Powered.Dynamics
open scoped Matrix ComplexOrder Matrix.Norms.Operator
noncomputable section

/-! The registered weak pulse owns its control Hamiltonian and switching work. -/

def controlPairHamiltonian : JointMatrix PairController :=
  Dynamics.pairH Powered.Producer.poweredTotalHamiltonian LAlanine40K2025.Thermal.Source.pairCoupling

def controlFullHamiltonian : Current.FullJoint := bareHamiltonian controlPairHamiltonian 2

def controlPointerHamiltonian : PointerJoint :=
  Matrix.fromBlocks Physical.baselineHamiltonian 0 0 (controlFullHamiltonian+(2 : ℂ) • 1)

theorem control_pair_hermitian : controlPairHamiltonian.IsHermitian :=
  Dynamics.pairH_hermitian _ Powered.Producer.poweredTotalHamiltonian_hermitian _

theorem control_full_hermitian : controlFullHamiltonian.IsHermitian :=
  bareHamiltonian_hermitian _ 2 control_pair_hermitian

theorem control_pointer_hermitian : controlPointerHamiltonian.IsHermitian :=
  oldBaseline_hermitian.fromBlocks (by simp)
    (control_full_hermitian.add (Matrix.isHermitian_one.smul (by simp)))

theorem pair_pulse_eq_exp (time : ℝ) :
    (pairPulse time : JointMatrix PairController) =
      NormedSpace.exp (time • (-Complex.I • controlPairHamiltonian)) := by
  change Dynamics.pairPropagatorMatrix Powered.Producer.poweredTotalHamiltonian
    LAlanine40K2025.Thermal.Source.pairCoupling time = _
  rw [Dynamics.pairPropagatorMatrix_eq_exp]
  change NormedSpace.exp ((-Complex.I*(time : ℂ)) • controlPairHamiltonian) = _
  congr 1
  ext i j
  simp only [Matrix.smul_apply,Complex.real_smul]
  ring

theorem full_pulse_eq_exp (time : ℝ) :
    (fullPulse time : Current.FullJoint) =
      NormedSpace.exp (time • (-Complex.I • controlFullHamiltonian)) := by
  have split : time • (-Complex.I • controlFullHamiltonian) =
      Matrix.kronecker (time • (-Complex.I • controlPairHamiltonian)) 1+
        Matrix.kronecker 1 (time • (-Complex.I • controllerHamiltonian 2)) := by
    ext i j
    simp only [controlFullHamiltonian,bareHamiltonian,Matrix.add_apply,Matrix.smul_apply,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Complex.real_smul]
    ring
  rw [split,Load.Recovery.Control.exp_tensor_sum,← pair_pulse_eq_exp]
  rfl

attribute [local irreducible] Physical.baselineHamiltonian controlFullHamiltonian
  Current.loadPulse fullPulse

theorem pointer_pulse_eq_exp (time : ℝ) :
    (pointerPulse time : PointerJoint) =
      NormedSpace.exp (time • (-Complex.I • controlPointerHamiltonian)) := by
  have generator : time • (-Complex.I • controlPointerHamiltonian) =
      Matrix.fromBlocks (time • (-Complex.I • Physical.baselineHamiltonian)) 0 0
        (time • (-Complex.I • (controlFullHamiltonian+(2 : ℂ) • 1))) := by
    simp only [controlPointerHamiltonian,Matrix.fromBlocks_smul,smul_zero]
  rw [generator,exp_fromBlocks_diagonal,shifted_exponential,
    ← Physical.loadPulse_baseline,← full_pulse_eq_exp]
  rfl

theorem pointer_pulse_commutes (time : ℝ) :
    Commute controlPointerHamiltonian (pointerPulse time : PointerJoint) := by
  rw [pointer_pulse_eq_exp]
  exact matrix_generator_commutes controlPointerHamiltonian time

theorem control_energy_conserved (time : ℝ) (joint : PointerJoint) :
    energy controlPointerHamiltonian (Quantum.conjugation (pointerPulse time) joint) =
      energy controlPointerHamiltonian joint := by
  simpa only [Quantum.conjugation_apply] using
    Recovery.PreparationEnergy.commuting_energy controlPointerHamiltonian joint
      (pointerPulse time) (pointer_pulse_commutes time)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

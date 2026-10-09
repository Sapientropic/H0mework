import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Evolution
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface Powered.Source Powered.Dynamics
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem flow_conjugation (U : Matrix.unitaryGroup ι ℂ) (H : Matrix ι ι ℂ) (time : ℝ) :
    Quantum.conjugation U (hamiltonianFlow H time) = hamiltonianFlow (Quantum.conjugation U H) time := by
  let phi := Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U
  let : NormedAlgebra ℚ (Matrix ι ι ℂ) := .restrictScalars ℚ ℂ _
  change phi (NormedSpace.exp (time • (-Complex.I • H))) =
    NormedSpace.exp (time • (-Complex.I • (Quantum.conjugation U H)))
  rw [NormedSpace.map_exp phi phi.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous]
  congr 1
  simp only [phi,Unitary.conjStarAlgAut_apply,Quantum.conjugation_apply,smul_mul_assoc,mul_smul_comm]

theorem actual_diagonal_hermitian : E.IsHermitian := by
  unfold E
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext i
  simp

theorem numeric_PC_hermitian : (sourcePCH E).IsHermitian :=
  totalHamiltonian_hermitian _ _ _ (pairHamiltonian_hermitian _ actual_diagonal_hermitian) (interaction_hermitian E)

def installedPCFrame : Matrix.unitaryGroup Load.Source.PairController ℂ := controllerFrame originalToCalculated

attribute [local irreducible] installedPCFrame Powered.Producer.poweredTotalHamiltonian

theorem actual_PC_flow_error (time : ℝ) :
    ‖Quantum.conjugation installedPCFrame (hamiltonianFlow Powered.Producer.poweredTotalHamiltonian time)-
      hamiltonianFlow (sourcePCH E) time‖ ≤ |time| * (126/10^12 : ℝ) := by
  rw [flow_conjugation]
  have original : (Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian).IsHermitian := by
    rw [Quantum.conjugation_apply]
    exact Matrix.isHermitian_mul_mul_conjTranspose _ Powered.Producer.poweredTotalHamiltonian_hermitian
  have paid : ‖Quantum.conjugation installedPCFrame Powered.Producer.poweredTotalHamiltonian-sourcePCH E‖ ≤
      (126/10^12 : ℝ) := by
    unfold installedPCFrame
    exact actual_powered_Hamiltonian_error
  exact (hamiltonian_flow_error _ _ original numeric_PC_hermitian time).trans
    (mul_le_mul_of_nonneg_left paid (abs_nonneg time))

/-- The registered analytic flow is the same full matrix exponential used by the error theorem. -/
theorem original_controller_flow (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian) (time : ℝ) :
    (flowUnitary H gap V hH hV time : ControllerJoint ι) = hamiltonianFlow (totalHamiltonian H gap V) time := by
  let equiv := Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)
  let : NormedAlgebra ℚ (ControllerSpace ι →L[ℂ] ControllerSpace ι) := .restrictScalars ℚ ℂ _
  change equiv.symm (NormedSpace.exp _) = NormedSpace.exp (time • (-Complex.I • totalHamiltonian H gap V))
  rw [NormedSpace.map_exp equiv.symm equiv.symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous]
  congr 1
  simp only [map_smul,controllerOperator]
  ext i j
  simp [Matrix.smul_apply,smul_eq_mul,equiv]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

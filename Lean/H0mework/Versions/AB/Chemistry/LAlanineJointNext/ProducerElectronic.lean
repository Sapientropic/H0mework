import H0mework.Versions.AB.Chemistry.LAlanineJointNext.ProducerCoefficients
import H0mework.Chemistry.LAlanineJointNext.DynamicsRealRestriction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourceJointUnitary : Matrix.unitaryGroup Basis ℂ :=
  Math.jointUnitary Source.hamiltonian sourceHamiltonian_hermitian (Interface.duration : ℝ)
    Source.crossMatrix sourceCross_close

def exactTarget : Matrix Basis Basis ℂ :=
  Interface.exactElectronicTarget Source.hamiltonian sourceHamiltonian_hermitian Source.crossMatrix

def realizedInputTarget : Matrix Basis Basis ℂ :=
  Interface.realizedInputTarget Source.hamiltonian sourceHamiltonian_hermitian Source.crossMatrix

def inheritedResidual : Matrix Basis Basis ℂ := realizedInputTarget - exactTarget
def newNumericalResidual : Matrix Basis Basis ℂ := Source.targetRealized - realizedInputTarget
def totalRealizationResidual : Matrix Basis Basis ℂ := Source.targetRealized - exactTarget

theorem exactTarget_joint : exactTarget =
    Unitary.conjStarAlgAut ℂ _ sourceJointUnitary Runtime.jointParentHeld :=
  Math.electronicAdvance_joint _ _ _ _ _ sourceCross_close

theorem exactTarget_faithful :
    Unitary.conjStarAlgAut ℂ _ (star sourceJointUnitary) exactTarget = Runtime.jointParentHeld :=
  Math.electronicAdvance_faithful _ _ _ _ _ sourceCross_close

theorem exactTarget_trace : exactTarget.trace = Runtime.jointParentHeld.trace :=
  Math.electronicAdvance_trace _ _ _ _ _ sourceCross_close

theorem exactTarget_spectrum : spectrum ℂ exactTarget = spectrum ℂ Runtime.jointParentHeld := by
  rw [exactTarget_joint]
  exact Unitary.spectrum_star_right_conjugate (U := sourceJointUnitary)

theorem parentHeld_hermitian : Runtime.jointParentHeld.IsHermitian := by
  change (ElectronicFrame.Source.heldStateTransport ElectronicFrame.Producer.heldMatrix).IsHermitian
  apply ElectronicFrame.Source.heldStateTransport_hermitian
  exact Propagation.Dynamics.initialDensityMatrix_hermitian _

theorem exactTarget_hermitian : exactTarget.IsHermitian :=
  Math.electronicAdvance_hermitian _ _ _ _ _ parentHeld_hermitian

theorem inherited_error_exact :
    ‖inheritedResidual‖ = ‖Runtime.jointParentRealization.1 - Runtime.jointParentHeld‖ :=
  Math.electronicAdvance_error_eq _ _ _ _ _ _ sourceCross_close

theorem inherited_error_bound : ‖inheritedResidual‖ < (8 : ℝ) / 10 ^ 9 :=
  Interface.inherited_realization_error _ _ _ sourceCross_close

/-- Newly introduced numerical error is a separate readout, never a reset of the inherited error budget. -/
theorem total_error_reconstruction : totalRealizationResidual = inheritedResidual + newNumericalResidual ∧
    Source.targetRealized = exactTarget + inheritedResidual + newNumericalResidual := by
  dsimp only [totalRealizationResidual, inheritedResidual, newNumericalResidual]
  constructor <;> abel

theorem total_error_account : ‖totalRealizationResidual‖ < (8 : ℝ) / 10 ^ 9 + ‖newNumericalResidual‖ := by
  rw [total_error_reconstruction.1]
  have triangle : ‖inheritedResidual + newNumericalResidual‖ ≤ ‖inheritedResidual‖ + ‖newNumericalResidual‖ :=
    norm_add_le inheritedResidual newNumericalResidual
  exact triangle.trans_lt (by linarith [inherited_error_bound])

def pullOperator (O : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  star (sourceJointUnitary : Matrix Basis Basis ℂ) * O * sourceJointUnitary

theorem independent_operator_commutes (O : Matrix Basis Basis ℂ) :
    (exactTarget * O).trace = (Runtime.jointParentHeld * pullOperator O).trace := by
  rw [exactTarget_joint]
  change (((sourceJointUnitary : Matrix Basis Basis ℂ) * Runtime.jointParentHeld *
    star (sourceJointUnitary : Matrix Basis Basis ℂ)) * O).trace = _
  calc
    _ = ((sourceJointUnitary : Matrix Basis Basis ℂ) *
      (Runtime.jointParentHeld * (star (sourceJointUnitary : Matrix Basis Basis ℂ) * O))).trace := by
        simp only [mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [pullOperator, mul_assoc]

theorem scalar_energy_restriction (A : Matrix Basis Basis ℝ) :
    (RealRestriction.complexify A * Source.targetRealized).trace.re =
      (A * RealRestriction.realPart Source.targetRealized).trace := RealRestriction.scalar_trace_restriction _ _

end
end LAlanine40K2025.JointNext.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

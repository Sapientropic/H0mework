import H0mework.Versions.AB.Chemistry.LAlanineReentry.ProducerNormBounds

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def sourceJointUnitary : Matrix.unitaryGroup Basis ℂ :=
  JointNext.Math.jointUnitary Source.hamiltonian sourceHamiltonian_hermitian (Continuation.duration : ℝ)
    Source.crossMatrix sourceCross_close

def exactTarget : Matrix Basis Basis ℂ :=
  Continuation.exactTarget Source.hamiltonian sourceHamiltonian_hermitian Source.crossMatrix

def realizedInputTarget : Matrix Basis Basis ℂ :=
  Continuation.numericalInputTarget Source.hamiltonian sourceHamiltonian_hermitian Source.crossMatrix

def inheritedResidual : Matrix Basis Basis ℂ :=
  Continuation.inheritedResidual Source.hamiltonian sourceHamiltonian_hermitian Source.crossMatrix

def newNumericalResidual : Matrix Basis Basis ℂ := Source.targetRealized - realizedInputTarget
def totalRealizationResidual : Matrix Basis Basis ℂ := Source.targetRealized - exactTarget

theorem exactTarget_joint : exactTarget =
    Unitary.conjStarAlgAut ℂ _ sourceJointUnitary Runtime.reentryParentHeld :=
  JointNext.Math.electronicAdvance_joint _ _ _ _ _ sourceCross_close

theorem exactTarget_faithful :
    Unitary.conjStarAlgAut ℂ _ (star sourceJointUnitary) exactTarget = Runtime.reentryParentHeld :=
  JointNext.Math.electronicAdvance_faithful _ _ _ _ _ sourceCross_close

theorem exactTarget_trace : exactTarget.trace = Runtime.reentryParentHeld.trace :=
  JointNext.Math.electronicAdvance_trace _ _ _ _ _ sourceCross_close

theorem exactTarget_spectrum : spectrum ℂ exactTarget = spectrum ℂ Runtime.reentryParentHeld := by
  rw [exactTarget_joint]
  exact Unitary.spectrum_star_right_conjugate (U := sourceJointUnitary)

theorem exactTarget_hermitian : exactTarget.IsHermitian :=
  JointNext.Math.electronicAdvance_hermitian _ _ _ _ _ JointNext.Producer.exactTarget_hermitian

theorem inherited_error_exact : ‖inheritedResidual‖ = ‖Runtime.reentryParentResidual‖ :=
  Continuation.inheritedResidual_norm _ _ _ sourceCross_close

theorem inherited_error_bound : ‖inheritedResidual‖ < (1 : ℝ) / 10 ^ 8 :=
  Continuation.inheritedResidual_bound _ _ _ sourceCross_close

theorem total_error_reconstruction : totalRealizationResidual = inheritedResidual + newNumericalResidual ∧
    Source.targetRealized = exactTarget + inheritedResidual + newNumericalResidual := by
  have identity := Continuation.totalResidual_reconstruction Source.hamiltonian sourceHamiltonian_hermitian
    Source.crossMatrix sourceCross_close Source.targetRealized
  change Source.targetRealized - exactTarget = inheritedResidual + newNumericalResidual at identity
  refine ⟨identity, ?_⟩
  calc
    Source.targetRealized = exactTarget + (Source.targetRealized - exactTarget) := by abel
    _ = exactTarget + (inheritedResidual + newNumericalResidual) := congrArg (exactTarget + ·) identity
    _ = _ := by abel

theorem total_error_account :
    ‖totalRealizationResidual‖ ≤ ‖Runtime.reentryParentResidual‖ + ‖newNumericalResidual‖ :=
  Continuation.totalResidual_bound _ _ _ sourceCross_close _

def pullOperator (O : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  star (sourceJointUnitary : Matrix Basis Basis ℂ) * O * sourceJointUnitary

theorem independent_operator_commutes (O : Matrix Basis Basis ℂ) :
    (exactTarget * O).trace = (Runtime.reentryParentHeld * pullOperator O).trace := by
  rw [exactTarget_joint]
  change (((sourceJointUnitary : Matrix Basis Basis ℂ) * Runtime.reentryParentHeld *
    star (sourceJointUnitary : Matrix Basis Basis ℂ)) * O).trace = _
  calc
    _ = ((sourceJointUnitary : Matrix Basis Basis ℂ) *
      (Runtime.reentryParentHeld * (star (sourceJointUnitary : Matrix Basis Basis ℂ) * O))).trace := by
        simp only [mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_comm]; simp only [pullOperator, mul_assoc]

theorem scalar_energy_restriction (A : Matrix Basis Basis ℝ) :
    (JointNext.RealRestriction.complexify A * Source.targetRealized).trace.re =
      (A * JointNext.RealRestriction.realPart Source.targetRealized).trace :=
  JointNext.RealRestriction.scalar_trace_restriction _ _

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

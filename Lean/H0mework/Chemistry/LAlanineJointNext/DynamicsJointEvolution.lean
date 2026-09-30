import H0mework.Chemistry.LAlaninePropagation.GeneratedElectronicDynamics
import H0mework.Chemistry.LAlanineElectronicFrame.DynamicsPolarFrameTransport
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.JointNext.Math

open _root_.SaturationMonoid.AffineRelaxation
open Propagation.Interface Propagation.Dynamics
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

theorem frozenFlow (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) :
    BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate ElectronicSpace (matrixOperatorEquiv H) :=
  boundedSelfAdjointHamiltonianSchrodingerFlowCertificate _ (hermitian.isSelfAdjoint.map matrixOperatorEquiv)

def frozenUnitary (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ) :
    Matrix.unitaryGroup Basis ℂ :=
  ⟨matrixOperatorEquiv.symm (NormedSpace.exp ((duration : ℂ) • (-Complex.I • matrixOperatorEquiv H))),
    Unitary.map_mem matrixOperatorEquiv.symm ((frozenFlow H hermitian).exponential_group.unitarySlice duration)⟩

theorem frozenUnitary_eq_exp (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ) :
    (frozenUnitary H hermitian duration : Matrix Basis Basis ℂ) =
      NormedSpace.exp (duration • (-Complex.I • H)) := by
  let : NormedAlgebra ℚ ElectronicOperator := .restrictScalars ℚ ℂ _
  change matrixOperatorEquiv.symm (NormedSpace.exp _) = _
  rw [NormedSpace.map_exp matrixOperatorEquiv.symm
    matrixOperatorEquiv.symm.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.continuous]
  congr 1
  simp only [map_smul, StarAlgEquiv.symm_apply_apply]
  ext i j
  simp [Matrix.smul_apply, smul_eq_mul]

theorem frozenUnitary_hasDerivAt (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ) :
    HasDerivAt (fun t => (frozenUnitary H hermitian t : Matrix Basis Basis ℂ))
      ((frozenUnitary H hermitian duration : Matrix Basis Basis ℂ) * (-Complex.I • H)) duration := by
  simp only [frozenUnitary_eq_exp]
  exact hasDerivAt_exp_smul_const _ _

/-- The elapsed evolution and geometric re-expression act on the same full state. -/
def electronicAdvance (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ)
    (cross current : Matrix Basis Basis ℂ) : Matrix Basis Basis ℂ :=
  ElectronicFrame.Polar.transport cross (Unitary.conjStarAlgAut ℂ _ (frozenUnitary H hermitian duration) current)

def jointUnitary (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ)
    (cross : Matrix Basis Basis ℂ) (close : ‖cross - 1‖ < 1) : Matrix.unitaryGroup Basis ℂ :=
  ElectronicFrame.Polar.unitary cross close * frozenUnitary H hermitian duration

theorem electronicAdvance_joint (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ)
    (cross current : Matrix Basis Basis ℂ) (close : ‖cross - 1‖ < 1) :
    electronicAdvance H hermitian duration cross current =
      Unitary.conjStarAlgAut ℂ _ (jointUnitary H hermitian duration cross close) current := by
  rw [jointUnitary, Unitary.conjStarAlgAut_mul_apply]
  rfl

theorem electronicAdvance_faithful (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ)
    (cross current : Matrix Basis Basis ℂ) (close : ‖cross - 1‖ < 1) :
    Unitary.conjStarAlgAut ℂ _ (star (jointUnitary H hermitian duration cross close))
      (electronicAdvance H hermitian duration cross current) = current := by
  rw [electronicAdvance_joint H hermitian duration cross current close,
    ← Unitary.conjStarAlgAut_mul_apply]
  simp

theorem electronicAdvance_trace (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ)
    (cross current : Matrix Basis Basis ℂ) (close : ‖cross - 1‖ < 1) :
    (electronicAdvance H hermitian duration cross current).trace = current.trace := by
  rw [electronicAdvance_joint H hermitian duration cross current close]
  exact Thermal.Quantum.unitary_conjugate_trace current _

theorem electronicAdvance_error_eq (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ)
    (cross realized exactState : Matrix Basis Basis ℂ) (close : ‖cross - 1‖ < 1) :
    ‖electronicAdvance H hermitian duration cross realized - electronicAdvance H hermitian duration cross exactState‖ =
      ‖realized - exactState‖ := by
  rw [electronicAdvance_joint H hermitian duration cross realized close,
    electronicAdvance_joint H hermitian duration cross exactState close, ← map_sub]
  exact StarAlgEquiv.norm_map _ _

theorem electronicAdvance_hermitian (H : Matrix Basis Basis ℂ) (hermitian : H.IsHermitian) (duration : ℝ)
    (cross current : Matrix Basis Basis ℂ) (currentHermitian : current.IsHermitian) :
    (electronicAdvance H hermitian duration cross current).IsHermitian :=
  ElectronicFrame.Polar.transport_hermitian _ _ (Matrix.isHermitian_mul_mul_conjTranspose _ currentHermitian)

end
end LAlanine40K2025.JointNext.Math
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

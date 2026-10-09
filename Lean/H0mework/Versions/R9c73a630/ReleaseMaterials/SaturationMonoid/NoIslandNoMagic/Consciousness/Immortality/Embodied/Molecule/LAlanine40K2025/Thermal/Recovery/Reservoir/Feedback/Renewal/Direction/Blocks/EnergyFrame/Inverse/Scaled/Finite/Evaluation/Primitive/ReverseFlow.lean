import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.ReverseBlock

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open Propagation.Interface Load.Source
open scoped Matrix BigOperators
noncomputable section

theorem small_controller_square : smallControllerSign*smallControllerSign=1 := by
  ext ⟨p,c⟩ ⟨q,d⟩
  fin_cases p <;> fin_cases c <;> fin_cases q <;> fin_cases d <;>
    norm_num [smallControllerSign,controllerSign,Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_succ,
      Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.diagonal_apply,Matrix.one_apply]

private theorem involution_power {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S A : Matrix ι ι ℂ) (square : S*S=1) (n : Nat) : (S*A*S)^n=S*A^n*S := by
  induction n with
  | zero => simp only [pow_zero,Matrix.mul_one,square]
  | succ n ih =>
    rw [pow_succ,ih,pow_succ]
    calc
      _=S*(A^n*(S*S)*A)*S := by noncomm_ring
      _=_ := by rw [square,Matrix.mul_one,Matrix.mul_assoc]

private theorem involution_polynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S A : Matrix ι ι ℂ) (square : S*S=1) (N : Nat) :
    Phase.polynomial (S*A*S) N=S*Phase.polynomial A N*S := by
  simp only [Phase.polynomial,involution_power S A square,Matrix.mul_sum,Matrix.sum_mul,
    Matrix.smul_mul,Matrix.mul_smul]

private theorem involution_flow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S H : Matrix ι ι ℂ) (square : S*S=1) (time : ℝ) :
    Phase.flowPolynomial (S*H*S) time=S*Phase.flowPolynomial H time*S := by
  have argument : time • (-Complex.I • (S*H*S))=S*(time • (-Complex.I • H))*S := by
    simp only [Matrix.mul_smul,Matrix.smul_mul]
  rw [Phase.flowPolynomial,argument,involution_polynomial S _ square]
  rfl

theorem original_reverse_flow (a b : Basis) (distinct : a ≠ b) (time : ℝ) :
    (Phase.flowPolynomial (Actions.reversePCH E) time).submatrix (orbitPC a b) (orbitPC a b)=
      smallControllerSign*sharedOrdinaryPC a b time*smallControllerSign := by
  have kept : Preserves pcOrbit (Actions.reversePCH E) := Contraction.diagonal_reverse_preserves _
  have restricted := original_flow_restriction kept s(a,b) (offDiagonalEquiv a b distinct) time
  have source : ((restrict pcOrbit s(a,b) (Actions.reversePCH E)).submatrix (offDiagonalEquiv a b distinct) (offDiagonalEquiv a b distinct))=
      smallControllerSign*scalarHpc (Donor.calculatedEnergy a) (Donor.calculatedEnergy b)*smallControllerSign :=
    original_reverse_scalar a b distinct
  rw [source,involution_flow _ _ small_controller_square] at restricted
  have same : Phase.flowPolynomial (scalarHpc (Donor.calculatedEnergy a) (Donor.calculatedEnergy b)) time=sharedOrdinaryPC a b time := by
    rw [scalarHpc,← flow_reindex,pc_flow_resolution]
    rfl
  rw [same] at restricted
  exact restricted

theorem original_recovery_pc_shared (a b : Basis) (distinct : a ≠ b) :
    Actions.recoveryPCPolynomial.submatrix (orbitPC a b) (orbitPC a b)=
      smallControllerSign*sharedOrdinaryPC a b (3*(Propagation.Producer.nativeClockStep : ℝ))*smallControllerSign :=
  original_reverse_flow a b distinct _

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

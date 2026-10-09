import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Algebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Hamiltonian
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Pair

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision
open scoped Matrix

theorem qvalue_neg {α β : Type*} (A : MatrixQ α β) : qvalue (-A)=-qvalue A := by
  ext i j
  simp [qvalue,Scalar.value]
  ring

theorem qvalue_sub {α β : Type*} (A B : MatrixQ α β) : qvalue (A-B)=qvalue A-qvalue B := by
  ext i j
  exact scalar_value_sub _ _

theorem qvalue_fourBlocks {α β : Type*} (A : MatrixQ α α) (B : MatrixQ α β) (C : MatrixQ β α) (D : MatrixQ β β) :
    qvalue (Matrix.fromBlocks A B C D)=Matrix.fromBlocks (qvalue A) (qvalue B) (qvalue C) (qvalue D) := by
  ext i j
  rcases i with (i | i) <;> rcases j with (j | j) <;> rfl

def localMatrixQ {α β : Type*} (A : MatrixQ (α × β) (α × β)) (B : MatrixQ α α) : MatrixQ ((α × α) × β) ((α × α) × β) :=
  (qkron A B).submatrix Incidence.bodyReservoir Incidence.bodyReservoir

theorem localMatrixQ_value {α β : Type*} (A : MatrixQ (α × β) (α × β)) (B : MatrixQ α α) :
    qvalue (localMatrixQ A B)=Post.localMatrix (qvalue A) (qvalue B) := by
  rw [localMatrixQ,qvalue_submatrix,qvalue_kron]
  rfl

def swapQ (α : Type*) [DecidableEq α] : MatrixQ (α × α) (α × α) :=
  qreal (fun i j => if (i.2,i.1)=j then 1 else 0)

theorem swapQ_value {α : Type*} [Fintype α] [DecidableEq α] : qvalue (swapQ α)=(swapOperator : JointMatrix α) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  have source := swap_mul_apply (1 : JointMatrix α) i a j b
  rw [Matrix.mul_one] at source
  simp only [Matrix.one_apply] at source
  rw [source]
  by_cases same : (a,i)=(j,b) <;> simp [swapQ,qvalue,qreal,Scalar.value,same]

def partialSwapQ (α : Type*) [Fintype α] [DecidableEq α] (c s : ℚ) : MatrixQ (α × α) (α × α) :=
  qscale (c,0) (qidentity (α × α))+qscale (0,-s) (swapQ α)

theorem partialSwapQ_value {α : Type*} [Fintype α] [DecidableEq α] (c s : ℚ) :
    qvalue (partialSwapQ α c s)=(partialSwap (c : ℝ) (s : ℝ) : JointMatrix α) := by
  rw [partialSwapQ,qvalue_add,qvalue_scale,qvalue_scale,qvalue_identity,swapQ_value]
  ext i j
  simp only [Scalar.value,Rat.cast_zero,Rat.cast_neg,mul_zero,add_zero,zero_add,
    partialSwap,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_ratCast]
  ring

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

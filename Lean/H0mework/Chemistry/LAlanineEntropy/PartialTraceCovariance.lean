import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapReducedState
import H0mework.Quantum.GNS.NormalizedGram
import Mathlib.Data.Matrix.Basis

/-! # Local basis changes commute with both partial traces of the same joint state -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Preparation
open scoped ComplexOrder

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def localUnitary (U V : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup (ι × ι) ℂ :=
  ⟨Matrix.kronecker (U : SystemMatrix ι) (V : SystemMatrix ι), Matrix.kronecker_mem_unitary U.2 V.2⟩

def localConjugation (U V : Matrix.unitaryGroup ι ℂ) : JointMatrix ι →ₗ[ℂ] JointMatrix ι :=
  (Unitary.conjStarAlgAut ℂ (JointMatrix ι) (localUnitary U V)).toAlgEquiv.toLinearMap

def conjugation (U : Matrix.unitaryGroup ι ℂ) : SystemMatrix ι →ₗ[ℂ] SystemMatrix ι :=
  (Unitary.conjStarAlgAut ℂ (SystemMatrix ι) U).toAlgEquiv.toLinearMap

theorem conjugation_apply (U : Matrix.unitaryGroup ι ℂ) (A : SystemMatrix ι) :
    conjugation U A = (U : SystemMatrix ι) * A * star (U : SystemMatrix ι) := rfl

theorem localConjugation_tensor (U V : Matrix.unitaryGroup ι ℂ) (A B : SystemMatrix ι) :
    localConjugation U V (Matrix.kronecker A B) =
      Matrix.kronecker (conjugation U A) (conjugation V B) := by
  change (Matrix.kronecker (U : SystemMatrix ι) (V : SystemMatrix ι)) *
    Matrix.kronecker A B * star (Matrix.kronecker (U : SystemMatrix ι) (V : SystemMatrix ι)) = _
  dsimp only [Matrix.kronecker]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

theorem conjugation_trace (U : Matrix.unitaryGroup ι ℂ) (A : SystemMatrix ι) :
    (conjugation U A).trace = A.trace := unitary_conjugation_trace U A

theorem conjugation_posSemidef (U : Matrix.unitaryGroup ι ℂ) (A : SystemMatrix ι)
    (positive : A.PosSemidef) : (conjugation U A).PosSemidef :=
  positive.mul_mul_conjTranspose_same (U : SystemMatrix ι)

theorem localConjugation_posSemidef (U V : Matrix.unitaryGroup ι ℂ) (joint : JointMatrix ι)
    (positive : joint.PosSemidef) : (localConjugation U V joint).PosSemidef :=
  positive.mul_mul_conjTranspose_same (localUnitary U V : JointMatrix ι)

theorem localConjugation_trace (U V : Matrix.unitaryGroup ι ℂ) (joint : JointMatrix ι) :
    (localConjugation U V joint).trace = joint.trace := unitary_conjugation_trace (localUnitary U V) joint

theorem systemReduce_local_tensor (U V : Matrix.unitaryGroup ι ℂ) (A B : SystemMatrix ι) :
    systemReduce (localConjugation U V (Matrix.kronecker A B)) =
      conjugation U (systemReduce (Matrix.kronecker A B)) := by
  rw [localConjugation_tensor, systemReduce_tensor, systemReduce_tensor,
    conjugation_trace, map_smul]

theorem bathReduce_local_tensor (U V : Matrix.unitaryGroup ι ℂ) (A B : SystemMatrix ι) :
    bathReduce (localConjugation U V (Matrix.kronecker A B)) =
      conjugation V (bathReduce (Matrix.kronecker A B)) := by
  rw [localConjugation_tensor, bathReduce_tensor, bathReduce_tensor,
    conjugation_trace, map_smul]

omit [Fintype ι] in
private theorem joint_single_tensor (i j a b : ι) (value : ℂ) :
    Matrix.single (i, a) (j, b) value =
      Matrix.kronecker (Matrix.single i j value) (Matrix.single a b 1) := by
  exact (Matrix.single_kronecker_single i j a b value (1 : ℂ)).trans
    (by rw [mul_one]) |>.symm

theorem systemReduce_local_conjugation (U V : Matrix.unitaryGroup ι ℂ) (joint : JointMatrix ι) :
    systemReduce (localConjugation U V joint) = conjugation U (systemReduce joint) := by
  rw [Matrix.matrix_eq_sum_single joint]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i, a⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨j, b⟩ _
  rw [joint_single_tensor]
  exact systemReduce_local_tensor U V _ _

theorem bathReduce_local_conjugation (U V : Matrix.unitaryGroup ι ℂ) (joint : JointMatrix ι) :
    bathReduce (localConjugation U V joint) = conjugation V (bathReduce joint) := by
  rw [Matrix.matrix_eq_sum_single joint]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i, a⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨j, b⟩ _
  rw [joint_single_tensor]
  exact bathReduce_local_tensor U V _ _

end

end LAlanine40K2025.Thermal.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Chemistry.LAlanineThermalDynamics.UnequalPartialTrace
import H0mework.Chemistry.LAlanineEntropy.PartialTraceCovariance

/-! # Local basis changes on one joint state with unequal subsystem dimensions

The two reduced states remain restrictions of the same joint matrix. These
transport identities feed its marginal eigenbasis entropy measurement.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Quantum

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped ComplexOrder

noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The local unitaries act on their original subsystem carriers. -/
def localUnitary (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    Matrix.unitaryGroup (ι × κ) ℂ :=
  ⟨Matrix.kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ),
    Matrix.kronecker_mem_unitary U.2 V.2⟩

def localConjugation (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix (ι × κ) (ι × κ) ℂ :=
  conjugation (localUnitary U V)

theorem localConjugation_tensor (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    localConjugation U V (Matrix.kronecker A B) =
      Matrix.kronecker (conjugation U A) (conjugation V B) := by
  change (Matrix.kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)) *
    Matrix.kronecker A B * star (Matrix.kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ)) = _
  dsimp only [Matrix.kronecker]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

theorem localConjugation_posSemidef (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (joint : Matrix (ι × κ) (ι × κ) ℂ)
    (positive : joint.PosSemidef) : (localConjugation U V joint).PosSemidef :=
  conjugation_posSemidef (localUnitary U V) joint positive

theorem localConjugation_trace (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ)
    (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    (localConjugation U V joint).trace = joint.trace :=
  conjugation_trace (localUnitary U V) joint

private theorem systemReduce_local_tensor (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    systemReduce (localConjugation U V (Matrix.kronecker A B)) =
      conjugation U (systemReduce (Matrix.kronecker A B)) := by
  rw [localConjugation_tensor, systemReduce_tensor, systemReduce_tensor,
    conjugation_trace, map_smul]

private theorem controllerReduce_local_tensor (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    controllerReduce (localConjugation U V (Matrix.kronecker A B)) =
      conjugation V (controllerReduce (Matrix.kronecker A B)) := by
  rw [localConjugation_tensor, controllerReduce_tensor, controllerReduce_tensor,
    conjugation_trace, map_smul]

omit [Fintype ι] [Fintype κ] in
private theorem joint_single_tensor (i j : ι) (a b : κ) (value : ℂ) :
    Matrix.single (i, a) (j, b) value =
      Matrix.kronecker (Matrix.single i j value) (Matrix.single a b 1) := by
  exact (Matrix.single_kronecker_single i j a b value (1 : ℂ)).trans
    (by rw [mul_one]) |>.symm

/-- The first marginal of the rotated joint is the rotated first marginal. -/
theorem systemReduce_local_conjugation (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    systemReduce (localConjugation U V joint) = conjugation U (systemReduce joint) := by
  rw [Matrix.matrix_eq_sum_single joint]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i, a⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨j, b⟩ _
  rw [joint_single_tensor]
  exact systemReduce_local_tensor U V _ _

/-- The second marginal of the rotated joint is the rotated second marginal. -/
theorem controllerReduce_local_conjugation (U : Matrix.unitaryGroup ι ℂ)
    (V : Matrix.unitaryGroup κ ℂ) (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    controllerReduce (localConjugation U V joint) = conjugation V (controllerReduce joint) := by
  rw [Matrix.matrix_eq_sum_single joint]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  rintro ⟨i, a⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨j, b⟩ _
  rw [joint_single_tensor]
  exact controllerReduce_local_tensor U V _ _

end

end LAlanine40K2025.Thermal.Load.Quantum
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Actual finite partial-swap collision

The swap is a source permutation, and the joint next is its partial-swap
unitary conjugation of the two input matrices. No reduced-state equation or
target state is supplied to this construction.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Collision

open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

abbrev SystemMatrix (ι : Type*) := Matrix ι ι ℂ
abbrev JointMatrix (ι : Type*) := Matrix (ι × ι) (ι × ι) ℂ

def swapOperator : JointMatrix ι :=
  Equiv.Perm.permMatrix ℂ (Equiv.prodComm ι ι)

omit [Fintype ι] in
theorem swap_adjoint : (swapOperator (ι := ι))ᴴ = swapOperator := by
  unfold swapOperator
  rw [Matrix.conjTranspose_permMatrix]
  rfl

theorem swap_squared : (swapOperator (ι := ι)) * swapOperator = 1 := by
  unfold swapOperator
  rw [← Matrix.permMatrix_mul]
  have twice : (Equiv.prodComm ι ι) * (Equiv.prodComm ι ι) = (1 : Equiv.Perm (ι × ι)) := by
    ext pair <;> rfl
  rw [twice, Matrix.permMatrix_one]

theorem swap_mul_apply (matrix : JointMatrix ι) (i a j b : ι) :
    ((swapOperator : JointMatrix ι) * matrix) (i, a) (j, b) = matrix (a, i) (j, b) := by
  change (((Equiv.prodComm ι ι).toPEquiv.toMatrix : JointMatrix ι) * matrix) (i, a) (j, b) = _
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rfl

theorem mul_swap_apply (matrix : JointMatrix ι) (i a j b : ι) :
    (matrix * (swapOperator : JointMatrix ι)) (i, a) (j, b) = matrix (i, a) (b, j) := by
  change (matrix * ((Equiv.prodComm ι ι).toPEquiv.toMatrix : JointMatrix ι)) (i, a) (j, b) = _
  rw [PEquiv.mul_toMatrix_toPEquiv]
  rfl

theorem swap_kronecker_swap (rho tau : SystemMatrix ι) :
    swapOperator * Matrix.kronecker rho tau * swapOperator = Matrix.kronecker tau rho := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [mul_swap_apply, swap_mul_apply]
  simp [Matrix.kronecker, mul_comm]

/-- The physical coupling parameters are the real cosine/sine coordinates. -/
def partialSwap (c s : ℝ) : JointMatrix ι :=
  (c : ℂ) • 1 - (Complex.I * (s : ℂ)) • swapOperator

omit [Fintype ι] in
theorem partialSwap_adjoint (c s : ℝ) :
    (partialSwap (ι := ι) c s)ᴴ = (c : ℂ) • 1 + (Complex.I * (s : ℂ)) • swapOperator := by
  simp [partialSwap, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, swap_adjoint]

private theorem partialSwap_products (c s : ℝ) :
    (partialSwap (ι := ι) c s) * (partialSwap c s)ᴴ =
      (((c : ℂ) ^ 2 + (s : ℂ) ^ 2) • (1 : JointMatrix ι)) ∧
    (partialSwap (ι := ι) c s)ᴴ * partialSwap c s =
      (((c : ℂ) ^ 2 + (s : ℂ) ^ 2) • (1 : JointMatrix ι)) := by
  constructor
  all_goals
    rw [partialSwap_adjoint]
    simp only [partialSwap, sub_mul, mul_add, add_mul, mul_sub,
      smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one, swap_squared]
    ext row column
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring_nf
    simp [Complex.I_sq]

theorem partialSwap_unitary (c s : ℝ) (circle : c ^ 2 + s ^ 2 = 1) :
    partialSwap (ι := ι) c s ∈ unitary (JointMatrix ι) := by
  have complexCircle : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast circle
  have products := partialSwap_products (ι := ι) c s
  rw [complexCircle, one_smul] at products
  exact ⟨products.2, products.1⟩

def jointNext (rho tau : SystemMatrix ι) (c s : ℝ) : JointMatrix ι :=
  partialSwap c s * Matrix.kronecker rho tau * (partialSwap c s)ᴴ

/-- Full joint expansion; the cross term is retained before either partial trace. -/
theorem jointNext_expansion (rho tau : SystemMatrix ι) (c s : ℝ) :
    jointNext rho tau c s =
      ((c : ℂ) ^ 2) • Matrix.kronecker rho tau +
      ((s : ℂ) ^ 2) • Matrix.kronecker tau rho +
      (Complex.I * (c : ℂ) * (s : ℂ)) •
        (Matrix.kronecker rho tau * swapOperator - swapOperator * Matrix.kronecker rho tau) := by
  unfold jointNext
  rw [partialSwap_adjoint]
  simp only [partialSwap, sub_mul, mul_add,
    smul_mul_assoc, mul_smul_comm, Matrix.one_mul, Matrix.mul_one]
  rw [swap_kronecker_swap]
  ext row column
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

theorem jointNext_trace (rho tau : SystemMatrix ι) (c s : ℝ)
    (circle : c ^ 2 + s ^ 2 = 1) :
    Matrix.trace (jointNext rho tau c s) = Matrix.trace rho * Matrix.trace tau := by
  unfold jointNext
  rw [Matrix.trace_mul_cycle]
  have inverse := (partialSwap_unitary (ι := ι) c s circle).1
  change (partialSwap c s)ᴴ * partialSwap c s = 1 at inverse
  rw [inverse, Matrix.one_mul]
  exact Matrix.trace_kronecker rho tau

end

end LAlanine40K2025.Thermal.Collision
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

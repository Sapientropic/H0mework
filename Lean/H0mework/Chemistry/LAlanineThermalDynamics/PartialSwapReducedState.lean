import H0mework.Chemistry.LAlanineThermalDynamics.PartialSwapUnitary
import Mathlib.Analysis.Matrix.Order

/-!
# Both reduced targets of the actual joint collision

Partial traces are finite entry contractions of the joint target. Their
closed forms retain opposite commutator terms; population mixing is not
assumed and coherence is not deleted.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Collision

open scoped Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

def systemReduce : JointMatrix ι →ₗ[ℂ] SystemMatrix ι where
  toFun matrix i j := ∑ a : ι, matrix (i, a) (j, a)
  map_add' := by
    intro left right
    ext i j
    change (∑ a : ι, (left (i, a) (j, a) + right (i, a) (j, a))) = _
    exact Finset.sum_add_distrib
  map_smul' := by
    intro scalar matrix
    ext i j
    change (∑ a : ι, scalar * matrix (i, a) (j, a)) = scalar * ∑ a : ι, matrix (i, a) (j, a)
    rw [Finset.mul_sum]

def bathReduce : JointMatrix ι →ₗ[ℂ] SystemMatrix ι where
  toFun matrix a b := ∑ i : ι, matrix (i, a) (i, b)
  map_add' := by
    intro left right
    ext a b
    change (∑ i : ι, (left (i, a) (i, b) + right (i, a) (i, b))) = _
    exact Finset.sum_add_distrib
  map_smul' := by
    intro scalar matrix
    ext a b
    change (∑ i : ι, scalar * matrix (i, a) (i, b)) = scalar * ∑ i : ι, matrix (i, a) (i, b)
    rw [Finset.mul_sum]

omit [DecidableEq ι] in
theorem systemReduce_tensor (rho tau : SystemMatrix ι) :
    systemReduce (Matrix.kronecker rho tau) = Matrix.trace tau • rho := by
  ext i j
  change (∑ a : ι, rho i j * tau a a) = (∑ a : ι, tau a a) * rho i j
  rw [← Finset.mul_sum, mul_comm]

omit [DecidableEq ι] in
theorem bathReduce_tensor (rho tau : SystemMatrix ι) :
    bathReduce (Matrix.kronecker rho tau) = Matrix.trace rho • tau := by
  ext a b
  change (∑ i : ι, rho i i * tau a b) = (∑ i : ι, rho i i) * tau a b
  rw [← Finset.sum_mul]

theorem systemReduce_tensor_swap (rho tau : SystemMatrix ι) :
    systemReduce (Matrix.kronecker rho tau * swapOperator) = rho * tau := by
  ext i j
  change (∑ a : ι, ((Matrix.kronecker rho tau * swapOperator) : JointMatrix ι) (i, a) (j, a)) =
    ∑ a : ι, rho i a * tau a j
  apply Finset.sum_congr rfl
  intro a _membership
  rw [mul_swap_apply]
  rfl

theorem systemReduce_swap_tensor (rho tau : SystemMatrix ι) :
    systemReduce (swapOperator * Matrix.kronecker rho tau) = tau * rho := by
  ext i j
  change (∑ a : ι, ((swapOperator * Matrix.kronecker rho tau) : JointMatrix ι) (i, a) (j, a)) =
    ∑ a : ι, tau i a * rho a j
  apply Finset.sum_congr rfl
  intro a _membership
  rw [swap_mul_apply]
  exact mul_comm _ _

theorem bathReduce_tensor_swap (rho tau : SystemMatrix ι) :
    bathReduce (Matrix.kronecker rho tau * swapOperator) = tau * rho := by
  ext a b
  change (∑ i : ι, ((Matrix.kronecker rho tau * swapOperator) : JointMatrix ι) (i, a) (i, b)) =
    ∑ i : ι, tau a i * rho i b
  apply Finset.sum_congr rfl
  intro i _membership
  rw [mul_swap_apply]
  exact mul_comm _ _

theorem bathReduce_swap_tensor (rho tau : SystemMatrix ι) :
    bathReduce (swapOperator * Matrix.kronecker rho tau) = rho * tau := by
  ext a b
  change (∑ i : ι, ((swapOperator * Matrix.kronecker rho tau) : JointMatrix ι) (i, a) (i, b)) =
    ∑ i : ι, rho a i * tau i b
  apply Finset.sum_congr rfl
  intro i _membership
  rw [swap_mul_apply]
  rfl

def systemNext (rho tau : SystemMatrix ι) (c s : ℝ) : SystemMatrix ι :=
  systemReduce (jointNext rho tau c s)

def bathNext (rho tau : SystemMatrix ι) (c s : ℝ) : SystemMatrix ι :=
  bathReduce (jointNext rho tau c s)

theorem systemNext_full (rho tau : SystemMatrix ι) (c s : ℝ) :
    systemNext rho tau c s =
      ((c : ℂ) ^ 2) • (Matrix.trace tau • rho) +
      ((s : ℂ) ^ 2) • (Matrix.trace rho • tau) +
      (Complex.I * (c : ℂ) * (s : ℂ)) • (rho * tau - tau * rho) := by
  simp only [systemNext, jointNext_expansion, map_add, map_smul, map_sub,
    systemReduce_tensor, systemReduce_tensor_swap, systemReduce_swap_tensor]

theorem bathNext_full (rho tau : SystemMatrix ι) (c s : ℝ) :
    bathNext rho tau c s =
      ((c : ℂ) ^ 2) • (Matrix.trace rho • tau) +
      ((s : ℂ) ^ 2) • (Matrix.trace tau • rho) +
      (Complex.I * (c : ℂ) * (s : ℂ)) • (tau * rho - rho * tau) := by
  simp only [bathNext, jointNext_expansion, map_add, map_smul, map_sub,
    bathReduce_tensor, bathReduce_tensor_swap, bathReduce_swap_tensor]

theorem systemNext_eq (rho tau : SystemMatrix ι) (c s : ℝ)
    (rhoTrace : Matrix.trace rho = 1) (tauTrace : Matrix.trace tau = 1) :
    systemNext rho tau c s = ((c : ℂ) ^ 2) • rho + ((s : ℂ) ^ 2) • tau +
      (Complex.I * (c : ℂ) * (s : ℂ)) • (rho * tau - tau * rho) := by
  rw [systemNext_full, rhoTrace, tauTrace, one_smul, one_smul]

theorem bathNext_eq (rho tau : SystemMatrix ι) (c s : ℝ)
    (rhoTrace : Matrix.trace rho = 1) (tauTrace : Matrix.trace tau = 1) :
    bathNext rho tau c s = ((c : ℂ) ^ 2) • tau + ((s : ℂ) ^ 2) • rho +
      (Complex.I * (c : ℂ) * (s : ℂ)) • (tau * rho - rho * tau) := by
  rw [bathNext_full, rhoTrace, tauTrace, one_smul, one_smul]

omit [DecidableEq ι] in
theorem systemReduce_trace (matrix : JointMatrix ι) :
    Matrix.trace (systemReduce matrix) = Matrix.trace matrix := by
  change (∑ i : ι, ∑ a : ι, matrix (i, a) (i, a)) = ∑ pair : ι × ι, matrix pair pair
  rw [Fintype.sum_prod_type]

omit [DecidableEq ι] in
theorem bathReduce_trace (matrix : JointMatrix ι) :
    Matrix.trace (bathReduce matrix) = Matrix.trace matrix := by
  change (∑ a : ι, ∑ i : ι, matrix (i, a) (i, a)) = ∑ pair : ι × ι, matrix pair pair
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem reduced_traces (rho tau : SystemMatrix ι) (c s : ℝ)
    (circle : c ^ 2 + s ^ 2 = 1) (rhoTrace : Matrix.trace rho = 1)
    (tauTrace : Matrix.trace tau = 1) :
    Matrix.trace (systemNext rho tau c s) = 1 ∧ Matrix.trace (bathNext rho tau c s) = 1 := by
  simp only [systemNext, bathNext, systemReduce_trace, bathReduce_trace,
    jointNext_trace rho tau c s circle, rhoTrace, tauTrace, mul_one, and_self]

theorem jointNext_posSemidef (rho tau : SystemMatrix ι) (c s : ℝ)
    (rhoPositive : rho.PosSemidef) (tauPositive : tau.PosSemidef) :
    (jointNext rho tau c s).PosSemidef :=
  (rhoPositive.kronecker tauPositive).mul_mul_conjTranspose_same (partialSwap c s)

omit [DecidableEq ι] in
theorem systemReduce_posSemidef (matrix : JointMatrix ι) (positive : matrix.PosSemidef) :
    (systemReduce matrix).PosSemidef := by
  have sumForm : systemReduce matrix =
      ∑ a : ι, matrix.submatrix (fun i => (i, a)) (fun j => (j, a)) := by
    ext i j
    simp [systemReduce, Matrix.sum_apply]
    rfl
  rw [sumForm]
  exact Matrix.posSemidef_sum Finset.univ fun a _ => positive.submatrix (fun i => (i, a))

omit [DecidableEq ι] in
theorem bathReduce_posSemidef (matrix : JointMatrix ι) (positive : matrix.PosSemidef) :
    (bathReduce matrix).PosSemidef := by
  have sumForm : bathReduce matrix =
      ∑ i : ι, matrix.submatrix (fun a => (i, a)) (fun b => (i, b)) := by
    ext a b
    simp [bathReduce, Matrix.sum_apply]
    rfl
  rw [sumForm]
  exact Matrix.posSemidef_sum Finset.univ fun i _ => positive.submatrix (fun a => (i, a))

theorem reduced_posSemidef (rho tau : SystemMatrix ι) (c s : ℝ)
    (rhoPositive : rho.PosSemidef) (tauPositive : tau.PosSemidef) :
    (systemNext rho tau c s).PosSemidef ∧ (bathNext rho tau c s).PosSemidef :=
  ⟨systemReduce_posSemidef _ (jointNext_posSemidef rho tau c s rhoPositive tauPositive),
    bathReduce_posSemidef _ (jointNext_posSemidef rho tau c s rhoPositive tauPositive)⟩

end

end LAlanine40K2025.Thermal.Collision
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

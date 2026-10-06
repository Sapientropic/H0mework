import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceQuantumFockGauge
import Mathlib.Tactic

/-! Full occupation-space CAR contractions, without a particle cutoff. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceCARBound
open SaturationMonoid.PhysicsCore
open SaturationMonoid.PhysicsCore.LowEnergy
open QuantizationCheck.Fermion SourceQuantumFockGauge
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

def liftOp (T : Module.End ℂ (Fock ι)) : Module.End ℂ (Fiber (ι := ι)) :=
  fiberCoordinates.symm.toLinearMap.comp (T.comp fiberCoordinates.toLinearMap)

omit [Fintype ι] [LinearOrder ι] in
@[simp] theorem coordinates_liftOp (T : Module.End ℂ (Fock ι)) (psi : Fiber (ι := ι)) :
    fiberCoordinates (liftOp T psi) = T (fiberCoordinates psi) := by
  simp [liftOp]

def createOp (i : ι) := liftOp (Fermion.creation i)
def annihilateOp (i : ι) := liftOp (Fermion.annihilation i)

theorem create_adjoint (i : ι) (psi phi : Fiber (ι := ι)) :
    inner ℂ (createOp i psi) phi = inner ℂ psi (annihilateOp i phi) := by
  simp only [fiber_pairing, createOp, annihilateOp, coordinates_liftOp,
    Fermion.creation_apply, Fermion.annihilation_apply]
  exact pairing_create_annihilate i _ _

theorem annihilate_adjoint (i : ι) (psi phi : Fiber (ι := ι)) :
    inner ℂ (annihilateOp i psi) phi = inner ℂ psi (createOp i phi) := by
  simp only [fiber_pairing, createOp, annihilateOp, coordinates_liftOp,
    Fermion.creation_apply, Fermion.annihilation_apply]
  exact pairing_annihilate_create i _ _

omit [Fintype ι] in
theorem car_same (i : ι) (psi : Fiber (ι := ι)) :
    annihilateOp i (createOp i psi) + createOp i (annihilateOp i psi) = psi := by
  apply fiberCoordinates.injective
  simp only [map_add, createOp, annihilateOp, coordinates_liftOp,
    Fermion.creation_apply, Fermion.annihilation_apply]
  simpa using Fermion.annihilate_create_car i i (fiberCoordinates psi)

theorem norm_partition (i : ι) (psi : Fiber (ι := ι)) :
    ‖createOp i psi‖ ^ 2 + ‖annihilateOp i psi‖ ^ 2 = ‖psi‖ ^ 2 := by
  have h : inner ℂ (createOp i psi) (createOp i psi) +
      inner ℂ (annihilateOp i psi) (annihilateOp i psi) = inner ℂ psi psi := by
    rw [create_adjoint, annihilate_adjoint, ← inner_add_right, car_same]
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

theorem create_norm_le (i : ι) (psi : Fiber (ι := ι)) : ‖createOp i psi‖ ≤ ‖psi‖ := by
  have h := norm_partition i psi
  nlinarith [sq_nonneg ‖annihilateOp i psi‖, norm_nonneg psi, norm_nonneg (createOp i psi)]

theorem annihilate_norm_le (i : ι) (psi : Fiber (ι := ι)) : ‖annihilateOp i psi‖ ≤ ‖psi‖ := by
  have h := norm_partition i psi
  nlinarith [sq_nonneg ‖createOp i psi‖, norm_nonneg psi, norm_nonneg (annihilateOp i psi)]

theorem matrix_unit_norm_le (i j : ι) (psi : Fiber (ι := ι)) :
    ‖createOp i (annihilateOp j psi)‖ ≤ ‖psi‖ :=
  (create_norm_le i _).trans (annihilate_norm_le j psi)

theorem quantized_expansion (A : Matrix ι ι ℂ) (psi : Fiber (ι := ι)) :
    quantizedFiber A psi = ∑ i, ∑ j, A i j • createOp i (annihilateOp j psi) := by
  apply fiberCoordinates.injective
  simp only [quantizedFiber, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, map_sum, map_smul, createOp, annihilateOp,
    coordinates_liftOp, Fermion.quantize, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply]

theorem quantized_norm_le_sum (A : Matrix ι ι ℂ) (psi : Fiber (ι := ι)) :
    ‖quantizedFiber A psi‖ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖psi‖ := by
  rw [quantized_expansion, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (matrix_unit_norm_le i j psi) (norm_nonneg _)

theorem quantized_norm_sq_le_support (A : Matrix ι ι ℂ) (support : Finset (ι × ι))
    (covered : ∀ i j, (i, j) ∉ support → A i j = 0) (psi : Fiber (ι := ι)) :
    ‖quantizedFiber A psi‖ ^ 2 ≤
      support.card * (∑ p ∈ support, ‖A p.1 p.2‖ ^ 2) * ‖psi‖ ^ 2 := by
  have hsum : (∑ i, ∑ j, ‖A i j‖) = ∑ p ∈ support, ‖A p.1 p.2‖ := by
    have h := Finset.sum_subset (Finset.subset_univ support)
      (f := fun p : ι × ι => ‖A p.1 p.2‖)
      (by intro p _ hp; simp [covered p.1 p.2 hp])
    simpa only [← Finset.univ_product_univ, Finset.sum_product] using h.symm
  have hbound := quantized_norm_le_sum A psi
  rw [hsum] at hbound
  have hnonnegative : 0 ≤ ∑ p ∈ support, ‖A p.1 p.2‖ :=
    Finset.sum_nonneg (fun p _ => norm_nonneg (A p.1 p.2))
  have hsquare := (sq_le_sq₀ (norm_nonneg (quantizedFiber A psi))
    (mul_nonneg hnonnegative (norm_nonneg psi))).mpr hbound
  have cauchy := Finset.sum_mul_sq_le_sq_mul_sq support
    (fun _ => (1 : ℝ)) (fun p => ‖A p.1 p.2‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at cauchy
  calc
    ‖quantizedFiber A psi‖ ^ 2 ≤ (∑ p ∈ support, ‖A p.1 p.2‖) ^ 2 * ‖psi‖ ^ 2 := by
      simpa only [mul_pow] using hsquare
    _ ≤ _ := mul_le_mul_of_nonneg_right cauchy (sq_nonneg _)

#print axioms matrix_unit_norm_le
#print axioms quantized_norm_le_sum
#print axioms quantized_norm_sq_le_support
end LowEnergy.SourceCARBound

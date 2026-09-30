import H0mework.Chemistry.LAlanineEntropy.JointEnergyReadout

/-! # Both unequal-dimensional marginals are read from the same full joint -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Dynamics

open scoped Matrix ComplexOrder

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable section

def systemReduce : Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun matrix i j := ∑ a : κ, matrix (i, a) (j, a)
  map_add' := by
    intro left right
    ext i j
    exact Finset.sum_add_distrib
  map_smul' := by
    intro scalar matrix
    ext i j
    exact (Finset.mul_sum _ _ _).symm

def controllerReduce : Matrix (ι × κ) (ι × κ) ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun matrix a b := ∑ i : ι, matrix (i, a) (i, b)
  map_add' := by
    intro left right
    ext a b
    exact Finset.sum_add_distrib
  map_smul' := by
    intro scalar matrix
    ext a b
    exact (Finset.mul_sum _ _ _).symm

omit [Fintype ι] in
theorem systemReduce_tensor (rho : Matrix ι ι ℂ) (tau : Matrix κ κ ℂ) :
    systemReduce (Matrix.kronecker rho tau) = tau.trace • rho := by
  ext i j
  change (∑ a : κ, rho i j * tau a a) = (∑ a : κ, tau a a) * rho i j
  rw [← Finset.mul_sum, mul_comm]

omit [Fintype κ] in
theorem controllerReduce_tensor (rho : Matrix ι ι ℂ) (tau : Matrix κ κ ℂ) :
    controllerReduce (Matrix.kronecker rho tau) = rho.trace • tau := by
  ext a b
  change (∑ i : ι, rho i i * tau a b) = (∑ i : ι, rho i i) * tau a b
  rw [← Finset.sum_mul]

theorem systemReduce_trace (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    (systemReduce joint).trace = joint.trace := by
  change (∑ i : ι, ∑ a : κ, joint (i, a) (i, a)) = ∑ ia : ι × κ, joint ia ia
  rw [Fintype.sum_prod_type]

theorem controllerReduce_trace (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    (controllerReduce joint).trace = joint.trace := by
  change (∑ a : κ, ∑ i : ι, joint (i, a) (i, a)) = ∑ ia : ι × κ, joint ia ia
  rw [Fintype.sum_prod_type, Finset.sum_comm]

omit [Fintype ι] in
theorem systemReduce_posSemidef (joint : Matrix (ι × κ) (ι × κ) ℂ)
    (positive : joint.PosSemidef) : (systemReduce joint).PosSemidef := by
  have sumForm : systemReduce joint =
      ∑ a : κ, joint.submatrix (fun i => (i, a)) (fun j => (j, a)) := by
    ext i j
    simp [systemReduce, Matrix.sum_apply]
    rfl
  rw [sumForm]
  exact Matrix.posSemidef_sum Finset.univ fun a _ => positive.submatrix (fun i => (i, a))

omit [Fintype κ] in
theorem controllerReduce_posSemidef (joint : Matrix (ι × κ) (ι × κ) ℂ)
    (positive : joint.PosSemidef) : (controllerReduce joint).PosSemidef := by
  have sumForm : controllerReduce joint =
      ∑ i : ι, joint.submatrix (fun a => (i, a)) (fun b => (i, b)) := by
    ext a b
    simp [controllerReduce, Matrix.sum_apply]
    rfl
  rw [sumForm]
  exact Matrix.posSemidef_sum Finset.univ fun i _ => positive.submatrix (fun a => (i, a))

variable [DecidableEq ι] [DecidableEq κ]

private theorem tensor_energy_read (H A : Matrix ι ι ℂ) (K B : Matrix κ κ ℂ) :
    ((Matrix.kronecker H 1 + Matrix.kronecker 1 K) * Matrix.kronecker A B).trace =
      (H * systemReduce (Matrix.kronecker A B)).trace +
        (K * controllerReduce (Matrix.kronecker A B)).trace := by
  simp only [Matrix.add_mul, Matrix.trace_add, systemReduce_tensor, controllerReduce_tensor,
    mul_smul_comm, Matrix.trace_smul]
  dsimp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.one_mul, Matrix.trace_kronecker, Matrix.trace_kronecker]
  simp only [smul_eq_mul]
  ring

theorem jointEnergy_eq_reduced (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    ((Matrix.kronecker H 1 + Matrix.kronecker 1 K) * joint).trace =
      (H * systemReduce joint).trace + (K * controllerReduce joint).trace := by
  rw [Matrix.matrix_eq_sum_single joint]
  simp only [Matrix.mul_sum, Matrix.trace_sum, map_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  rintro ⟨i, a⟩ _
  apply Finset.sum_congr rfl
  rintro ⟨j, b⟩ _
  have tensor : Matrix.single (i, a) (j, b) (joint (i, a) (j, b)) =
      Matrix.kronecker (Matrix.single i j (joint (i, a) (j, b))) (Matrix.single a b 1) :=
    (Matrix.single_kronecker_single i j a b (joint (i, a) (j, b)) (1 : ℂ)).trans
      (by rw [mul_one]) |>.symm
  rw [tensor]
  exact tensor_energy_read H _ K _

theorem jointEnergy_real_eq_reduced (H : Matrix ι ι ℂ) (K : Matrix κ κ ℂ)
    (joint : Matrix (ι × κ) (ι × κ) ℂ) :
    Collision.energy (Matrix.kronecker H 1 + Matrix.kronecker 1 K) joint =
      Collision.energy H (systemReduce joint) + Collision.energy K (controllerReduce joint) := by
  unfold Collision.energy
  rw [jointEnergy_eq_reduced, Complex.add_re]

end

end LAlanine40K2025.Thermal.Powered.Dynamics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

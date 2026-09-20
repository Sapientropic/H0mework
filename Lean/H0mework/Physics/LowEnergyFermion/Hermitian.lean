import H0mework.Physics.LowEnergyFermion.MatrixElement
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-! The original real bilinear source is quantized through its Hermitian part. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open scoped BigOperators Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]

theorem modePair_add_right (u v w : ι → ℂ) :
    modePair u (v+w) = modePair u v+modePair u w := by
  simp [modePair, mul_add, Finset.sum_add_distrib]

theorem modePair_smul_right (c : ℂ) (u v : ι → ℂ) :
    modePair u (c • v) = c * modePair u v := by
  simp only [modePair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem modePair_conjTranspose (A : Matrix ι ι ℂ) (u v : ι → ℂ) :
    modePair u (A.conjTranspose *ᵥ v) = star (modePair v (A *ᵥ u)) := by
  simp only [modePair, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    star_sum, star_mul, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def hermitianPart (A : Matrix ι ι ℂ) : Matrix ι ι ℂ := (1/2 : ℂ) • (A+A.conjTranspose)

omit [Fintype ι] in
theorem hermitianPart_adjoint (A : Matrix ι ι ℂ) :
    (hermitianPart A).conjTranspose = hermitianPart A := by
  simp [hermitianPart, Matrix.conjTranspose_smul, add_comm]

theorem hermitianPart_self (A : Matrix ι ι ℂ) (u : ι → ℂ) :
    modePair u (hermitianPart A *ᵥ u) = ((modePair u (A *ᵥ u)).re : ℂ) := by
  rw [hermitianPart, Matrix.smul_mulVec, modePair_smul_right,
    Matrix.add_mulVec, modePair_add_right, modePair_conjTranspose]
  rw [Complex.re_eq_add_conj]
  simp only [starRingEnd_apply]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion

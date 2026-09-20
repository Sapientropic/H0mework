import H0mework.Physics.QuantumDynamics.Phase
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! The physical phase action uses Mathlib's complete unitary-induced
star-algebra automorphism, including its inverse on the same observable algebra. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField Source

noncomputable section

def automorphism (displacement : BasePoint) :
    Matrix Index Index ℂ ≃⋆ₐ[ℂ] Matrix Index Index ℂ :=
  Unitary.conjStarAlgAut ℂ (Matrix Index Index ℂ) (unitary displacement)

theorem automorphism_apply (displacement : BasePoint) (observable : Matrix Index Index ℂ) :
    automorphism displacement observable =
      (unitary displacement : Matrix Index Index ℂ) * observable *
        star (unitary displacement : Matrix Index Index ℂ) := rfl

theorem automorphism_mul (displacement : BasePoint) (first second : Matrix Index Index ℂ) :
    automorphism displacement (first * second) =
      automorphism displacement first * automorphism displacement second :=
  map_mul (automorphism displacement) first second

theorem automorphism_star (displacement : BasePoint) (observable : Matrix Index Index ℂ) :
    automorphism displacement (star observable) = star (automorphism displacement observable) :=
  map_star (automorphism displacement) observable

theorem automorphism_one (displacement : BasePoint) :
    automorphism displacement 1 = 1 := map_one (automorphism displacement)

theorem unitary_neg (displacement : BasePoint) :
    unitary (-displacement) = star (unitary displacement) := by
  rw [Unitary.star_eq_inv]
  apply eq_inv_iff_mul_eq_one.mpr
  rw [← unitary_add, neg_add_cancel, unitary_zero]

theorem automorphism_neg (displacement : BasePoint) :
    automorphism (-displacement) = (automorphism displacement).symm := by
  rw [automorphism, unitary_neg, ← Unitary.conjStarAlgAut_symm]
  rfl

theorem automorphism_inverse (displacement : BasePoint) (observable : Matrix Index Index ℂ) :
    automorphism (-displacement) (automorphism displacement observable) = observable := by
  rw [automorphism_neg]
  exact (automorphism displacement).symm_apply_apply observable

theorem automorphism_two_step (first second : BasePoint) (observable : Matrix Index Index ℂ) :
    automorphism first (automorphism second observable) =
      automorphism (first + second) observable := by
  simp only [automorphism, unitary_add, Unitary.conjStarAlgAut_mul_apply]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Dynamics

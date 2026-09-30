import H0mework.Physics.LowEnergy.BosonEffective.Schur

/-! Auxiliary-first and matter-first block inversions generate the same joint
inverse. This keeps the changed matter block after the Lorentz elimination. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective
noncomputable section
variable {a m b : Type*} [Fintype a] [Fintype m] [Fintype b]
variable [DecidableEq a] [DecidableEq m] [DecidableEq b]
variable (A : Matrix a a ℂ) (B : Matrix a m ℂ) (C : Matrix m a ℂ) (D : Matrix m m ℂ)
variable [Invertible A] [Invertible D] [Invertible (D-C*⅟A*B)] [Invertible (A-B*⅟D*C)]

def auxiliaryFirst : Matrix (a ⊕ m) (a ⊕ m) ℂ :=
  Matrix.fromBlocks (⅟A+⅟A*B*⅟(D-C*⅟A*B)*C*⅟A) (-(⅟A*B*⅟(D-C*⅟A*B)))
    (-(⅟(D-C*⅟A*B)*C*⅟A)) (⅟(D-C*⅟A*B))

def matterFirst : Matrix (a ⊕ m) (a ⊕ m) ℂ :=
  Matrix.fromBlocks (⅟(A-B*⅟D*C)) (-(⅟(A-B*⅟D*C)*B*⅟D))
    (-(⅟D*C*⅟(A-B*⅟D*C))) (⅟D+⅟D*C*⅟(A-B*⅟D*C)*B*⅟D)

omit [Fintype b] [DecidableEq b] in
theorem elimination_order : auxiliaryFirst A B C D=matterFirst A B C D := by
  let _ := Matrix.fromBlocks₁₁Invertible A B C D
  rw [auxiliaryFirst,matterFirst,← Matrix.invOf_fromBlocks₁₁_eq,← Matrix.invOf_fromBlocks₂₂_eq]

omit [Fintype b] [DecidableEq b] [Invertible D] [Invertible (A-B*⅟D*C)] in
theorem auxiliaryFirst_inverse :
    Matrix.fromBlocks A B C D*auxiliaryFirst A B C D=1 ∧
    auxiliaryFirst A B C D*Matrix.fromBlocks A B C D=1 := by
  let _ := Matrix.fromBlocks₁₁Invertible A B C D
  rw [auxiliaryFirst,← Matrix.invOf_fromBlocks₁₁_eq]
  exact ⟨mul_invOf_self _,invOf_mul_self _⟩

omit [Fintype b] [DecidableEq b] in
theorem same_boson_kernel (bb : Matrix b b ℂ) (left : Matrix b (a ⊕ m) ℂ)
    (right : Matrix (a ⊕ m) b ℂ) :
    schur bb left right (auxiliaryFirst A B C D)=schur bb left right (matterFirst A B C D) := by
  rw [elimination_order]

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective

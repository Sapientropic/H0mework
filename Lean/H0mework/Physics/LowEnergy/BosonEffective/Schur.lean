import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Complex.Basic

/-! Exact matter elimination writes both the retained equation and the discarded
matter equation. Its inverse is the retained block of the same full system. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective
noncomputable section
variable {b m : Type*} [Fintype b] [Fintype m] [DecidableEq b] [DecidableEq m]

def schur (A : Matrix b b ℂ) (B : Matrix b m ℂ) (C : Matrix m b ℂ) (G : Matrix m m ℂ) : Matrix b b ℂ :=
  A-B*G*C

def matterWrite (G : Matrix m m ℂ) (C : Matrix m b ℂ) (v : b → ℂ) : m → ℂ :=
  -(G*ᵥ(C*ᵥv))

omit [DecidableEq b] in
theorem eliminated_row (D G : Matrix m m ℂ) (C : Matrix m b ℂ)
    (right : D*G=1) (v : b → ℂ) : C*ᵥv+D*ᵥmatterWrite G C v=0 := by
  unfold matterWrite
  rw [Matrix.mulVec_neg,Matrix.mulVec_mulVec (C*ᵥv) D G,right,Matrix.one_mulVec,add_neg_cancel]

omit [DecidableEq b] [DecidableEq m] in
theorem retained_row (A : Matrix b b ℂ) (B : Matrix b m ℂ) (C : Matrix m b ℂ)
    (G : Matrix m m ℂ) (v : b → ℂ) :
    A*ᵥv+B*ᵥmatterWrite G C v=schur A B C G*ᵥv := by
  simp only [matterWrite,schur,Matrix.mulVec_neg,sub_eq_add_neg,Matrix.add_mulVec,
    Matrix.neg_mulVec,Matrix.mulVec_mulVec,Matrix.mul_assoc]

theorem full_response (A : Matrix b b ℂ) (B : Matrix b m ℂ) (C : Matrix m b ℂ)
    (D G : Matrix m m ℂ) (R : Matrix b b ℂ) (matterInverse : D*G=1)
    (bosonInverse : schur A B C G*R=1) (current : b → ℂ) :
    A*ᵥ(R*ᵥcurrent)+B*ᵥmatterWrite G C (R*ᵥcurrent)=current ∧
    C*ᵥ(R*ᵥcurrent)+D*ᵥmatterWrite G C (R*ᵥcurrent)=0 := by
  constructor
  · rw [retained_row,Matrix.mulVec_mulVec,bosonInverse,Matrix.one_mulVec]
  · exact eliminated_row D G C matterInverse _

omit [DecidableEq b] in
theorem eliminated_unique (D G : Matrix m m ℂ) (C : Matrix m b ℂ)
    (left : G*D=1) (v : b → ℂ) (w : m → ℂ) (equation : C*ᵥv+D*ᵥw=0) : w=matterWrite G C v := by
  have applied := congrArg (fun x : m → ℂ => G*ᵥx) equation
  simp only [Matrix.mulVec_add,Matrix.mulVec_mulVec,left,Matrix.one_mulVec,Matrix.mulVec_zero] at applied
  simpa only [matterWrite,Matrix.mulVec_mulVec] using eq_neg_of_add_eq_zero_right applied

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonEffective

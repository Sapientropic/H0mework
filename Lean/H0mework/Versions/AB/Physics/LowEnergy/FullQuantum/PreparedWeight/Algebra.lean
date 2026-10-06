import H0mework.Versions.AB.Physics.LowEnergyFermion.Source
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! The original one-particle occupation determines a boundary determinant. -/
set_option autoImplicit false
open scoped Matrix BigOperators
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedWeight
open QuantizationCheck.Fermion
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def occupation (prepared : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec prepared (star prepared)

def boundaryDeterminant (prepared : ι → ℂ) (action : Matrix ι ι ℂ) : ℂ :=
  Matrix.det (1-occupation prepared+occupation prepared*action)

theorem rank_one_determinant (u v : ι → ℂ) :
    Matrix.det (1+Matrix.vecMulVec u v)=1+v ⬝ᵥ u := by
  rw [Matrix.vecMulVec_eq Unit]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) u v

theorem boundaryDeterminant_pair (prepared : ι → ℂ) (action : Matrix ι ι ℂ)
    (unit : Fermion.modePair prepared prepared=1) :
    boundaryDeterminant prepared action=Fermion.modePair prepared (action*ᵥprepared) := by
  have kernel : 1-occupation prepared+occupation prepared*action=
      1+Matrix.vecMulVec prepared (fun j => (star prepared ᵥ* action) j-star (prepared j)) := by
    ext i j
    simp only [occupation,Matrix.vecMulVec_apply,Matrix.mul_apply,Matrix.sub_apply,Matrix.add_apply,
      Matrix.vecMul,Pi.star_apply,dotProduct,Finset.mul_sum,mul_assoc,mul_sub]
    ring
  rw [boundaryDeterminant,kernel,rank_one_determinant]
  have sum : (fun j => (star prepared ᵥ* action) j-star (prepared j)) ⬝ᵥ prepared=
      Fermion.modePair prepared (action*ᵥprepared)-Fermion.modePair prepared prepared := by
    change ((star prepared ᵥ* action)-star prepared) ⬝ᵥ prepared=_
    rw [sub_dotProduct,← Matrix.dotProduct_mulVec]
    rfl
  rw [sum,unit]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.PreparedWeight

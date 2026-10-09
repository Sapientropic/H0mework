import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Cayley
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.ExteriorPower.Pairing

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1ElectronicEvolution
noncomputable section
open scoped Matrix InnerProductSpace
variable {n m E : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def fields (basis : n → E) (occupied : Matrix n m ℂ) (slot : m) : E :=
  ∑ mode, occupied mode slot • basis mode

theorem field_gram (basis : n → E) (orthogonal : Orthonormal ℂ basis)
    (occupied : Matrix n m ℂ) (first second : m) :
    inner ℂ (fields basis occupied first) (fields basis occupied second) =
      (occupied.conjTranspose * occupied) first second := by
  simp only [fields,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    orthonormal_iff_ite.mp orthogonal,Matrix.mul_apply,Matrix.conjTranspose_apply]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true,starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro mode _
  ring

theorem actual_field_gram (basis : n → E) (orthogonal : Orthonormal ℂ basis)
    (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ)
    (occupied : Matrix n m ℂ) (first second : m) :
    inner ℂ (fields basis (occupiedUpdate H time occupied) first)
      (fields basis (occupiedUpdate H time occupied) second) =
      inner ℂ (fields basis occupied first) (fields basis occupied second) := by
  rw [field_gram basis orthogonal,field_gram basis orthogonal,occupied_gram H hermitian time]

variable [DecidableEq m]
theorem occupied_fields (basis : n → E) (orthogonal : Orthonormal ℂ basis)
    (occupied : Matrix n m ℂ) (normalized : occupied.conjTranspose * occupied = 1) :
    Orthonormal ℂ (fields basis occupied) := by
  apply orthonormal_iff_ite.mpr
  intro first second
  rw [field_gram basis orthogonal,normalized]
  rfl

theorem updated_fields (basis : n → E) (orthogonal : Orthonormal ℂ basis)
    (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ)
    (occupied : Matrix n m ℂ) (normalized : occupied.conjTranspose * occupied = 1) :
    Orthonormal ℂ (fields basis (occupiedUpdate H time occupied)) :=
  occupied_fields basis orthogonal _ ((occupied_gram H hermitian time occupied).trans normalized)

variable {electrons : Nat}
def slater (orbitals : Fin electrons → E) : ⋀[ℂ]^electrons E :=
  exteriorPower.ιMulti ℂ electrons orbitals

def slaterDual (orbitals : Fin electrons → E) : Module.Dual ℂ (⋀[ℂ]^electrons E) :=
  exteriorPower.pairingDual ℂ E electrons
    (exteriorPower.ιMulti ℂ electrons (fun slot => (innerSL ℂ (orbitals slot)).toLinearMap))

theorem slater_normalized (orbitals : Fin electrons → E) (orthogonal : Orthonormal ℂ orbitals) :
    slaterDual orbitals (slater orbitals) = 1 := by
  rw [slaterDual,slater,exteriorPower.pairingDual_ιMulti_ιMulti]
  have identity : Matrix.of (fun i j : Fin electrons =>
      (innerSL ℂ (orbitals j)).toLinearMap (orbitals i)) = 1 := by
    ext i j
    change inner ℂ (orbitals j) (orbitals i) = _
    rw [orthonormal_iff_ite.mp orthogonal]
    simp only [Matrix.one_apply,eq_comm]
  rw [identity,Matrix.det_one]

theorem actual_slater (basis : n → E) (orthogonal : Orthonormal ℂ basis)
    (H : Matrix n n ℂ) (hermitian : H.IsHermitian) (time : ℝ)
    (occupied : Matrix n (Fin electrons) ℂ) (normalized : occupied.conjTranspose * occupied = 1) :
    slaterDual (fields basis (occupiedUpdate H time occupied))
      (slater (fields basis (occupiedUpdate H time occupied))) = 1 :=
  slater_normalized _ (updated_fields basis orthogonal H hermitian time occupied normalized)

end
end CPS1ElectronicEvolution

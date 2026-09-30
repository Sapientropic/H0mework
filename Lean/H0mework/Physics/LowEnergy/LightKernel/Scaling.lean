import H0mework.Physics.LowEnergy.LightKernel.Source
import Mathlib.Topology.Instances.Matrix

/-! The linear time pair and the quadratic kernel give different source
scalings. Exact row factors identify the first nonzero determinant orders. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
noncomputable section

theorem pair_scale (t u : ℂ) : pair (t*u)=t • pair u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pair] <;> ring

theorem pairSecond_scale (t u q : ℂ) : pairSecond (t*u) (t*q)=t^2 • pairSecond u q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pairSecond,pairDiagonal₁,pairDiagonal₂] <;> ring

theorem mixing_scale (t u q : ℂ) : mixing (t*u) (t*q)=t^2 • mixing u q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mixing,realMix,vectorMix,axialMix] <;> ring

theorem core_scale (t u q : ℂ) : core (t*u) (t*q)=t^2 • core u q := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [core,realKernel,vectorKernel,axialKernel] <;> ring

def rayReduced (u q t : ℂ) : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) ℂ :=
  Matrix.fromBlocks (pair u+t • pairSecond u q) (t • mixing u q) (mixing u q).transpose (core u q)

def rayRowScale (t : ℂ) : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) ℂ :=
  Matrix.fromBlocks (t • (1 : Matrix (Fin 2) (Fin 2) ℂ)) 0 0 (t^2 • (1 : Matrix (Fin 3) (Fin 3) ℂ))

theorem ray_factor (u q t : ℂ) : blockPencil (t*u) (t*q)=rayRowScale t*rayReduced u q t := by
  rw [rayRowScale,rayReduced,Matrix.fromBlocks_multiply]
  simp only [blockPencil,pair_scale,pairSecond_scale,mixing_scale,core_scale,Matrix.transpose_smul,
    Matrix.smul_mul,Matrix.one_mul,Matrix.zero_mul,add_zero,zero_add,smul_add,smul_smul]
  rw [pow_two]

theorem ray_determinant_factor (u q t : ℂ) :
    (blockPencil (t*u) (t*q)).det=t^8*(rayReduced u q t).det := by
  rw [ray_factor,Matrix.det_mul]
  congr 1
  rw [rayRowScale,Matrix.det_fromBlocks_zero₂₁,Matrix.det_smul,Matrix.det_smul]
  simp
  ring

def characteristic (u q : ℂ) : ℂ :=
  (655360/537273)*u^2*(5*q^2+3*u^2)*(55*q^2+67*u^2)*(125*q^2-162*u^2)

theorem ray_initial_determinant (u q : ℂ) : (rayReduced u q 0).det=characteristic u q := by
  simp only [rayReduced,zero_smul,add_zero]
  rw [Matrix.det_fromBlocks_zero₁₂,pair_determinant,core_determinant]
  unfold characteristic
  ring

def quadraticReduced (slow t : ℂ) : Matrix (Fin 2 ⊕ Fin 3) (Fin 2 ⊕ Fin 3) ℂ :=
  Matrix.fromBlocks (pair slow+pairSecond (t*slow) 1) (mixing (t*slow) 1)
    (mixing (t*slow) 1).transpose (core (t*slow) 1)

theorem quadratic_factor (slow t : ℂ) :
    blockPencil (t^2*slow) t=t^2 • quadraticReduced slow t := by
  have ps : pairSecond (t^2*slow) t=t^2 • pairSecond (t*slow) 1 := by
    simpa only [mul_one,pow_two,mul_assoc] using pairSecond_scale t (t*slow) 1
  have ms : mixing (t^2*slow) t=t^2 • mixing (t*slow) 1 := by
    simpa only [mul_one,pow_two,mul_assoc] using mixing_scale t (t*slow) 1
  have cs : core (t^2*slow) t=t^2 • core (t*slow) 1 := by
    simpa only [mul_one,pow_two,mul_assoc] using core_scale t (t*slow) 1
  rw [blockPencil,quadraticReduced,pair_scale,ps,ms,cs,Matrix.transpose_smul]
  simp only [Matrix.fromBlocks_smul,smul_add]

theorem quadratic_determinant_factor (slow t : ℂ) :
    (blockPencil (t^2*slow) t).det=t^10*(quadraticReduced slow t).det := by
  rw [quadratic_factor,Matrix.det_smul]
  congr 1
  norm_num only [Fintype.card_sum,Fintype.card_fin]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightKernel

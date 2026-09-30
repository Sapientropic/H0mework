import H0mework.Physics.LowEnergy.LightKernel.Scaling

/-! The static quadratic complement of the first-order pair is generated
explicitly. Both light scalings have genuine nonzero leading determinants. -/
set_option autoImplicit false
open scoped Matrix
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightKernel
open Filter Topology
noncomputable section

def staticCoreInverse : Matrix (Fin 3) (Fin 3) ℂ :=
  !![9/80,0,0;0,67/160,0;0,0,81/2500]

theorem static_core_inverse : core 0 1*staticCoreInverse=1 ∧ staticCoreInverse*core 0 1=1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [core,realKernel,vectorKernel,axialKernel,staticCoreInverse,Matrix.mul_apply,Fin.sum_univ_succ]

theorem quadratic_pair_generated (slow : ℂ) :
    pair slow+pairSecond 0 1-mixing 0 1*staticCoreInverse*(mixing 0 1).transpose=
      !![-40/3,-8*slow;8*slow,-10/3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pair,pairSecond,pairDiagonal₁,pairDiagonal₂,mixing,realMix,vectorMix,axialMix,
      staticCoreInverse,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_succ]

theorem quadratic_initial_determinant (slow : ℂ) :
    (quadraticReduced slow 0).det=(512000000/439587 : ℂ)*(36*slow^2+25) := by
  let : Invertible (core 0 1) := ⟨staticCoreInverse,static_core_inverse.2,static_core_inverse.1⟩
  simp only [quadraticReduced,zero_mul]
  rw [Matrix.det_fromBlocks₂₂]
  change (core 0 1).det*(pair slow+pairSecond 0 1-mixing 0 1*staticCoreInverse*(mixing 0 1).transpose).det= _
  rw [quadratic_pair_generated,Matrix.det_fin_two,core_determinant]
  norm_num
  ring

theorem source_ray_leading (u q : ℂ) :
    Tendsto (fun t : ℂ => (blockPencil (t*u) (t*q)).det/t^8)
      (𝓝[≠] 0) (𝓝 (characteristic u q)) := by
  have continuousMatrix : Continuous (fun t : ℂ => rayReduced u q t) := by
    unfold rayReduced
    fun_prop
  have generated := (continuousMatrix.matrix_det.continuousAt.tendsto).mono_left
    (show 𝓝[≠] (0 : ℂ)≤𝓝 0 from inf_le_left)
  rw [ray_initial_determinant] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with t nonzero
  have nonzero' : t≠0 := by simpa using nonzero
  rw [ray_determinant_factor]
  field_simp [nonzero']

theorem source_quadratic_leading (slow : ℂ) :
    Tendsto (fun t : ℂ => (blockPencil (t^2*slow) t).det/t^10)
      (𝓝[≠] 0) (𝓝 ((512000000/439587 : ℂ)*(36*slow^2+25))) := by
  have continuousMatrix : Continuous (fun t : ℂ => quadraticReduced slow t) := by
    unfold quadraticReduced pairSecond pairDiagonal₁ pairDiagonal₂ mixing realMix vectorMix axialMix
      core realKernel vectorKernel axialKernel
    fun_prop
  have generated := (continuousMatrix.matrix_det.continuousAt.tendsto).mono_left
    (show 𝓝[≠] (0 : ℂ)≤𝓝 0 from inf_le_left)
  rw [quadratic_initial_determinant] at generated
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with t nonzero
  have nonzero' : t≠0 := by simpa using nonzero
  rw [quadratic_determinant_factor]
  field_simp [nonzero']

theorem quadratic_frequency_pair :
    (36*(5*Complex.I/6)^2+25 : ℂ)=0 ∧ (36*(-5*Complex.I/6)^2+25 : ℂ)=0 := by
  norm_num [mul_pow,div_pow,Complex.I_sq]

theorem first_characteristic_nonzero : characteristic 1 1≠0 := by norm_num [characteristic]

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightKernel

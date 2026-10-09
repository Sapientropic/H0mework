import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Hpc

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
open scoped Matrix BigOperators
noncomputable section

def pcVector (n : Fin 4) : Fin 4 → ℚ :=
  ![![-1,0,1,0],![0,1,0,1],![-1,-1,-1,1],![1,-1,1,1]] n

def pcWeight (n : Fin 4) : ℚ := ![(1/2),(1/2),(1/4),(1/4)] n

def pcProjectionQ (n : Fin 4) : Matrix (Fin 4) (Fin 4) ℚ :=
  fun i j => pcWeight n*pcVector n i*pcVector n j

def rationalMatrix (A : Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 4) (Fin 4) ℂ := fun i j => (A i j : ℂ)

def pcProjection (n : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ := rationalMatrix (pcProjectionQ n)

def pcValues (x y : ℝ) : Fin 4 → ℂ := ![x+y-1,x+y+3,2*x+1,2*y+1]

theorem pc_projection_rational_orthogonal (a b : Fin 4) :
    pcProjectionQ a*pcProjectionQ b=if a=b then pcProjectionQ a else 0 := by
  revert a b
  decide +kernel

private theorem rational_multiply (A B : Matrix (Fin 4) (Fin 4) ℚ) :
    rationalMatrix (A*B)=rationalMatrix A*rationalMatrix B := by
  ext i j
  simp only [rationalMatrix,Matrix.mul_apply,Rat.cast_sum,Rat.cast_mul]

theorem pc_projection_orthogonal (a b : Fin 4) :
    pcProjection a*pcProjection b=if a=b then pcProjection a else 0 := by
  change rationalMatrix (pcProjectionQ a)*rationalMatrix (pcProjectionQ b)=_
  rw [← rational_multiply,pc_projection_rational_orthogonal]
  by_cases same : a=b
  · simp only [same,ite_true]; rfl
  · simp only [same,ite_false]
    ext i j
    simp [rationalMatrix]

theorem pc_projection_total : ∑ a : Fin 4, pcProjection a=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pcProjection,rationalMatrix,pcProjectionQ,pcWeight,pcVector,Matrix.sum_apply,Fin.sum_univ_succ]

theorem pc_projection_hermitian (a : Fin 4) : (pcProjection a).IsHermitian := by
  ext i j
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [pcProjection,rationalMatrix,pcProjectionQ,pcWeight,pcVector,Matrix.conjTranspose_apply]

theorem original_pc_resolution (x y : ℝ) : packedHpc x y=∑ a : Fin 4, pcValues x y a • pcProjection a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [packedHpc,pcValues,pcProjection,rationalMatrix,pcProjectionQ,pcWeight,pcVector,Matrix.sum_apply,
      Matrix.smul_apply,Fin.sum_univ_succ,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_div] <;> ring

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

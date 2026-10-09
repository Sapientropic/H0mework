import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.RationalEffect

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def firstSlope : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1/2,0,-1/2;1/2,1,1/2,0;0,1/2,1,-1/2;-1/2,0,-1/2,1]
def secondSlope : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,-1/2,0,1/2;-1/2,1,-1/2,0;0,-1/2,1,1/2;1/2,0,1/2,1]
private def weight : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1,3/4,2/3,0]
private def firstFactor : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0;1/2,1,0,0;0,2/3,1,0;-1/2,1/3,-1,1]
private def secondFactor : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,0,0,0;-1/2,1,0,0;0,-2/3,1,0;1/2,1/3,1,1]

private theorem weight_positive : weight.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.nonneg_iff]

theorem first_slope_gram : firstSlope=firstFactor*weight*firstFactorᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstSlope,firstFactor,weight,Matrix.mul_apply,Matrix.vecMul, dotProduct,Fin.sum_univ_succ,Matrix.diagonal_apply,map_ofNat]

theorem second_slope_gram : secondSlope=secondFactor*weight*secondFactorᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondSlope,secondFactor,weight,Matrix.mul_apply,Matrix.vecMul, dotProduct,Fin.sum_univ_succ,Matrix.diagonal_apply,map_ofNat]

theorem first_slope_positive : firstSlope.PosSemidef := by
  rw [first_slope_gram]
  exact weight_positive.mul_mul_conjTranspose_same firstFactor

theorem second_slope_positive : secondSlope.PosSemidef := by
  rw [second_slope_gram]
  exact weight_positive.mul_mul_conjTranspose_same secondFactor

theorem packed_affine_difference (x y a b : ℝ) :
    packedHpc x y-packedHpc a b=(x-a) • firstSlope+(y-b) • secondSlope := by
  ext i j
  change packedHpc x y i j-packedHpc a b i j=(x-a) • firstSlope i j+(y-b) • secondSlope i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstSlope,secondSlope,packedHpc,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Complex.real_smul]
  all_goals ring

theorem packed_monotone (x y a b : ℝ) (first : a ≤ x) (second : b ≤ y) :
    packedHpc a b ≤ packedHpc x y := by
  apply sub_nonneg.mp
  rw [packed_affine_difference]
  exact (first_slope_positive.smul (sub_nonneg.mpr first)).add
    (second_slope_positive.smul (sub_nonneg.mpr second)) |>.nonneg

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Order
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

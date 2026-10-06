import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceChartMatrices
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceChartBudget
open PreparationChartGuard PreparationPhaseScalar
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumNativeDimensions
open scoped BigOperators Matrix RealInnerProductSpace

def sourceGramWeight (i : Fin 9) : ℝ := if i=4 ∨ i=7 ∨ i=8 then 1 else 2
def sourceGramVector : Fin 9 → ℝ := ![0,0,0,0,1,0,0,-1,1]
def sourceGram : Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.diagonal sourceGramWeight +
    Matrix.replicateCol (Fin 1) sourceGramVector*Matrix.replicateRow (Fin 1) sourceGramVector

theorem sourceGram_apply (i j : Fin 9) :
    sourceGram i j=(if i=j then sourceGramWeight i else 0)+sourceGramVector i*sourceGramVector j := by
  simp only [sourceGram,Matrix.add_apply,Matrix.diagonal_apply]
  change (if i=j then sourceGramWeight i else 0)+
    (∑ _k : Fin 1,sourceGramVector i*sourceGramVector j)=_
  rw [Fin.sum_univ_one]

private theorem normalBuild_add (x y : NormalCoordinates) : normalBuild (x+y)=normalBuild x+normalBuild y := by
  apply nativeCoordinates.injective
  simp only [normalBuild,map_add,LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · ext i; fin_cases i <;> simp
  · apply Prod.ext
    · ext i; fin_cases i <;> simp
    · rfl

theorem sourceGram_actual (i j : Fin 9) : sourceD9 vacuum i j=sourceGram i j := by
  have read : sourceD9 vacuum i j=
      inner ℝ (orbit (normalBuild (sourceNormal i))) (orbit (normalBuild (sourceNormal j))) := by
    change inner ℝ (orbit (normalBuild (sourceNormal i))) (orbit (sourceBroken j).val)=_
    rw [sourceBroken_orbit]
  rw [read]
  rw [sourceGram_apply]
  have pair := norm_add_sq_real (orbit (normalBuild (sourceNormal i))) (orbit (normalBuild (sourceNormal j)))
  rw [←map_add,←normalBuild_add] at pair
  rw [normal_orbit_squared,normal_orbit_squared,normal_orbit_squared] at pair
  fin_cases i <;> fin_cases j
  all_goals norm_num [sourceNormal,PiLp.add_apply,PiLp.toLp_apply,Pi.single_apply,
    sourceGramWeight,sourceGramVector,Fin.ext_iff] at pair ⊢
  all_goals linarith

theorem sourceGram_entry_bound (i j : Fin 9) : |sourceGram i j| ≤ 4 := by
  rw [sourceGram_apply]
  fin_cases i <;> fin_cases j
  all_goals norm_num [sourceGramWeight,sourceGramVector,Fin.ext_iff]

theorem sourceGram_diagonal_det : (Matrix.diagonal sourceGramWeight).det=64 := by
  rw [Matrix.det_diagonal]
  norm_num [sourceGramWeight,Fin.prod_univ_succ,Fin.ext_iff]

theorem sourceGram_vector_diagonal (i : Fin 9) : sourceGramWeight i*sourceGramVector i=sourceGramVector i := by
  fin_cases i <;> norm_num [sourceGramWeight,sourceGramVector,Fin.ext_iff]

theorem sourceGram_factor : sourceGram=Matrix.diagonal sourceGramWeight*
    (1+Matrix.replicateCol (Fin 1) sourceGramVector*Matrix.replicateRow (Fin 1) sourceGramVector) := by
  rw [Matrix.mul_add,Matrix.mul_one]
  unfold sourceGram
  congr 1
  rw [←Matrix.mul_assoc]
  congr 1
  ext i j
  simp only [Matrix.diagonal_mul,Matrix.replicateCol_apply,sourceGram_vector_diagonal]

theorem sourceGram_det : sourceGram.det=256 := by
  rw [sourceGram_factor,Matrix.det_mul,sourceGram_diagonal_det,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  norm_num [dotProduct,sourceGramVector,Fin.sum_univ_succ]

theorem sourceD9_vacuum_det : (sourceD9 vacuum).det=256 := by
  have same : sourceD9 vacuum=sourceGram := by ext i j; exact sourceGram_actual i j
  rw [same,sourceGram_det]

end LowEnergy.PreparationVacuumSourceChartBudget

import H0mework.Physics.Dirac.PointwiseDiracSpinConnectionLift

/-!
# Traceless centralizer rigidity for the fixed Dirac gamma representation

The four explicit gamma matrices generate the full complex Dirac matrix
algebra: a matrix commuting with all four is scalar.  This file proves the
traceless form needed by the Stage-9 local Spin reconstruction directly from
fixed gamma coordinates.  No abstract irreducibility or supplied centralizer
certificate is used.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracGammaCentralizer

open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open scoped Matrix

noncomputable section

set_option autoImplicit false

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- A traceless complex `4 × 4` matrix commuting with every fixed Dirac gamma
matrix is zero.  The proof is a coordinate elimination in the actual gamma
representation. -/
theorem diracMatrix_eq_zero_of_trace_eq_zero_of_gamma_commutators
    (matrix : DiracMatrix)
    (traceZero : Matrix.trace matrix = 0)
    (commutatorZero :
      ∀ internal : LorentzianIndex,
        diracMatrixCommutator matrix (diracGamma internal) = 0) :
    matrix = 0 := by
  have entryZero
      (internal : LorentzianIndex) (row column : DiracSpinorIndex) :
      diracMatrixCommutator matrix (diracGamma internal) row column = 0 := by
    have entry :=
      congrFun (congrFun (commutatorZero internal) row) column
    simpa using entry

  have h0_00 := entryZero 0 0 0
  have h0_01 := entryZero 0 0 1
  have h0_02 := entryZero 0 0 2
  have h0_03 := entryZero 0 0 3
  have h0_10 := entryZero 0 1 0
  have h0_11 := entryZero 0 1 1
  have h0_12 := entryZero 0 1 2
  have h0_13 := entryZero 0 1 3
  have h1_00 := entryZero 1 0 0
  have h1_01 := entryZero 1 0 1
  have h1_02 := entryZero 1 0 2
  have h1_03 := entryZero 1 0 3
  have h2_00 := entryZero 2 0 0
  have h3_00 := entryZero 3 0 0
  have h3_03 := entryZero 3 0 3

  norm_num [diracMatrixCommutator, diracGamma, diracGammaZero,
    diracGammaOne, diracGammaTwo, diracGammaThree, Matrix.mul_apply,
    Matrix.vecMul_apply_eq_sum, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod,
    Matrix.cons_val, Nat.reduceMod] at h0_00 h0_01 h0_02 h0_03 h0_10 h0_11 h0_12 h0_13 h1_00 h1_01 h1_02 h1_03 h2_00 h3_00 h3_03

  have entry02Zero : matrix 0 2 = 0 := by
    linear_combination (1 / 2) * h3_00 - (1 / 2) * h0_00
  have entry20Zero : matrix 2 0 = 0 := by
    linear_combination -(1 / 2) * h3_00 - (1 / 2) * h0_00
  rw [entry02Zero] at h1_01
  have entry31Zero : matrix 3 1 = 0 := by
    linear_combination -h1_01
  rw [entry31Zero] at h0_11
  have entry13Zero : matrix 1 3 = 0 := by
    linear_combination -h0_11

  have entry30Eq : matrix 3 0 = matrix 0 3 := by
    linear_combination -h1_00
  rw [entry30Eq] at h2_00
  have doubledEntry03 :
      (2 * Complex.I) * matrix 0 3 = 0 := by
    linear_combination h2_00
  have entry03Zero : matrix 0 3 = 0 := by
    exact (mul_eq_zero.mp doubledEntry03).resolve_left
      (mul_ne_zero (by norm_num) Complex.I_ne_zero)
  have entry30Zero : matrix 3 0 = 0 := by
    rw [entry30Eq, entry03Zero]
  rw [entry30Zero] at h0_10
  have entry12Zero : matrix 1 2 = 0 := by
    linear_combination -h0_10
  rw [entry03Zero] at h0_01
  have entry21Zero : matrix 2 1 = 0 := by
    linear_combination -h0_01

  have entry01Zero : matrix 0 1 = 0 := by
    linear_combination (1 / 2) * (h0_03 - h3_03)
  rw [entry01Zero] at h0_03 h1_02
  have entry23Zero : matrix 2 3 = 0 := by
    linear_combination -h0_03
  have entry32Zero : matrix 3 2 = 0 := by
    linear_combination -h1_02
  rw [entry32Zero] at h0_12
  have entry10Zero : matrix 1 0 = 0 := by
    linear_combination h0_12

  have entry22Eq : matrix 2 2 = matrix 0 0 := by
    linear_combination -h0_02
  have entry33Eq : matrix 3 3 = matrix 0 0 := by
    linear_combination -h1_03
  have entry11Eq : matrix 1 1 = matrix 0 0 := by
    linear_combination h0_13 - h1_03

  simp [Matrix.trace, Fin.sum_univ_four, entry11Eq, entry22Eq, entry33Eq]
      at traceZero
  have entry00Zero : matrix 0 0 = 0 := by
    linear_combination (1 / 4) * traceZero
  have entry11Zero : matrix 1 1 = 0 := by
    rw [entry11Eq, entry00Zero]
  have entry22Zero : matrix 2 2 = 0 := by
    rw [entry22Eq, entry00Zero]
  have entry33Zero : matrix 3 3 = 0 := by
    rw [entry33Eq, entry00Zero]

  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [entry00Zero, entry01Zero, entry02Zero, entry03Zero,
      entry10Zero, entry11Zero, entry12Zero, entry13Zero,
      entry20Zero, entry21Zero, entry22Zero, entry23Zero,
      entry30Zero, entry31Zero, entry32Zero, entry33Zero]

end

end SaturationMonoid.PhysicsCore.StageNineDiracGammaCentralizer

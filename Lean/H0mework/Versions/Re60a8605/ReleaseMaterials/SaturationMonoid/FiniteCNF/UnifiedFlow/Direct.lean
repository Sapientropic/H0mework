import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Spectrum
import H0mework.Quantum.Generator.P257
import Mathlib.Analysis.Matrix.Hermitian

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.UnifiedFlowProbe
open SaturationMonoid.AffineRelaxation
noncomputable section

abbrev Space (n : Nat) := EuclideanSpace ℂ (Assignment n)

def matrix {n : Nat} (formula : CNFFormula n) : Matrix (Assignment n) (Assignment n) ℂ :=
  Matrix.diagonal (fun assignment => (violationCount formula assignment : ℂ))

theorem matrix_hermitian {n : Nat} (formula : CNFFormula n) : (matrix formula).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro assignment
  simp [isSelfAdjoint_iff]

def operator {n : Nat} (formula : CNFFormula n) : Space n →L[ℂ] Space n :=
  Matrix.toEuclideanCLM (n := Assignment n) (𝕜 := ℂ) (matrix formula)

theorem source_flow {n : Nat} (formula : CNFFormula n) :
    BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate (Space n) (operator formula) :=
  boundedSelfAdjointHamiltonianSchrodingerFlowCertificate _
    ((matrix_hermitian formula).isSelfAdjoint.map (Matrix.toEuclideanCLM (n := Assignment n) (𝕜 := ℂ)))

theorem diagonal_zero_iff {n : Nat} (formula : CNFFormula n) (assignment : Assignment n) :
    matrix formula assignment assignment = 0 ↔ CNFFormula.eval formula (extendAssignment assignment) = true := by
  simp only [matrix, Matrix.diagonal_apply_eq, Nat.cast_eq_zero]
  exact violationCount_eq_zero_iff_eval formula assignment

theorem zero_energy_iff_sat {n : Nat} (formula : CNFFormula n) :
    (∃ assignment : Assignment n, matrix formula assignment assignment = 0) ↔ CNFSatisfiable formula := by
  rw [satisfiable_iff_finite_assignment]
  exact exists_congr (diagonal_zero_iff formula)

end
end SaturationMonoid.ComplexityProjection.SATSource.UnifiedFlowProbe

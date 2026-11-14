import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Table
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Projector
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Acceptance
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Boolean
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Decision

theorem table_lift (n : Nat) (basis : List Row) (inside : RowsWithin n basis)
    (parameters : Assignment (freeIndices n basis).length) :
    Gates.lift n (Table.coordinates n basis) parameters = parameterLift n basis parameters := by
  funext i
  exact congrFun (Table.coordinates_value n basis inside (extendAssignment parameters)) i.val

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  match eliminate (Extract.extract formula) with
  | .contradiction => false
  | .basis basis =>
      Boolean.decideWith (freeIndices n basis).length (Table.coordinates n basis) formula

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  cases generated : eliminate (Extract.extract formula) with
  | contradiction =>
      have rejected : ¬ CNFSatisfiable formula := by
        rintro ⟨assignment, accepted⟩
        rw [extracted_contradiction_eval formula generated] at accepted
        exact Bool.noConfusion accepted
      simp [decideFormula, generated, rejected]
  | basis basis =>
      simp only [decideFormula, generated, Boolean.decideWith_correct]
      simp only [table_lift n basis (extracted_basis_within formula basis generated)]
      exact (satisfiable_iff_free formula basis generated).symm

theorem decideFormula_no {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = false ↔ ¬ CNFSatisfiable formula := by
  rw [← Bool.not_eq_true, decideFormula_correct]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits, Encoding.decideBits, parsed]
  | some input =>
      simp only [decideBits, Encoding.decideBits, parsed]
      apply Bool.eq_iff_iff.mpr
      rw [decideFormula_correct, Dense.decideFormula_correct]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) :
    decideBits bits = false := by simp [decideBits, invalid]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original, Encoding.decideBits_iff_rootVerify]

theorem initial_nodes {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (Acceptance.compile (Table.coordinates n basis) formula).code.size ≤
      3 + n + 2 * n * (freeIndices n basis).length +
        3 * formula.length + 3 * SATJoint.literalCount formula := by
  have source := Acceptance.compile_size (Table.coordinates n basis) formula
  have storage := Table.coordinates_storage n basis
  simp only [Acceptance.initialNodes, Table.coordinates_size] at source
  nlinarith

theorem initial_nodes_generated {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : eliminate (Extract.extract formula) = .basis basis) :
    (Acceptance.compile (Table.coordinates n basis) formula).code.size ≤
      3 + n + 2 * n * n + 3 * formula.length + 3 * SATJoint.literalCount formula := by
  have bound := initial_nodes formula basis
  have dimension := extracted_basis_dimension formula basis generated
  have freeBound : (freeIndices n basis).length ≤ n := by omega
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Decision

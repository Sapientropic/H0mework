import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Atoms
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Realization

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Atoms

theorem gateAction_mask {n freeWidth : Nat} (formula : CNFFormula n) (coordinates : Array Row)
    (source : Source n) (parameters : Assignment freeWidth) :
    gateAction formula coordinates source parameters =
      if CNFFormula.eval formula (extendAssignment (Gates.lift n coordinates parameters)) = true
      then source (Gates.lift n coordinates parameters) else 0 := by
  rw [gateAction, Acceptance.eval_compile]
  have same := formula_eval_restrict formula (Gates.coordinate coordinates (extendAssignment parameters))
  change CNFFormula.eval formula (extendAssignment (Gates.lift n coordinates parameters)) = _ at same
  rw [← same]
  simp only [InterferenceProgram.bit]
  split <;> simp_all

theorem original_projector_compiled_gates {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : generate formula = .basis basis) (source : Source n) :
    zeroProjector formula source = freeZeroExtension n basis
      (gateAction formula (Table.coordinates n basis) source) := by
  have triangular := generated_triangular formula basis generated
  have inside := generated_within formula basis generated
  funext assignment
  rw [zeroProjector_apply]
  by_cases relations : holds basis (extendAssignment assignment) = true
  · have recovery := (Decision.table_lift n basis inside (projectFree n basis assignment)).trans
      (parameterLift_projectFree n basis triangular assignment relations)
    simp only [freeZeroExtension, if_pos relations, gateAction_mask, recovery]
  · have rejected : CNFFormula.eval formula (extendAssignment assignment) ≠ true :=
      fun accepted => relations (generated_relations formula basis generated _ accepted)
    simp [freeZeroExtension, relations, rejected]

theorem contradiction_projector {n : Nat} (formula : CNFFormula n)
    (generated : generate formula = .contradiction) : zeroProjector formula = 0 := by
  apply LinearMap.ext
  intro source
  funext assignment
  rw [zeroProjector_apply, generated_contradiction_eval formula generated]
  rfl

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  match generate formula with
  | .contradiction => false
  | .basis basis => Boolean.decideWith (freeIndices n basis).length (Table.coordinates n basis) formula

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  cases generated : generate formula with
  | contradiction =>
      have rejected : ¬ CNFSatisfiable formula := by
        rintro ⟨assignment, accepted⟩
        rw [generated_contradiction_eval formula generated] at accepted
        exact Bool.noConfusion accepted
      simp [decideFormula, generated, rejected]
  | basis basis =>
      simp only [decideFormula, generated, Boolean.decideWith_correct,
        Decision.table_lift n basis (generated_within formula basis generated)]
      exact (satisfiable_iff_free formula basis generated).symm

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

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original, Encoding.decideBits_iff_rootVerify]

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔ ¬ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [decideBits_eq_original, Encoding.decideBits_no]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) : decideBits bits = false := by
  simp [decideBits, invalid]

theorem initial_nodes {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : generate formula = .basis basis) :
    (Acceptance.compile (Table.coordinates n basis) formula).code.size ≤
      3 + n + 2 * n * n + 3 * formula.length + 3 * SATJoint.literalCount formula := by
  have bound := Decision.initial_nodes formula basis
  have dimension := generated_dimension formula basis generated
  have freeBound : (freeIndices n basis).length ≤ n := by omega
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Atoms

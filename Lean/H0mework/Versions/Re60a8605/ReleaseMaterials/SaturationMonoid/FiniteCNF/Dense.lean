import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Encoding.Syntax
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Alias
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.EmptyCube
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Eliminate
import Mathlib.Data.List.Nodup

/-!
# Dense addresses generated from the original occurring variables

All output addresses are computed by `idxOf` in the original source-variable
list. The producer traverses that list and the original clauses, never the
ambient `Fin n` universe. Assignment readback preserves the original CNF and
the encoded result has a size bound in the original clause and literal counts.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Dense

abbrev width {n : Nat} (source : CNFFormula n) : Nat := (Shared.sourceVars source).length

def address {n : Nat} (source : CNFFormula n) (v : Fin n)
    (mem : v ∈ Shared.sourceVars source) : Fin (width source) :=
  ⟨(Shared.sourceVars source).idxOf v, List.idxOf_lt_length_of_mem mem⟩

theorem get_address {n : Nat} (source : CNFFormula n) (v : Fin n)
    (mem : v ∈ Shared.sourceVars source) :
    (Shared.sourceVars source).get (address source v mem) = v := List.idxOf_get _

def lowerAssignment {n : Nat} (source : CNFFormula n) (assignment : Nat → Bool) : Nat → Bool :=
  fun i => if hi : i < width source then
    assignment ((Shared.sourceVars source).get ⟨i, hi⟩).val else false

def liftAssignment {n : Nat} (source : CNFFormula n) (assignment : Nat → Bool) : Nat → Bool :=
  fun i => if hi : i < n then
    if (⟨i, hi⟩ : Fin n) ∈ Shared.sourceVars source then
      assignment ((Shared.sourceVars source).idxOf ⟨i, hi⟩)
    else false
  else false

theorem lowerAssignment_address {n : Nat} (source : CNFFormula n)
    (assignment : Nat → Bool) (v : Fin n) (mem : v ∈ Shared.sourceVars source) :
    lowerAssignment source assignment (address source v mem).val = assignment v.val := by
  simp only [lowerAssignment, dif_pos (address source v mem).isLt]
  exact congrArg (fun index : Fin n => assignment index.val) (get_address source v mem)

theorem liftAssignment_source {n : Nat} (source : CNFFormula n)
    (assignment : Nat → Bool) (v : Fin n) (mem : v ∈ Shared.sourceVars source) :
    liftAssignment source assignment v.val = assignment (address source v mem).val := by
  simp [liftAssignment, v.isLt, mem, address]

/-- Every occurring original coordinate survives lowering followed by lifting. -/
theorem lift_lower_source {n : Nat} (source : CNFFormula n)
    (assignment : Nat → Bool) (v : Fin n) (mem : v ∈ Shared.sourceVars source) :
    liftAssignment source (lowerAssignment source assignment) v.val = assignment v.val := by
  rw [liftAssignment_source source _ v mem, lowerAssignment_address]

/-- Every generated dense coordinate has its original source address. -/
theorem lower_lift_dense {n : Nat} (source : CNFFormula n)
    (assignment : Nat → Bool) (i : Fin (width source)) :
    lowerAssignment source (liftAssignment source assignment) i.val = assignment i.val := by
  rw [lowerAssignment, dif_pos i.isLt]
  rw [liftAssignment_source source assignment ((Shared.sourceVars source).get i)
    (List.get_mem _ i)]
  exact congrArg assignment
    (List.get_idxOf (List.nodup_dedup _) i)

def renameLiteral {n : Nat} (source : CNFFormula n) (lit : CNFLiteral n)
    (mem : lit.var ∈ Shared.sourceVars source) : CNFLiteral (width source) :=
  ⟨address source lit.var mem, lit.positive⟩

theorem renameLiteral_eval_lower {n : Nat} (source : CNFFormula n) (lit : CNFLiteral n)
    (mem : lit.var ∈ Shared.sourceVars source) (assignment : Nat → Bool) :
    (renameLiteral source lit mem).eval (lowerAssignment source assignment) =
      lit.eval assignment := by
  simp only [renameLiteral, CNFLiteral.eval, lowerAssignment_address]

theorem renameLiteral_eval_lift {n : Nat} (source : CNFFormula n) (lit : CNFLiteral n)
    (mem : lit.var ∈ Shared.sourceVars source) (assignment : Nat → Bool) :
    (renameLiteral source lit mem).eval assignment =
      lit.eval (liftAssignment source assignment) := by
  simp only [renameLiteral, CNFLiteral.eval, liftAssignment_source source assignment lit.var mem]
  rfl

def renameClause {n : Nat} (source : CNFFormula n)
    (clause : { c : CNFClause n // c ∈ source }) : CNFClause (width source) :=
  clause.val.attach.map fun lit => renameLiteral source lit.val
    (Shared.sourceVars_supported source clause.val clause.property lit.val lit.property)

private theorem any_attach {α : Type} (values : List α) (predicate : α → Bool) :
    values.attach.any (fun value => predicate value.val) = values.any predicate := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨value, _, holds⟩
    exact ⟨value.val, value.property, holds⟩
  · rintro ⟨value, mem, holds⟩
    exact ⟨⟨value, mem⟩, by simp, holds⟩

private theorem all_attach {α : Type} (values : List α) (predicate : α → Bool) :
    values.attach.all (fun value => predicate value.val) = values.all predicate := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro holds value mem
    exact holds ⟨value, mem⟩ (by simp)
  · intro holds value _
    exact holds value.val value.property

theorem renameClause_eval_lower {n : Nat} (source : CNFFormula n)
    (clause : { c : CNFClause n // c ∈ source }) (assignment : Nat → Bool) :
    CNFClause.eval (renameClause source clause) (lowerAssignment source assignment) =
      CNFClause.eval clause.val assignment := by
  simp only [renameClause, CNFClause.eval, List.any_map, Function.comp_def,
    renameLiteral_eval_lower]
  exact any_attach clause.val (fun lit => lit.eval assignment)

theorem renameClause_eval_lift {n : Nat} (source : CNFFormula n)
    (clause : { c : CNFClause n // c ∈ source }) (assignment : Nat → Bool) :
    CNFClause.eval (renameClause source clause) assignment =
      CNFClause.eval clause.val (liftAssignment source assignment) := by
  simp only [renameClause, CNFClause.eval, List.any_map, Function.comp_def,
    renameLiteral_eval_lift]
  exact any_attach clause.val (fun lit => lit.eval (liftAssignment source assignment))

def renameFormula {n : Nat} (source : CNFFormula n) : CNFFormula (width source) :=
  source.attach.map (renameClause source)

theorem renameFormula_eval_lower {n : Nat} (source : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (renameFormula source) (lowerAssignment source assignment) =
      CNFFormula.eval source assignment := by
  simp only [renameFormula, CNFFormula.eval, List.all_map, Function.comp_def,
    renameClause_eval_lower]
  exact all_attach source (fun clause => CNFClause.eval clause assignment)

theorem renameFormula_eval_lift {n : Nat} (source : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (renameFormula source) assignment =
      CNFFormula.eval source (liftAssignment source assignment) := by
  simp only [renameFormula, CNFFormula.eval, List.all_map, Function.comp_def,
    renameClause_eval_lift]
  exact all_attach source (fun clause => CNFClause.eval clause (liftAssignment source assignment))

theorem renameFormula_sat {n : Nat} (source : CNFFormula n) :
    CNFSatisfiable (renameFormula source) ↔ CNFSatisfiable source := by
  constructor
  · rintro ⟨assignment, satisfies⟩
    exact ⟨liftAssignment source assignment,
      (renameFormula_eval_lift source assignment).symm ▸ satisfies⟩
  · rintro ⟨assignment, satisfies⟩
    exact ⟨lowerAssignment source assignment,
      (renameFormula_eval_lower source assignment) ▸ satisfies⟩

/-- The dependent input is constructed solely from the original finite source list. -/
def compile {n : Nat} (source : CNFFormula n) : Encoding.Input :=
  ⟨width source, renameFormula source⟩

theorem width_le_literals {n : Nat} (source : CNFFormula n) :
    width source ≤ source.flatten.length := Shared.sourceVars_length_le source

theorem renameClause_length {n : Nat} (source : CNFFormula n)
    (clause : { c : CNFClause n // c ∈ source }) :
    (renameClause source clause).length = clause.val.length := by simp [renameClause]

theorem renameFormula_length {n : Nat} (source : CNFFormula n) :
    (renameFormula source).length = source.length := by simp [renameFormula]

theorem renameFormula_literals {n : Nat} (source : CNFFormula n) :
    (renameFormula source).flatten.length = source.flatten.length := by
  rw [List.length_flatten, List.length_flatten]
  apply congrArg List.sum
  simp only [renameFormula, List.map_map, Function.comp_def, renameClause_length]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- Unary encoding of the dense result has a fixed quadratic bound independent of the old header. -/
theorem encode_compile_length {n : Nat} (source : CNFFormula n) :
    (Encoding.encode (compile source)).length ≤
      (source.flatten.length + 2) * (source.flatten.length + 1) + 2 * source.length := by
  have bounded := Encoding.encode_formula_length_le (renameFormula source)
  rw [renameFormula_length, renameFormula_literals] at bounded
  have widthBound := width_le_literals source
  have multiplied := Nat.mul_le_mul_right source.flatten.length
    (Nat.add_le_add_right widthBound 2)
  change (Encoding.encode (compile source)).length ≤ _ at bounded
  nlinarith

/-- Normalize the actual source, contract aliases, then eliminate accepted source variables. -/
def prepare {n : Nat} (source : CNFFormula n) : CNFFormula (width source) :=
  Eliminate.reduce (Alias.reduce (Subsumption.reduce (renameFormula source)))

theorem prepare_sat {n : Nat} (source : CNFFormula n) :
    CNFSatisfiable (prepare source) ↔ CNFSatisfiable source := by
  have normalized : CNFSatisfiable (Subsumption.reduce (renameFormula source)) ↔
      CNFSatisfiable (renameFormula source) := by
    simp only [CNFSatisfiable, Subsumption.reduce_eval]
  exact (Eliminate.reduce_sat _).trans
    ((Alias.reduce_sat _).trans (normalized.trans (renameFormula_sat source)))

theorem prepare_length_le {n : Nat} (source : CNFFormula n) :
    (prepare source).length ≤ source.length := by
  have bounded := Eliminate.reduce_length_le
    (Alias.reduce (Subsumption.reduce (renameFormula source)))
  rw [Alias.reduce_length] at bounded
  exact bounded.trans ((Subsumption.reduce_length_le _).trans_eq (renameFormula_length source))

theorem prepare_literals_le {n : Nat} (source : CNFFormula n) :
    (prepare source).flatten.length ≤ 2 * width source * source.length := by
  have bounded := Eliminate.literalCount_le_of_clauses (prepare source)
    (Eliminate.reduce_clause_bound _)
  have bound := bounded.trans (Nat.mul_le_mul_left (2 * width source) (prepare_length_le source))
  simpa only [SATJoint.literalCount, List.length_flatten] using bound

theorem encode_prepare_length {n : Nat} (source : CNFFormula n) :
    (Encoding.encode ⟨width source, prepare source⟩).length ≤
      width source + 2 + 2 * source.length + 2 * (width source + 2) * width source * source.length := by
  have bounded := Encoding.encode_formula_length_le (prepare source)
  have clauses := Nat.mul_le_mul_left 2 (prepare_length_le source)
  have literals := Nat.mul_le_mul_left (width source + 2) (prepare_literals_le source)
  nlinarith

/-- The generated source representation is bounded by one fixed polynomial of the original input. -/
theorem parse_prepare_length (bits : List Bool) (input : Encoding.Input)
    (parsed : Encoding.parse bits = some input) :
    (Encoding.encode ⟨width input.2, prepare input.2⟩).length ≤
      (bits.length + 2) * (2 * bits.length ^ 2 + 3) := by
  have sourceSize := Encoding.parse_source_size bits input parsed
  have widthBound : width input.2 ≤ bits.length := (width_le_literals input.2).trans (by omega)
  have clauseBound : input.2.length ≤ bits.length := by omega
  calc
    _ ≤ width input.2 + 2 + 2 * input.2.length +
        2 * (width input.2 + 2) * width input.2 * input.2.length := encode_prepare_length input.2
    _ ≤ bits.length + 2 + 2 * bits.length +
        2 * (bits.length + 2) * bits.length * bits.length := by gcongr
    _ ≤ (bits.length + 2) * (2 * bits.length ^ 2 + 3) := by nlinarith

/-- Run the component decision program on the generated, reduced source. -/
def decideFormula {n : Nat} (source : CNFFormula n) : Bool :=
  Factor.decideFormula (prepare source)

theorem decideFormula_correct {n : Nat} (source : CNFFormula n) :
    decideFormula source = true ↔ CNFSatisfiable source := by
  exact (Factor.decideFormula_correct (prepare source)).trans (prepare_sat source)

theorem decideFormula_no {n : Nat} (source : CNFFormula n) :
    decideFormula source = false ↔ ¬ CNFSatisfiable source := by
  rw [Bool.eq_false_iff]
  exact not_congr (decideFormula_correct source)

end SaturationMonoid.ComplexityProjection.SATSource.Dense

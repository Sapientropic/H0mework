import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Propagation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Table

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Atoms

open InterferenceProgram

def canonical (row : Row) : Row := ⟨row.vars.mergeSort, row.rhs⟩

theorem canonical_holds (row : Row) (assignment : Nat → Bool) :
    (canonical row).holds assignment = row.holds assignment := by
  change (Parity.eval assignment (row.vars.mergeSort) == row.rhs) =
    (Parity.eval assignment row.vars == row.rhs)
  rw [Propagation.parity_perm _ _ (List.mergeSort_perm _ _) assignment]

def data {n : Nat} (basis : List Row) (formula : CNFFormula n) : List (List Row) :=
  formula.map fun clause => clause.map fun literal => canonical (Propagation.residualRow basis literal)

def keys (source : List (List Row)) : List (List Nat) :=
  ([] :: source.flatten.map Row.vars).dedup

theorem zero_present (source : List (List Row)) : [] ∈ keys source := by simp [keys]

theorem row_present (source : List (List Row)) (row : Row) (member : row ∈ source.flatten) :
    row.vars ∈ keys source := by
  apply List.mem_dedup.mpr
  exact List.mem_cons_of_mem [] (List.mem_map.mpr ⟨row, member, rfl⟩)

def table (source : List (List Row)) : Array Row :=
  ((keys source).map (fun terms => (⟨terms, false⟩ : Row))).toArray

def read (source : List (List Row)) (assignment : Nat → Bool) : Nat → Bool :=
  Gates.coordinate (table source) assignment

def address (source : List (List Row)) (terms : List Nat) : Fin (keys source).length :=
  if member : terms ∈ keys source then
    ⟨(keys source).idxOf terms, List.idxOf_lt_length_of_mem member⟩
  else ⟨(keys source).idxOf [], List.idxOf_lt_length_of_mem (zero_present source)⟩

theorem get_address (source : List (List Row)) (terms : List Nat) (member : terms ∈ keys source) :
    (keys source).get (address source terms) = terms := by
  simp only [address, dif_pos member]
  exact List.idxOf_get _

theorem read_address (source : List (List Row)) (terms : List Nat) (member : terms ∈ keys source)
    (assignment : Nat → Bool) :
    read source assignment (address source terms).val = Parity.eval assignment terms := by
  simp only [read, Gates.coordinate, table, List.toList_toArray]
  change Gates.value (((keys source).map (fun key => (⟨key, false⟩ : Row))).getD
    (address source terms).val (⟨[], false⟩ : Row)) assignment = _
  rw [List.getD_map, List.getD_eq_get (keys source) [] (address source terms), get_address source terms member]
  simp only [Gates.value, Row.eval, Bool.false_xor]

def literal (source : List (List Row)) (row : Row) : CNFLiteral (keys source).length :=
  ⟨address source row.vars, !row.rhs⟩

theorem literal_value (source : List (List Row)) (row : Row) (member : row ∈ source.flatten)
    (assignment : Nat → Bool) :
    (literal source row).eval (read source assignment) = !row.holds assignment := by
  simp only [literal, CNFLiteral.eval, read_address source row.vars (row_present source row member) assignment]
  change (if !row.rhs then Parity.eval assignment row.vars else !Parity.eval assignment row.vars) =
    !(Parity.eval assignment row.vars == row.rhs)
  cases row.rhs <;> cases Parity.eval assignment row.vars <;> rfl

def clause (source : List (List Row)) (rows : List Row) : CNFClause (keys source).length :=
  rows.map (literal source)

theorem clause_value (source : List (List Row)) (rows : List Row)
    (inside : ∀ row ∈ rows, row ∈ source.flatten) (assignment : Nat → Bool) :
    CNFClause.eval (clause source rows) (read source assignment) = !holds rows assignment := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      have first := literal_value source row (inside row (by simp)) assignment
      have tail := ih (fun value member => inside value (by simp [member]))
      simp only [clause, List.map_cons, CNFClause.eval, List.any_cons] at *
      simp only [first, tail, holds, List.all_cons, Bool.not_and]

def compile (source : List (List Row)) : CNFFormula (keys source).length :=
  [⟨address source [], false⟩] :: source.map (clause source)

/-- The atom coordinates are read from their actual source forms, including the fixed zero atom. -/
theorem compile_value (source : List (List Row)) (assignment : Nat → Bool) :
    CNFFormula.eval (compile source) (read source assignment) =
      source.all (fun rows => !holds rows assignment) := by
  simp only [compile, CNFFormula.eval, List.all_cons, CNFClause.eval, List.any_cons, CNFLiteral.eval,
    Bool.false_eq_true, if_false, List.any_nil, Bool.or_false,
    read_address source [] (zero_present source) assignment, Parity.eval, Bool.not_false, Bool.true_and,
    List.all_map]
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  apply forall_congr'
  intro rows
  apply imp_congr_right
  intro member
  change (CNFClause.eval (clause source rows) (read source assignment) = true) ↔ _
  rw [clause_value source rows (fun row hit => List.mem_flatten.mpr ⟨rows, member, hit⟩) assignment]

theorem data_clause_holds {n : Nat} (basis : List Row) (original : CNFClause n)
    (assignment : Nat → Bool) (accepted : holds basis assignment = true) :
    holds (original.map (fun lit => canonical (Propagation.residualRow basis lit))) assignment =
      !CNFClause.eval original assignment := by
  rw [← Propagation.residual_clause basis original assignment accepted]
  simp only [holds, List.all_map]
  apply List.all_congr rfl
  intro literal
  exact canonical_holds _ assignment

def ofFormula {n : Nat} (basis : List Row) (formula : CNFFormula n) :=
  Subsumption.reduce (compile (data basis formula))

theorem ofFormula_value {n : Nat} (basis : List Row) (formula : CNFFormula n)
    (assignment : Nat → Bool) (accepted : holds basis assignment = true) :
    CNFFormula.eval (ofFormula basis formula) (read (data basis formula) assignment) =
      CNFFormula.eval formula assignment := by
  rw [ofFormula, Subsumption.reduce_eval, compile_value]
  simp only [data, List.all_map, CNFFormula.eval]
  apply List.all_congr rfl
  intro original
  change (!holds (original.map (fun lit => canonical (Propagation.residualRow basis lit))) assignment) = _
  rw [data_clause_holds basis original assignment accepted, Bool.not_not]

theorem holds_not_value (row : Row) (assignment : Nat → Bool) :
    row.holds assignment = !Gates.value row assignment := by
  change (row.eval assignment == row.rhs) = !(row.rhs ^^ row.eval assignment)
  cases row.eval assignment <;> cases row.rhs <;> rfl

def decode (source : List (List Row)) (row : Row) : Row :=
  Table.combine (table source) row.vars ⟨[], row.rhs⟩

theorem decode_holds (source : List (List Row)) (row : Row) (assignment : Nat → Bool) :
    (decode source row).holds assignment = row.holds (read source assignment) := by
  rw [holds_not_value, holds_not_value, decode, Table.combine_value]
  simp only [Gates.value, Row.eval, Parity.eval, Bool.xor_false, read]

def unitRows {n : Nat} (formula : CNFFormula n) : List Row :=
  formula.flatMap fun clause => match clause with
    | [] => [⟨[], true⟩]
    | [lit] => [⟨[lit.var.val], lit.positive⟩]
    | _ :: _ :: _ => []

theorem unitRows_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : holds (unitRows formula) assignment = true := by
  apply (holds_iff _ _).mpr
  intro row member
  obtain ⟨clause, inFormula, member⟩ := List.mem_flatMap.mp member
  have clauseTrue := List.all_eq_true.mp accepted clause inFormula
  cases clause with
  | nil => simp [CNFClause.eval] at clauseTrue
  | cons lit rest =>
      cases rest with
      | nil =>
          have same : row = ⟨[lit.var.val], lit.positive⟩ := by simpa using member
          subst row
          cases value : assignment lit.var.val <;> cases polarity : lit.positive <;>
            simp_all [Row.holds, Row.eval, Parity.eval, CNFClause.eval, CNFLiteral.eval]
      | cons next tail => simp at member

def equations {n : Nat} (formula : CNFFormula n) : List Row := unitRows formula ++ Extract.extract formula

theorem equations_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : holds (equations formula) assignment = true := by
  have units := unitRows_entails formula assignment accepted
  have extracted := Extract.extract_entails formula assignment accepted
  simp only [equations, holds, List.all_append]
  change (holds (unitRows formula) assignment && holds (Extract.extract formula) assignment) = true
  rw [units, extracted]
  rfl

def learn {n : Nat} (basis : List Row) (formula : CNFFormula n) : List Row :=
  let source := data basis formula
  let normalized := Subsumption.reduce (compile source)
  (equations normalized).map (decode source)

theorem learn_entails {n : Nat} (basis : List Row) (formula : CNFFormula n)
    (assignment : Nat → Bool) (relations : holds basis assignment = true)
    (accepted : CNFFormula.eval formula assignment = true) : holds (learn basis formula) assignment = true := by
  have truth : CNFFormula.eval (ofFormula basis formula) (read (data basis formula) assignment) = true :=
    (ofFormula_value basis formula assignment relations).trans accepted
  have generated := equations_entails _ _ truth
  apply (holds_iff _ _).mpr
  intro row member
  obtain ⟨original, hit, rfl⟩ := List.mem_map.mp member
  rw [decode_holds]
  exact ((holds_iff _ _).mp generated) original hit

theorem data_valid {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    ∀ row ∈ (data basis formula).flatten, Table.RowValid n row := by
  intro row member
  obtain ⟨rows, rowsMember, rowMember⟩ := List.mem_flatten.mp member
  obtain ⟨clause, _, rfl⟩ := List.mem_map.mp rowsMember
  obtain ⟨literal, _, rfl⟩ := List.mem_map.mp rowMember
  have permutation := List.mergeSort_perm (Propagation.residualRow basis literal).vars (fun a b => a ≤ b)
  refine ⟨permutation.nodup_iff.mpr (Row.normalize_nodup _), ?_⟩
  intro i hit
  exact Propagation.residualRow_within basis inside literal i (permutation.mem_iff.mp hit)

theorem table_valid (n : Nat) (source : List (List Row))
    (valid : ∀ row ∈ source.flatten, Table.RowValid n row) : Table.Valid n (table source) := by
  intro row member
  simp only [table, List.toList_toArray, List.mem_map] at member
  obtain ⟨terms, member, rfl⟩ := member
  simp only [keys, List.mem_dedup, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨original, hit, rfl⟩
  · simp [Table.RowValid, Parity.Within]
  · exact valid original hit

theorem learn_valid {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    ∀ row ∈ learn basis formula, Table.RowValid n row := by
  intro row member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact Table.combine_valid n (table (data basis formula)) (table_valid n _ (data_valid basis inside formula))
    original.vars _ (by simp [Table.RowValid, Parity.Within])

theorem keys_length (source : List (List Row)) : (keys source).length ≤ source.flatten.length + 1 := by
  have bound := (List.dedup_sublist ([] :: source.flatten.map Row.vars)).length_le
  simpa only [keys, List.length_cons, List.length_map] using bound

theorem data_length {n : Nat} (basis : List Row) (formula : CNFFormula n) : (data basis formula).length = formula.length := by
  simp [data]

theorem data_literals {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (data basis formula).flatten.length = formula.flatten.length := by
  simp only [data, List.length_flatten, List.map_map, List.length_map, Function.comp_def]

theorem atom_count {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (keys (data basis formula)).length ≤ formula.flatten.length + 1 := by
  simpa only [data_literals] using keys_length (data basis formula)

theorem compile_length (source : List (List Row)) : (compile source).length = source.length + 1 := by
  simp [compile]

theorem unitRows_length {n : Nat} (formula : CNFFormula n) : (unitRows formula).length ≤ formula.length := by
  induction formula with
  | nil => simp [unitRows]
  | cons clause rest ih =>
      cases clause with
      | nil => simpa [unitRows] using Nat.add_le_add_left ih 1
      | cons lit tail =>
          cases tail with
          | nil => simpa [unitRows] using Nat.add_le_add_left ih 1
          | cons next tail => simpa [unitRows] using ih.trans (Nat.le_succ _)

theorem equations_length {n : Nat} (formula : CNFFormula n) : (equations formula).length ≤ 2 * formula.length := by
  have units := unitRows_length formula
  have rows := Extract.extract_length formula
  simp only [equations, List.length_append]
  omega

theorem learn_length {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (learn basis formula).length ≤ 2 * (formula.length + 1) := by
  have reduced := Subsumption.reduce_length_le (compile (data basis formula))
  simp only [compile_length, data_length] at reduced
  simp only [learn, List.length_map]
  exact (equations_length (Subsumption.reduce (compile (data basis formula)))).trans
    (Nat.mul_le_mul_left 2 reduced)

def advance {n : Nat} (formula : CNFFormula n) : Result → Result
  | .contradiction => .contradiction
  | .basis basis => eliminateFrom (.basis basis) (learn basis formula)

theorem advance_entailed {n : Nat} (formula : CNFFormula n) (result : Result)
    (entailed : Propagation.Entailed formula result) : Propagation.Entailed formula (advance formula result) := by
  intro assignment accepted
  have relations := entailed assignment accepted
  cases result with
  | contradiction => exact relations
  | basis basis =>
      rw [advance, eliminateFrom_holds, relations, learn_entails basis formula assignment relations accepted]
      rfl

theorem advance_invariants {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (advance formula result).within n ∧ (advance formula result).triangular := by
  cases result with
  | contradiction => exact ⟨trivial, trivial⟩
  | basis basis =>
      have consume : ∀ rows : List Row, RowsWithin n rows →
          (eliminateFrom (.basis basis) rows).within n ∧
            (eliminateFrom (.basis basis) rows).triangular := by
        intro rows bounded
        exact ⟨eliminateFrom_within n (.basis basis) inside rows bounded,
          eliminateFrom_triangular (.basis basis) triangular rows⟩
      exact consume (learn basis formula) (fun row member => (learn_valid basis inside formula row member).2)

def Retains (old : List Row) : Result → Prop
  | .contradiction => True
  | .basis current => old.IsPrefix current

theorem insert_retains (old : List Row) (result : Result) (retained : Retains old result) (row : Row) :
    Retains old (result.insert row) := by
  cases result with
  | contradiction => trivial
  | basis current =>
      cases reduced : reduceWith current row.normalize with
      | mk vars rhs =>
          cases vars with
          | nil => cases rhs <;> simp only [Result.insert, reduced, Retains] <;> trivial
          | cons p rest =>
              simp only [Result.insert, reduced, Retains]
              exact List.prefix_append_of_prefix retained

theorem eliminateFrom_retains (old : List Row) (result : Result) (retained : Retains old result)
    (rows : List Row) : Retains old (eliminateFrom result rows) := by
  induction rows generalizing result with
  | nil => exact retained
  | cons row rest ih => exact ih _ (insert_retains old result retained row)

theorem eliminateFrom_prefix (basis rows current : List Row)
    (produced : eliminateFrom (.basis basis) rows = .basis current) : basis.IsPrefix current := by
  have retained := eliminateFrom_retains basis (.basis basis) ⟨[], by simp⟩ rows
  rw [produced] at retained
  exact retained

theorem advance_retains {n : Nat} (formula : CNFFormula n) (basis current : List Row)
    (produced : advance formula (.basis basis) = .basis current) : basis.IsPrefix current :=
  eliminateFrom_prefix basis (learn basis formula) current produced

theorem advance_progress {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (changed : advance formula result ≠ result) :
    Propagation.remaining n (advance formula result) < Propagation.remaining n result := by
  cases result with
  | contradiction => exact False.elim (changed rfl)
  | basis basis =>
      have rank := basis_length_le n basis triangular inside
      have consume : ∀ next : Result, (∀ current, next = .basis current → basis.IsPrefix current) → next ≠ .basis basis →
          Propagation.remaining n next < Propagation.remaining n (.basis basis) := by
        intro next retained different
        cases next with
        | contradiction => simp only [Propagation.remaining]; omega
        | basis current =>
            have pref : basis.IsPrefix current := retained current rfl
            have apart : basis ≠ current := fun same => different (congrArg Result.basis same.symm)
            have growth : basis.length < current.length := by
              by_contra! absent
              exact apart (pref.eq_of_length_le absent)
            simp only [Propagation.remaining]
            omega
      exact consume (advance formula (.basis basis)) (advance_retains formula basis) changed

def iterate {n : Nat} (formula : CNFFormula n) : Nat → Result → Result
  | 0, result => result
  | fuel+1, result => iterate formula fuel (advance formula result)

theorem iterate_entailed {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (entailed : Propagation.Entailed formula result) : Propagation.Entailed formula (iterate formula fuel result) := by
  induction fuel generalizing result with
  | zero => exact entailed
  | succ fuel ih => exact ih _ (advance_entailed formula result entailed)

theorem iterate_invariants {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (iterate formula fuel result).within n ∧ (iterate formula fuel result).triangular := by
  induction fuel generalizing result with
  | zero => exact ⟨inside, triangular⟩
  | succ fuel ih =>
      have next := advance_invariants formula result inside triangular
      exact ih _ next.1 next.2

theorem iterate_fixed {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (fixed : advance formula result = result) : iterate formula fuel result = result := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [iterate, fixed] using ih

theorem iterate_settled {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular)
    (enough : Propagation.remaining n result ≤ fuel) :
    advance formula (iterate formula fuel result) = iterate formula fuel result := by
  induction fuel generalizing result with
  | zero =>
      cases result with
      | contradiction => rfl
      | basis basis =>
          have rank := basis_length_le n basis triangular inside
          simp only [Propagation.remaining] at enough
          omega
  | succ fuel ih =>
      by_cases fixed : advance formula result = result
      · rw [iterate_fixed formula (fuel+1) result fixed]
        exact fixed
      · have progress := advance_progress formula result inside triangular fixed
        have next := advance_invariants formula result inside triangular
        exact ih _ next.1 next.2 (by omega)

def generate {n : Nat} (formula : CNFFormula n) : Result :=
  iterate formula (n+1) (Propagation.generate formula)

theorem generate_entailed {n : Nat} (formula : CNFFormula n) : Propagation.Entailed formula (generate formula) :=
  iterate_entailed formula (n+1) _ (Propagation.generate_entailed formula)

theorem generate_invariants {n : Nat} (formula : CNFFormula n) :
    (generate formula).within n ∧ (generate formula).triangular :=
  iterate_invariants formula (n+1) _ (Propagation.generate_invariants formula).1
    (Propagation.generate_invariants formula).2

theorem generate_settled {n : Nat} (formula : CNFFormula n) :
    advance formula (generate formula) = generate formula := by
  apply iterate_settled formula (n+1) _ (Propagation.generate_invariants formula).1
    (Propagation.generate_invariants formula).2
  cases Propagation.generate formula <;> simp only [Propagation.remaining] <;> omega

theorem generated_within {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : generate formula = .basis basis) : RowsWithin n basis := by
  have result := (generate_invariants formula).1
  simpa only [generated, Result.within] using result

theorem generated_triangular {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : generate formula = .basis basis) : Triangular basis := by
  have result := (generate_invariants formula).2
  simpa only [generated, Result.triangular] using result

theorem generated_dimension {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : generate formula = .basis basis) : (freeIndices n basis).length + basis.length = n :=
  freeIndices_dimension n basis (generated_triangular formula basis generated)
    (generated_within formula basis generated)

theorem generated_relations {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : generate formula = .basis basis) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : holds basis assignment = true := by
  have result := generate_entailed formula assignment accepted
  simpa only [generated, Result.holds] using result

theorem generated_contradiction_eval {n : Nat} (formula : CNFFormula n)
    (generated : generate formula = .contradiction) (assignment : Nat → Bool) :
    CNFFormula.eval formula assignment = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have result := generate_entailed formula assignment accepted
  simp only [generated, Result.holds, Bool.false_eq_true] at result

theorem satisfiable_iff_free {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : generate formula = .basis basis) :
    CNFSatisfiable formula ↔ ∃ parameters : Assignment (freeIndices n basis).length,
      CNFFormula.eval formula (extendAssignment (parameterLift n basis parameters)) = true := by
  rw [satisfiable_iff_finite_assignment]
  constructor
  · rintro ⟨assignment, accepted⟩
    have relations := generated_relations formula basis generated (extendAssignment assignment) accepted
    have recovery := parameterLift_projectFree n basis (generated_triangular formula basis generated) assignment relations
    exact ⟨projectFree n basis assignment, by simpa only [recovery] using accepted⟩
  · rintro ⟨parameters, accepted⟩
    exact ⟨parameterLift n basis parameters, accepted⟩

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Atoms

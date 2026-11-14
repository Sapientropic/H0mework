import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Lift

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Propagation

open InterferenceProgram

theorem parity_perm (left right : List Nat) (permutation : left.Perm right) (assignment : Nat → Bool) :
    Parity.eval assignment left = Parity.eval assignment right := by
  induction permutation with
  | nil => rfl
  | cons i _ ih => simp only [Parity.eval, ih]
  | swap i j rest => simp only [Parity.eval, Bool.xor_left_comm]
  | trans _ _ first second => exact first.trans second

def flip (row : Row) : Row := ⟨row.vars, !row.rhs⟩

theorem flip_holds (row : Row) (assignment : Nat → Bool) :
    (flip row).holds assignment = !row.holds assignment := by
  change (row.eval assignment == !row.rhs) = !(row.eval assignment == row.rhs)
  cases row.eval assignment <;> cases row.rhs <;> rfl

def badLiteral {n : Nat} (literal : CNFLiteral n) : Row := ⟨[literal.var.val], !literal.positive⟩

theorem badLiteral_holds {n : Nat} (literal : CNFLiteral n) (assignment : Nat → Bool) :
    (badLiteral literal).holds assignment = !CNFLiteral.eval literal assignment := by
  simp only [badLiteral, Row.holds, Row.eval, Parity.eval, Bool.xor_false, CNFLiteral.eval]
  cases assignment literal.var.val <;> cases literal.positive <;> rfl

def residualRow {n : Nat} (basis : List Row) (literal : CNFLiteral n) : Row :=
  (reduceWith basis (badLiteral literal)).normalize

theorem residualRow_holds {n : Nat} (basis : List Row) (literal : CNFLiteral n)
    (assignment : Nat → Bool) (accepted : holds basis assignment = true) :
    (residualRow basis literal).holds assignment = !CNFLiteral.eval literal assignment := by
  rw [residualRow, Row.normalize_holds, reduceWith_holds basis _ assignment accepted, badLiteral_holds]

theorem residual_clause {n : Nat} (basis : List Row) (clause : CNFClause n)
    (assignment : Nat → Bool) (accepted : holds basis assignment = true) :
    holds (clause.map (residualRow basis)) assignment = !CNFClause.eval clause assignment := by
  induction clause with
  | nil => rfl
  | cons literal rest ih =>
      simp only [List.map_cons, holds, List.all_cons, residualRow_holds basis literal assignment accepted,
        CNFClause.eval, List.any_cons, Bool.not_or]
      exact congrArg (fun b => !CNFLiteral.eval literal assignment && b) ih

inductive Reading where
  | satisfied
  | contradiction
  | forced : Row → Reading
  | unresolved
  deriving Repr

def scan (pivot : Option Row) : List Row → Reading
  | [] => match pivot with
    | none => .contradiction
    | some row => .forced (flip row)
  | row :: rest =>
      if row.vars = [] then
        if row.rhs then .satisfied else scan pivot rest
      else match pivot with
        | none => scan (some row) rest
        | some first =>
            if row.vars.isPerm first.vars then
              if row.rhs = first.rhs then scan pivot rest else .satisfied
            else .unresolved

def pending (pivot : Option Row) (rows : List Row) (assignment : Nat → Bool) : Bool :=
  (pivot.map (fun row => row.holds assignment)).getD true && holds rows assignment

def Reading.Sound (reading : Reading) (value : Bool) (assignment : Nat → Bool) : Prop :=
  match reading with
  | .satisfied => value = false
  | .contradiction => value = true
  | .forced row => value = !row.holds assignment
  | .unresolved => True

theorem same_vars_holds (left right : Row) (same : left.vars.isPerm right.vars = true)
    (assignment : Nat → Bool) :
    left.holds assignment = if left.rhs = right.rhs then right.holds assignment else !right.holds assignment := by
  have value := parity_perm left.vars right.vars (List.isPerm_iff.mp same) assignment
  change (Parity.eval assignment left.vars == left.rhs) = _
  rw [value]
  change (right.eval assignment == left.rhs) = _
  unfold Row.holds
  cases left.rhs <;> cases right.rhs <;> cases right.eval assignment <;> rfl

theorem scan_sound (rows : List Row) (pivot : Option Row) (assignment : Nat → Bool) :
    (scan pivot rows).Sound (pending pivot rows assignment) assignment := by
  induction rows generalizing pivot with
  | nil =>
      cases pivot with
      | none => rfl
      | some row => simp [scan, Reading.Sound, pending, holds, flip_holds]
  | cons row rest ih =>
      by_cases empty : row.vars = []
      · cases rhs : row.rhs with
        | false =>
            have value : row.holds assignment = true := by simp [Row.holds, Row.eval, empty, Parity.eval, rhs]
            simpa only [scan, if_pos empty, rhs, Bool.false_eq_true, if_false,
              pending, holds, List.all_cons, value, Bool.true_and] using ih pivot
        | true =>
            simp [scan, empty, rhs, Reading.Sound, pending, holds, Row.holds, Row.eval, Parity.eval]
      · cases pivot with
        | none =>
            simpa only [scan, if_neg empty, pending, Option.map_none, Option.getD_none,
              Option.map_some, Option.getD_some, Bool.true_and, holds, List.all_cons] using ih (some row)
        | some first =>
            by_cases same : row.vars.isPerm first.vars = true
            · have value := same_vars_holds row first same assignment
              by_cases rhs : row.rhs = first.rhs
              · simp only [if_pos rhs] at value
                simpa only [scan, if_neg empty, if_pos same, if_pos rhs, pending, Option.map_some,
                  Option.getD_some, holds, List.all_cons, value, ← Bool.and_assoc, Bool.and_self] using ih (some first)
              · simp only [if_neg rhs] at value
                simp only [scan, if_neg empty, if_pos same, if_neg rhs, Reading.Sound, pending,
                  Option.map_some, Option.getD_some, holds, List.all_cons, value, ← Bool.and_assoc,
                  Bool.and_not_self, Bool.false_and]
            · simp only [scan, if_neg empty, if_neg same, Reading.Sound]

def inspect {n : Nat} (basis : List Row) (clause : CNFClause n) : Reading :=
  scan none (clause.map (residualRow basis))

theorem inspect_sound {n : Nat} (basis : List Row) (clause : CNFClause n) (assignment : Nat → Bool)
    (accepted : holds basis assignment = true) :
    (inspect basis clause).Sound (!CNFClause.eval clause assignment) assignment := by
  have sound := scan_sound (clause.map (residualRow basis)) none assignment
  simp only [pending, Option.map_none, Option.getD_none, Bool.true_and,
    residual_clause basis clause assignment accepted] at sound
  exact sound

theorem inspect_forced {n : Nat} (basis : List Row) (clause : CNFClause n) (row : Row)
    (generated : inspect basis clause = .forced row) (assignment : Nat → Bool)
    (relations : holds basis assignment = true) (accepted : CNFClause.eval clause assignment = true) :
    row.holds assignment = true := by
  have sound := inspect_sound basis clause assignment relations
  rw [generated] at sound
  change (!CNFClause.eval clause assignment) = (!row.holds assignment) at sound
  rw [accepted] at sound
  simpa using sound.symm

theorem inspect_contradiction {n : Nat} (basis : List Row) (clause : CNFClause n)
    (generated : inspect basis clause = .contradiction) (assignment : Nat → Bool)
    (relations : holds basis assignment = true) : CNFClause.eval clause assignment = false := by
  have sound := inspect_sound basis clause assignment relations
  rw [generated] at sound
  change (!CNFClause.eval clause assignment) = true at sound
  simpa using sound

def find {n : Nat} (basis : List Row) : CNFFormula n → Reading
  | [] => .unresolved
  | clause :: rest => match inspect basis clause with
    | .forced row => .forced row
    | .contradiction => .contradiction
    | _ => find basis rest

theorem find_forced {n : Nat} (basis : List Row) (formula : CNFFormula n) (row : Row)
    (generated : find basis formula = .forced row) (assignment : Nat → Bool)
    (relations : holds basis assignment = true) (accepted : CNFFormula.eval formula assignment = true) :
    row.holds assignment = true := by
  induction formula with
  | nil => simp [find] at generated
  | cons clause rest ih =>
      have conjunction : CNFClause.eval clause assignment = true ∧ CNFFormula.eval rest assignment = true := by
        simpa only [CNFFormula.eval, List.all_cons, Bool.and_eq_true] using accepted
      cases inspected : inspect basis clause with
      | satisfied => exact ih (by simpa [find, inspected] using generated) conjunction.2
      | contradiction => simp [find, inspected] at generated
      | forced learned =>
          have same : learned = row := by simpa only [find, inspected, Reading.forced.injEq] using generated
          exact inspect_forced basis clause row (same ▸ inspected) assignment relations conjunction.1
      | unresolved => exact ih (by simpa [find, inspected] using generated) conjunction.2

theorem find_contradiction {n : Nat} (basis : List Row) (formula : CNFFormula n)
    (generated : find basis formula = .contradiction) (assignment : Nat → Bool)
    (relations : holds basis assignment = true) : CNFFormula.eval formula assignment = false := by
  induction formula with
  | nil => simp [find] at generated
  | cons clause rest ih =>
      cases inspected : inspect basis clause with
      | satisfied =>
          change (CNFClause.eval clause assignment && CNFFormula.eval rest assignment) = false
          rw [ih (by simpa [find, inspected] using generated), Bool.and_false]
      | contradiction =>
          simp [CNFFormula.eval, inspect_contradiction basis clause inspected assignment relations]
      | forced row => simp [find, inspected] at generated
      | unresolved =>
          change (CNFClause.eval clause assignment && CNFFormula.eval rest assignment) = false
          rw [ih (by simpa [find, inspected] using generated), Bool.and_false]

def update {n : Nat} (formula : CNFFormula n) : Result → Result
  | .contradiction => .contradiction
  | .basis basis => match find basis formula with
    | .contradiction => .contradiction
    | .forced row => (Result.basis basis).insert row
    | _ => .basis basis

def Entailed {n : Nat} (formula : CNFFormula n) (result : Result) : Prop :=
  ∀ assignment, CNFFormula.eval formula assignment = true → result.holds assignment = true

theorem update_entailed {n : Nat} (formula : CNFFormula n) (result : Result)
    (entailed : Entailed formula result) : Entailed formula (update formula result) := by
  intro assignment accepted
  have relations := entailed assignment accepted
  cases result with
  | contradiction => exact relations
  | basis basis =>
      cases generated : find basis formula with
      | satisfied => simpa only [update, generated] using relations
      | contradiction =>
          have impossible := find_contradiction basis formula generated assignment relations
          rw [accepted] at impossible
          exact Bool.noConfusion impossible
      | forced row =>
          have learned := find_forced basis formula row generated assignment relations accepted
          simp only [update, generated, Result.insert_holds, relations, learned, Bool.and_self]
      | unresolved => simpa only [update, generated] using relations

def iterate {n : Nat} (formula : CNFFormula n) : Nat → Result → Result
  | 0, result => result
  | fuel+1, result => iterate formula fuel (update formula result)

theorem iterate_entailed {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (entailed : Entailed formula result) : Entailed formula (iterate formula fuel result) := by
  induction fuel generalizing result with
  | zero => exact entailed
  | succ fuel ih => exact ih _ (update_entailed formula result entailed)

def generate {n : Nat} (formula : CNFFormula n) : Result :=
  iterate formula (n+1) (eliminate (Extract.extract formula))

theorem generate_entailed {n : Nat} (formula : CNFFormula n) : Entailed formula (generate formula) :=
  iterate_entailed formula (n+1) _ (fun assignment accepted => by
    rw [eliminate_holds]
    exact Extract.extract_entails formula assignment accepted)

theorem scan_forced_property (rows : List Row) (pivot : Option Row) (property : Row → Prop)
    (known : ∀ row ∈ pivot.toList ++ rows, property (flip row)) (target : Row)
    (generated : scan pivot rows = .forced target) : property target := by
  induction rows generalizing pivot with
  | nil =>
      cases pivot with
      | none => simp [scan] at generated
      | some row =>
          have same : flip row = target := by simpa [scan] using generated
          exact same ▸ known row (by simp)
  | cons row rest ih =>
      have tail : ∀ value ∈ pivot.toList ++ rest, property (flip value) := by
        intro value member
        apply known value
        simp only [List.mem_append, List.mem_cons] at *
        rcases member with member | member
        · exact Or.inl member
        · exact Or.inr (Or.inr member)
      by_cases empty : row.vars = []
      · cases rhs : row.rhs with
        | false => exact ih pivot tail (by simpa [scan, empty, rhs] using generated)
        | true => simp [scan, empty, rhs] at generated
      · cases pivot with
        | none => exact ih (some row) (by simpa using known) (by simpa [scan, empty] using generated)
        | some first =>
            by_cases same : row.vars.isPerm first.vars = true
            · by_cases rhs : row.rhs = first.rhs
              · exact ih (some first) tail (by simpa [scan, empty, same, rhs] using generated)
              · simp [scan, empty, same, rhs] at generated
            · simp [scan, empty, same] at generated

theorem badLiteral_within {n : Nat} (literal : CNFLiteral n) : Parity.Within n (badLiteral literal).vars := by
  intro i member
  have same : i = literal.var.val := by simpa only [badLiteral, List.mem_singleton] using member
  exact same ▸ literal.var.isLt

theorem residualRow_within {n : Nat} (basis : List Row) (inside : RowsWithin n basis)
    (literal : CNFLiteral n) : Parity.Within n (residualRow basis literal).vars :=
  Row.normalize_within n _ (reduceWith_within n basis inside _ (badLiteral_within literal))

theorem inspect_forced_within {n : Nat} (basis : List Row) (inside : RowsWithin n basis)
    (clause : CNFClause n) (row : Row) (generated : inspect basis clause = .forced row) :
    Parity.Within n row.vars := by
  apply scan_forced_property (clause.map (residualRow basis)) none (fun value => Parity.Within n value.vars) _ row generated
  intro value member
  simp only [Option.toList_none, List.nil_append, List.mem_map] at member
  obtain ⟨literal, _, rfl⟩ := member
  exact residualRow_within basis inside literal

theorem find_forced_origin {n : Nat} (basis : List Row) (formula : CNFFormula n) (row : Row)
    (generated : find basis formula = .forced row) :
    ∃ clause ∈ formula, inspect basis clause = .forced row := by
  induction formula with
  | nil => simp [find] at generated
  | cons clause rest ih =>
      cases inspected : inspect basis clause with
      | satisfied =>
          obtain ⟨source, member, hit⟩ := ih (by simpa [find, inspected] using generated)
          exact ⟨source, by simp [member], hit⟩
      | contradiction => simp [find, inspected] at generated
      | forced learned =>
          have same : learned = row := by simpa [find, inspected] using generated
          exact ⟨clause, by simp, same ▸ inspected⟩
      | unresolved =>
          obtain ⟨source, member, hit⟩ := ih (by simpa [find, inspected] using generated)
          exact ⟨source, by simp [member], hit⟩

theorem update_within {n : Nat} (formula : CNFFormula n) (result : Result) (inside : result.within n) :
    (update formula result).within n := by
  cases result with
  | contradiction => trivial
  | basis basis =>
      cases generated : find basis formula with
      | satisfied => simpa only [update, generated] using inside
      | contradiction => simp only [update, generated, Result.within]
      | forced row =>
          obtain ⟨clause, _, hit⟩ := find_forced_origin basis formula row generated
          simpa only [update, generated] using Result.insert_within n (.basis basis) inside row
            (inspect_forced_within basis inside clause row hit)
      | unresolved => simpa only [update, generated] using inside

theorem update_triangular {n : Nat} (formula : CNFFormula n) (result : Result)
    (triangular : result.triangular) : (update formula result).triangular := by
  cases result with
  | contradiction => trivial
  | basis basis =>
      cases generated : find basis formula with
      | satisfied => simpa only [update, generated] using triangular
      | contradiction => simp only [update, generated, Result.triangular]
      | forced row => simpa only [update, generated] using Result.insert_triangular (.basis basis) triangular row
      | unresolved => simpa only [update, generated] using triangular

theorem iterate_invariants {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    (iterate formula fuel result).within n ∧ (iterate formula fuel result).triangular := by
  induction fuel generalizing result with
  | zero => exact ⟨inside, triangular⟩
  | succ fuel ih => exact ih _ (update_within formula result inside) (update_triangular formula result triangular)

theorem generate_invariants {n : Nat} (formula : CNFFormula n) :
    (generate formula).within n ∧ (generate formula).triangular :=
  iterate_invariants formula (n+1) _
    (eliminate_within n _ (extract_rowsWithin formula)) (eliminate_triangular _)

theorem normalize_vars_perm (row : Row) (nodup : row.vars.Nodup) : row.normalize.vars.Perm row.vars := by
  apply (List.perm_ext_iff_of_nodup row.normalize_nodup nodup).mpr
  intro p
  have value := row.normalize_eval (fun i => decide (i = p))
  change Parity.eval (fun i => decide (i = p)) row.normalize.vars =
    Parity.eval (fun i => decide (i = p)) row.vars at value
  rw [eval_delta _ p row.normalize_nodup, eval_delta _ p nodup] at value
  simpa using Bool.eq_iff_iff.mp value

theorem residualRow_erases {n : Nat} (basis : List Row) (triangular : Triangular basis)
    (literal : CNFLiteral n) (old : Row) (member : old ∈ basis) (p : Nat)
    (head : old.vars.head? = some p) : p ∉ (residualRow basis literal).vars := by
  have initial : (badLiteral literal).vars.Nodup := by simp [badLiteral]
  have reduced := reduceWith_nodup basis triangular.1 (badLiteral literal) initial
  have absent := reduceWith_erases basis triangular (badLiteral literal) initial old member p head
  exact fun hit => absent ((normalize_vars_perm _ reduced).mem_iff.mp hit)

theorem scan_forced_nonempty (rows : List Row) (pivot : Option Row)
    (valid : ∀ row ∈ pivot, row.vars ≠ []) (target : Row)
    (generated : scan pivot rows = .forced target) : target.vars ≠ [] := by
  induction rows generalizing pivot with
  | nil =>
      cases pivot with
      | none => simp [scan] at generated
      | some row =>
          have same : flip row = target := by simpa [scan] using generated
          simpa only [← same, flip] using valid row (by simp)
  | cons row rest ih =>
      by_cases empty : row.vars = []
      · cases rhs : row.rhs with
        | false => exact ih pivot valid (by simpa [scan, empty, rhs] using generated)
        | true => simp [scan, empty, rhs] at generated
      · cases pivot with
        | none =>
            apply ih (some row) _ (by simpa [scan, empty] using generated)
            intro other member
            have same : row = other := by simpa using member
            exact same ▸ empty
        | some first =>
            by_cases same : row.vars.isPerm first.vars = true
            · by_cases rhs : row.rhs = first.rhs
              · exact ih (some first) valid (by simpa [scan, empty, same, rhs] using generated)
              · simp [scan, empty, same, rhs] at generated
            · simp [scan, empty, same] at generated

theorem inspect_forced_geometry {n : Nat} (basis : List Row) (triangular : Triangular basis)
    (clause : CNFClause n) (row : Row) (generated : inspect basis clause = .forced row) :
    row.vars.Nodup ∧ row.vars ≠ [] ∧ ∀ old ∈ basis, ∀ p,
      old.vars.head? = some p → p ∉ row.vars := by
  refine ⟨?_, scan_forced_nonempty _ none (by simp) row generated, ?_⟩
  · apply scan_forced_property (clause.map (residualRow basis)) none (fun value => value.vars.Nodup) _ row generated
    intro value member
    simp only [Option.toList_none, List.nil_append, List.mem_map] at member
    obtain ⟨literal, _, rfl⟩ := member
    exact Row.normalize_nodup _
  · intro old member p head
    apply scan_forced_property (clause.map (residualRow basis)) none (fun value => p ∉ value.vars) _ row generated
    intro value hit
    simp only [Option.toList_none, List.nil_append, List.mem_map] at hit
    obtain ⟨literal, _, rfl⟩ := hit
    exact residualRow_erases basis triangular literal old member p head

theorem reduceWith_unchanged (basis : List Row) (row : Row)
    (erased : ∀ old ∈ basis, ∀ p, old.vars.head? = some p → p ∉ row.vars) :
    reduceWith basis row = row := by
  induction basis with
  | nil => rfl
  | cons old rest ih =>
      have tail : ∀ prior ∈ rest, ∀ p, prior.vars.head? = some p → p ∉ row.vars :=
        fun prior member => erased prior (by simp [member])
      cases shape : old.vars with
      | nil => simpa only [reduceWith, List.foldl_cons, shape] using ih tail
      | cons p vars =>
          have absent := erased old (by simp) p (by simp [shape])
          simpa only [reduceWith, List.foldl_cons, shape, if_neg absent] using ih tail

theorem forced_insert (basis : List Row) (row : Row) (nodup : row.vars.Nodup) (nonempty : row.vars ≠ [])
    (erased : ∀ old ∈ basis, ∀ p, old.vars.head? = some p → p ∉ row.vars) :
    (Result.basis basis).insert row = .basis (basis ++ [row.normalize]) := by
  have permutation := normalize_vars_perm row nodup
  have absent : ∀ old ∈ basis, ∀ p, old.vars.head? = some p → p ∉ row.normalize.vars :=
    fun old member p head hit => erased old member p head (permutation.mem_iff.mp hit)
  have normalizedNonempty : row.normalize.vars ≠ [] := by
    intro empty
    have lengths := permutation.length_eq
    simp only [empty, List.length_nil] at lengths
    exact nonempty (List.length_eq_zero_iff.mp lengths.symm)
  simp only [Result.insert, reduceWith_unchanged basis row.normalize absent]
  cases shape : row.normalize.vars with
  | nil => exact False.elim (normalizedNonempty shape)
  | cons p vars => rfl

theorem find_forced_update {n : Nat} (basis : List Row) (triangular : Triangular basis)
    (formula : CNFFormula n) (row : Row) (generated : find basis formula = .forced row) :
    update formula (.basis basis) = .basis (basis ++ [row.normalize]) := by
  obtain ⟨clause, _, found⟩ := find_forced_origin basis formula row generated
  obtain ⟨nodup, nonempty, erased⟩ := inspect_forced_geometry basis triangular clause row found
  simp only [update, generated, forced_insert basis row nodup nonempty erased]

def remaining (n : Nat) : Result → Nat
  | .contradiction => 0
  | .basis basis => n + 1 - basis.length

theorem update_progress {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular)
    (changed : update formula result ≠ result) :
    remaining n (update formula result) < remaining n result := by
  cases result with
  | contradiction => exact False.elim (changed rfl)
  | basis basis =>
      have rank := basis_length_le n basis triangular inside
      cases generated : find basis formula with
      | satisfied => exact False.elim (changed (by simp [update, generated]))
      | contradiction => simp only [update, generated, remaining]; omega
      | forced row =>
          rw [find_forced_update basis triangular formula row generated]
          simp only [remaining, List.length_append, List.length_singleton]
          omega
      | unresolved => exact False.elim (changed (by simp [update, generated]))

theorem iterate_fixed {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (fixed : update formula result = result) : iterate formula fuel result = result := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [iterate, fixed] using ih

theorem iterate_settled {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (enough : remaining n result ≤ fuel) :
    update formula (iterate formula fuel result) = iterate formula fuel result := by
  induction fuel generalizing result with
  | zero =>
      cases result with
      | contradiction => rfl
      | basis basis =>
          have rank := basis_length_le n basis triangular inside
          simp only [remaining] at enough
          omega
  | succ fuel ih =>
      by_cases fixed : update formula result = result
      · rw [iterate_fixed formula (fuel+1) result fixed]
        exact fixed
      · have progress := update_progress formula result inside triangular fixed
        exact ih _ (update_within formula result inside) (update_triangular formula result triangular) (by omega)

theorem generate_settled {n : Nat} (formula : CNFFormula n) :
    update formula (generate formula) = generate formula := by
  apply iterate_settled formula (n+1) _
    (eliminate_within n _ (extract_rowsWithin formula)) (eliminate_triangular _)
  cases eliminate (Extract.extract formula) <;> simp only [remaining] <;> omega

theorem generated_no_forced {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : generate formula = .basis basis) (row : Row) : find basis formula ≠ .forced row := by
  intro found
  have settled := generate_settled formula
  have triangular := (generate_invariants formula).2
  rw [generated] at settled triangular
  rw [find_forced_update basis triangular formula row found] at settled
  have same : basis ++ [row.normalize] = basis := Result.basis.inj settled
  have lengths := congrArg List.length same
  simp only [List.length_append, List.length_singleton] at lengths
  omega

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

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Propagation

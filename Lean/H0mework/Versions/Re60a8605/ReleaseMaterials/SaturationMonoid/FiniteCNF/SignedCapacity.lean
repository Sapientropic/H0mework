import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.CapacityFeedback

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.SignedCapacity

open SaturationMonoid.ComplexityProjection.SATSource.Affine

def positive {n : Nat} (i : Fin n) : Fin (n+n) := ⟨i.val,by omega⟩
def negative {n : Nat} (i : Fin n) : Fin (n+n) := ⟨n+i.val,by omega⟩

def address {n : Nat} (literal : CNFLiteral n) : Fin (n+n) :=
  if literal.positive then positive literal.var else negative literal.var

def lift (n : Nat) (assignment : Nat → Bool) : Nat → Bool :=
  fun i => if i<n then assignment i else !assignment (i-n)

@[simp] theorem lift_positive {n : Nat} (assignment : Nat → Bool) (i : Fin n) :
    lift n assignment (positive i).val = assignment i.val := by simp [lift,positive,i.isLt]

@[simp] theorem lift_negative {n : Nat} (assignment : Nat → Bool) (i : Fin n) :
    lift n assignment (negative i).val = !assignment i.val := by simp [lift,negative]

def required {n : Nat} (literal : CNFLiteral n) : CNFLiteral (n+n) := ⟨address literal,true⟩
def excluded {n : Nat} (literal : CNFLiteral n) : CNFLiteral (n+n) := ⟨address (Alias.negate literal),false⟩

theorem required_lift {n : Nat} (literal : CNFLiteral n) (assignment : Nat → Bool) :
    (required literal).eval (lift n assignment) = literal.eval assignment := by
  cases sign : literal.positive <;> simp [required,address,CNFLiteral.eval,sign]

theorem excluded_lift {n : Nat} (literal : CNFLiteral n) (assignment : Nat → Bool) :
    (excluded literal).eval (lift n assignment) = literal.eval assignment := by
  cases sign : literal.positive <;> simp [excluded,address,Alias.negate,CNFLiteral.eval,sign]

def demands {n : Nat} (formula : CNFFormula n) : CNFFormula (n+n) :=
  formula.map (fun clause => clause.map required)

def exclusions {n : Nat} (formula : CNFFormula n) : CNFFormula (n+n) :=
  formula.map (fun clause => clause.map excluded)

def covers (n : Nat) : CNFFormula (n+n) :=
  (List.finRange n).map fun i => [⟨positive i,true⟩,⟨negative i,true⟩]

def disjoint (n : Nat) : CNFFormula (n+n) :=
  (List.finRange n).map fun i => [⟨positive i,false⟩,⟨negative i,false⟩]

def expand {n : Nat} (formula : CNFFormula n) : CNFFormula (n+n) :=
  demands formula ++ exclusions formula ++ covers n ++ disjoint n

theorem demands_lift {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (demands formula) (lift n assignment) = CNFFormula.eval formula assignment := by
  simp only [demands,CNFFormula.eval,List.all_map]
  apply List.all_congr rfl
  intro clause
  simp only [Function.comp_apply,CNFClause.eval,List.any_map]
  apply List.any_congr rfl
  intro literal
  exact required_lift literal assignment

theorem exclusions_lift {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (exclusions formula) (lift n assignment) = CNFFormula.eval formula assignment := by
  simp only [exclusions,CNFFormula.eval,List.all_map]
  apply List.all_congr rfl
  intro clause
  simp only [Function.comp_apply,CNFClause.eval,List.any_map]
  apply List.any_congr rfl
  intro literal
  exact excluded_lift literal assignment

theorem covers_lift (n : Nat) (assignment : Nat → Bool) :
    CNFFormula.eval (covers n) (lift n assignment) = true := by
  simp only [covers,CNFFormula.eval,List.all_map,List.all_eq_true]
  intro i _
  simp [CNFClause.eval,CNFLiteral.eval]

theorem disjoint_lift (n : Nat) (assignment : Nat → Bool) :
    CNFFormula.eval (disjoint n) (lift n assignment) = true := by
  simp only [disjoint,CNFFormula.eval,List.all_map,List.all_eq_true]
  intro i _
  simp [CNFClause.eval,CNFLiteral.eval]

theorem expand_lift {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    CNFFormula.eval (expand formula) (lift n assignment) = CNFFormula.eval formula assignment := by
  simp only [expand,CNFFormula.eval,List.all_append]
  change (CNFFormula.eval (demands formula) (lift n assignment) &&
    CNFFormula.eval (exclusions formula) (lift n assignment) &&
    CNFFormula.eval (covers n) (lift n assignment) &&
    CNFFormula.eval (disjoint n) (lift n assignment)) = _
  rw [demands_lift,exclusions_lift,covers_lift,disjoint_lift]
  simp [CNFFormula.eval]

theorem complementary {n : Nat} (assignment : Nat → Bool)
    (covered : CNFFormula.eval (covers n) assignment = true)
    (separate : CNFFormula.eval (disjoint n) assignment = true) (i : Fin n) :
    assignment (negative i).val = !assignment (positive i).val := by
  have left := List.all_eq_true.mp covered [⟨positive i,true⟩,⟨negative i,true⟩]
    (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
  have right := List.all_eq_true.mp separate [⟨positive i,false⟩,⟨negative i,false⟩]
    (List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩)
  cases a : assignment (positive i).val <;> cases b : assignment (negative i).val <;>
    simp [CNFClause.eval,CNFLiteral.eval,a,b] at left right ⊢

theorem required_restrict {n : Nat} (literal : CNFLiteral n) (assignment : Nat → Bool)
    (covered : CNFFormula.eval (covers n) assignment = true)
    (separate : CNFFormula.eval (disjoint n) assignment = true) :
    (required literal).eval assignment = literal.eval assignment := by
  cases sign : literal.positive
  · simpa only [required,address,sign,Bool.false_eq_true,if_false,CNFLiteral.eval,if_true,positive] using
      complementary assignment covered separate literal.var
  · simp [required,address,sign,CNFLiteral.eval,positive]

theorem expand_restrict {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval (expand formula) assignment = true) :
    CNFFormula.eval formula assignment = true := by
  have clauses : CNFFormula.eval (demands formula) assignment = true ∧
      CNFFormula.eval (exclusions formula) assignment = true ∧
      CNFFormula.eval (covers n) assignment = true ∧ CNFFormula.eval (disjoint n) assignment = true := by
    simpa only [expand,CNFFormula.eval,List.all_append,Bool.and_eq_true,and_assoc] using accepted
  have same : CNFFormula.eval (demands formula) assignment = CNFFormula.eval formula assignment := by
    simp only [demands,CNFFormula.eval,List.all_map]
    apply List.all_congr rfl
    intro clause
    simp only [Function.comp_apply,CNFClause.eval,List.any_map]
    apply List.any_congr rfl
    intro literal
    exact required_restrict literal assignment clauses.2.2.1 clauses.2.2.2
  exact same.symm.trans clauses.1

theorem expand_satisfiable {n : Nat} (formula : CNFFormula n) :
    CNFSatisfiable (expand formula) ↔ CNFSatisfiable formula := by
  constructor
  · rintro ⟨assignment,accepted⟩
    exact ⟨assignment,expand_restrict formula assignment accepted⟩
  · rintro ⟨assignment,accepted⟩
    exact ⟨lift n assignment,(expand_lift formula assignment).trans accepted⟩

theorem lift_restrict {n : Nat} (assignment : Nat → Bool)
    (covered : CNFFormula.eval (covers n) assignment = true)
    (separate : CNFFormula.eval (disjoint n) assignment = true) (i : Fin (n+n)) :
    lift n assignment i.val = assignment i.val := by
  by_cases first : i.val<n
  · simp [lift,first]
  · let j : Fin n := ⟨i.val-n,by have bound := i.isLt; omega⟩
    have same : (negative j).val = i.val := by dsimp [negative,j]; omega
    have relation := complementary assignment covered separate j
    rw [same] at relation
    simpa only [lift,if_neg first,positive,j] using relation.symm

theorem expand_length {n : Nat} (formula : CNFFormula n) :
    (expand formula).length = 2*formula.length+2*n := by
  simp only [expand,demands,exclusions,covers,disjoint,List.length_append,List.length_map,List.length_finRange]
  omega

theorem expand_literals {n : Nat} (formula : CNFFormula n) :
    Extract.literalCount (expand formula) = 2*Extract.literalCount formula+4*n := by
  simp [Extract.literalCount,expand,demands,exclusions,covers,disjoint,List.map_map,Function.comp_def]
  change (formula.map List.length).sum + ((formula.map List.length).sum+(n+n)*2) = _
  omega

theorem expand_encode_length {n : Nat} (formula : CNFFormula n) :
    (Encoding.encode ⟨n+n,expand formula⟩).length ≤
      (2*n+2)+2*(2*formula.length+2*n)+(2*n+2)*(2*Extract.literalCount formula+4*n) := by
  have bound := Encoding.encode_formula_length_le (expand formula)
  have size : (expand formula).flatten.length = 2*Extract.literalCount formula+4*n := by
    simpa only [List.length_flatten,Extract.literalCount] using expand_literals formula
  rw [expand_length,size] at bound
  simpa only [two_mul] using bound

theorem partition_visits {n : Nat} (formula : CNFFormula n) :
    Capacity.partitionVisits (expand formula) (Capacity.positives (expand formula)).flatten ≤
      (2*Extract.literalCount formula+4*n+1)^2 *
        (10*(2*Extract.literalCount formula+4*n)+8*(2*formula.length+2*n)+9) := by
  simpa only [expand_literals,expand_length] using Capacity.source_partition_visits (expand formula)

def sourceRow (n : Nat) (i : Fin (n+n)) : Row :=
  if i.val<n then ⟨[i.val],false⟩ else ⟨[i.val-n],true⟩

def coordinates (n : Nat) : Array Row := Array.ofFn (sourceRow n)

theorem sourceRow_valid (n : Nat) (i : Fin (n+n)) : Table.RowValid n (sourceRow n i) := by
  unfold sourceRow
  split
  · rename_i inside
    simp [Table.RowValid,InterferenceProgram.Parity.Within,inside]
  · rename_i outside
    have inside : i.val-n<n := by have bound := i.isLt; omega
    simp [Table.RowValid,InterferenceProgram.Parity.Within,inside]

theorem coordinates_valid (n : Nat) : Table.Valid n (coordinates n) := by
  intro row member
  simp only [coordinates,Array.toList_ofFn,List.mem_ofFn] at member
  obtain ⟨i,rfl⟩ := member
  exact sourceRow_valid n i

theorem sourceRow_value (n : Nat) (i : Fin (n+n)) (assignment : Nat → Bool) :
    Gates.value (sourceRow n i) assignment = lift n assignment i.val := by
  unfold sourceRow lift
  split <;> simp [Gates.value,Row.eval,InterferenceProgram.Parity.eval]

theorem coordinates_value (n : Nat) (assignment : Nat → Bool) (i : Nat) (inside : i<n+n) :
    Gates.coordinate (coordinates n) assignment i = lift n assignment i := by
  rw [Table.coordinate_getD]
  simpa [coordinates,Array.getD,inside] using
    sourceRow_value n ⟨i,inside⟩ assignment

def decode (n : Nat) (row : Row) : Row := Table.combine (coordinates n) row.vars ⟨[],row.rhs⟩

theorem decode_holds (n : Nat) (row : Row) (inside : InterferenceProgram.Parity.Within (n+n) row.vars)
    (assignment : Nat → Bool) :
    (decode n row).holds assignment = row.holds (lift n assignment) := by
  rw [Atoms.holds_not_value,Atoms.holds_not_value,decode,Table.combine_value]
  simp only [Gates.value,Row.eval,InterferenceProgram.Parity.eval,Bool.xor_false]
  rw [InterferenceProgram.Parity.eval_congr (Gates.coordinate (coordinates n) assignment) (lift n assignment)
    row.vars (fun i member => coordinates_value n assignment i (inside i member))]

theorem decode_valid (n : Nat) (row : Row) : Table.RowValid n (decode n row) :=
  Table.combine_valid n _ (coordinates_valid n) row.vars _
    (by simp [Table.RowValid,InterferenceProgram.Parity.Within])

def relations {n : Nat} (formula : CNFFormula n) : List Row :=
  let table := coordinates n
  (Capacity.relations (expand formula)).map (fun row => Table.combine table row.vars ⟨[],row.rhs⟩)

theorem relations_entails {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool)
    (accepted : CNFFormula.eval formula assignment = true) : holds (relations formula) assignment = true := by
  have source := Capacity.relations_entails (expand formula) (lift n assignment)
    ((expand_lift formula assignment).trans accepted)
  apply (holds_iff _ _).mpr
  intro row member
  obtain ⟨original,hit,rfl⟩ := List.mem_map.mp member
  change (decode n original).holds assignment = true
  rw [decode_holds n original (Capacity.relations_within _ original hit)]
  exact (holds_iff _ _).mp source original hit

theorem relations_within {n : Nat} (formula : CNFFormula n) : RowsWithin n (relations formula) := by
  intro row member
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
  exact (decode_valid n original).2

theorem relations_length {n : Nat} (formula : CNFFormula n) :
    (relations formula).length ≤ 2*Extract.literalCount formula+2*formula.length+6*n+1 := by
  have bound := Capacity.relations_length (expand formula)
  rw [expand_length,expand_literals] at bound
  simp only [relations,List.length_map]
  omega

private theorem capacity_nodup {n : Nat} (formula : CNFFormula n) (row : Row)
    (member : row ∈ Capacity.relations formula) : row.vars.Nodup := by
  unfold Capacity.relations at member
  dsimp only at member
  split at member
  · have same : row = ⟨[],true⟩ := by simpa only [List.mem_singleton] using member
    simp [same]
  · split at member
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp member
      exact Row.normalize_nodup _
    · simp at member

def decodeVisits {n : Nat} (formula : CNFFormula n) : Nat :=
  let table := coordinates n
  ((Capacity.relations (expand formula)).map fun row => Table.combineVisits table row.vars ⟨[],row.rhs⟩).sum

theorem decode_visits {n : Nat} (formula : CNFFormula n) :
    decodeVisits formula ≤ (2*Extract.literalCount formula+2*formula.length+6*n+1)*
      ((n+n)*(n*(2*n+5)+4)+1) := by
  have each (row : Row) (member : row ∈ Capacity.relations (expand formula)) :
      Table.combineVisits (coordinates n) row.vars ⟨[],row.rhs⟩ ≤ (n+n)*(n*(2*n+5)+4)+1 := by
    have width := Table.row_length_le (n+n) row
      ⟨capacity_nodup _ row member,Capacity.relations_within _ row member⟩
    have bound := Table.combineVisits_bound n (coordinates n) (coordinates_valid n) row.vars ⟨[],row.rhs⟩
      (by simp [Table.RowValid,InterferenceProgram.Parity.Within])
    exact bound.trans (by gcongr)
  have sumBound : ∀ rows : List Row, (∀ row ∈ rows, row ∈ Capacity.relations (expand formula)) →
      (rows.map fun row => Table.combineVisits (coordinates n) row.vars ⟨[],row.rhs⟩).sum ≤
        rows.length*((n+n)*(n*(2*n+5)+4)+1) := by
    intro rows included
    induction rows with
    | nil => simp
    | cons row rest ih =>
        have head := each row (included row (by simp))
        have tail := ih (fun other member => included other (by simp [member]))
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
  have total := sumBound (Capacity.relations (expand formula)) (fun _ member => member)
  have count := Capacity.relations_length (expand formula)
  rw [expand_length,expand_literals] at count
  change decodeVisits formula ≤ _ at total
  have countBound : (Capacity.relations (expand formula)).length ≤
      2*Extract.literalCount formula+2*formula.length+6*n+1 := by omega
  exact total.trans (Nat.mul_le_mul_right _ countBound)

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  if Capacity.obstruction formula then false else CapacityFeedback.decideRows formula (relations formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  unfold decideFormula
  split
  · rename_i rejected
    simp [Capacity.obstruction_unsatisfiable formula rejected]
  · rw [CapacityFeedback.decideRows_correct _ _ (relations_within formula)]
    constructor
    · rintro ⟨assignment,accepted,_⟩
      exact ⟨extendAssignment assignment,accepted⟩
    · rintro ⟨assignment,accepted⟩
      let finite : Assignment n := fun i => assignment i.val
      have value : CNFFormula.eval formula (extendAssignment finite) = true :=
        (formula_eval_restrict _ assignment).trans accepted
      exact ⟨finite,value,relations_entails _ _ value⟩

def read (n : Nat) (formula : CNFFormula n) (assignment : Nat → Bool) : Bool :=
  CapacityFeedback.readRows formula (relations formula) assignment

theorem read_value {n : Nat} (formula : CNFFormula n) (assignment : Nat → Bool) :
    read n formula assignment = CNFFormula.eval formula assignment := by
  rw [read,CapacityFeedback.readRows_value _ _ (relations_within formula)]
  by_cases accepted : CNFFormula.eval formula assignment = true
  · rw [relations_entails _ _ accepted,Bool.and_true]
  · simp [accepted]

def sourceAction {n : Nat} (formula : CNFFormula n) (source : Source n) : Source n :=
  fun assignment => if read n formula (extendAssignment assignment) then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (source : Source n) :
    zeroProjector formula source = sourceAction formula source := by
  funext assignment
  simp only [zeroProjector_apply,sourceAction,read_value]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits,Encoding.decideBits,parsed]
  | some input =>
      simp only [decideBits,Encoding.decideBits,parsed]
      apply Bool.eq_iff_iff.mpr
      rw [decideFormula_correct,Dense.decideFormula_correct]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original,Encoding.decideBits_iff_rootVerify]

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔ ¬ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [decideBits_eq_original,Encoding.decideBits_no]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) : decideBits bits = false := by
  simp [decideBits,invalid]

end SaturationMonoid.ComplexityProjection.SATSource.SignedCapacity

import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.BranchImage

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.ConditionalPivot

open InterferenceProgram
open FunctionalSubstitution (Instruction)

def project (coordinates : Array Row) (rows : List Row) : List Row :=
  rows.map fun row => Table.combine coordinates row.vars ⟨[],row.rhs⟩

theorem project_holds (coordinates : Array Row) (rows : List Row) (environment : Nat → Bool) :
    holds (project coordinates rows) environment = holds rows (Gates.coordinate coordinates environment) := by
  simp only [holds, project, List.all_map]
  apply List.all_congr rfl
  intro row
  change (Table.combine coordinates row.vars ⟨[],row.rhs⟩).holds environment =
    row.holds (Gates.coordinate coordinates environment)
  rw [Atoms.holds_not_value, Atoms.holds_not_value, Table.combine_value]
  simp only [Gates.value, Row.eval, Parity.eval, Bool.xor_false]

def expression (rows : List Row) (address : Nat) : Row :=
  match rows.find? (fun row => decide (address ∈ row.vars)) with
  | none => ⟨[address],false⟩
  | some row => row.xor ⟨[address],false⟩

theorem expression_value (rows : List Row) (address : Nat) (environment : Nat → Bool)
    (accepted : holds rows environment = true) : Gates.value (expression rows address) environment = environment address := by
  unfold expression
  cases found : rows.find? (fun row => decide (address ∈ row.vars)) with
  | none => simp [Gates.value, Row.eval, Parity.eval]
  | some row =>
      have member := List.mem_of_find?_eq_some found
      have relation := (holds_iff rows environment).mp accepted row member
      have zero : Gates.value row environment = false := by
        rw [Atoms.holds_not_value] at relation
        cases value : Gates.value row environment <;> simp_all
      rw [Table.value_xor, zero]
      simp [Gates.value, Row.eval, Parity.eval]

def mux (selector left right : Fragment) : Fragment :=
  (selector.not.and left).xor (selector.and right)

theorem mux_value (selector left right : Fragment) (environment : Nat → Bool) :
    (mux selector left right).eval environment = bit
      (if truth (selector.eval environment) then truth (right.eval environment) else truth (left.eval environment)) := by
  simp only [mux, Fragment.eval_xor, Fragment.eval_and, Fragment.eval_not, truth_bit]
  cases truth (selector.eval environment) <;> simp

def split {n : Nat} (formula : CNFFormula n) (basis : List Row) (i : Fin n) : Option (List Row × List Row) :=
  match BranchImage.branch formula (.basis basis) i false, BranchImage.branch formula (.basis basis) i true with
  | .basis left, .basis right => some (left,right)
  | _, _ => none

theorem split_branches {n : Nat} (formula : CNFFormula n) (basis : List Row) (i : Fin n) (left right : List Row)
    (found : split formula basis i = some (left,right)) :
    BranchImage.branch formula (.basis basis) i false = .basis left ∧
      BranchImage.branch formula (.basis basis) i true = .basis right := by
  cases a : BranchImage.branch formula (.basis basis) i false <;>
    cases b : BranchImage.branch formula (.basis basis) i true <;> simp [split,a,b] at found
  obtain ⟨rfl,rfl⟩ := found
  exact ⟨rfl,rfl⟩

def body (coordinates : Array Row) (i j : Nat) (left right : List Row) : Fragment :=
  mux (Gates.compileRow (coordinates.getD i Gates.zeroRow))
    (Gates.compileRow (expression left j)) (Gates.compileRow (expression right j))

theorem body_value {n : Nat} (formula : CNFFormula n) (basis : List Row) (i : Fin n) (j : Nat)
    (left right : List Row) (found : split formula basis i = some (left,right))
    (coordinates : Array Row) (environment : Nat → Bool)
    (relations : holds basis (Gates.coordinate coordinates environment) = true)
    (accepted : CNFFormula.eval formula (Gates.coordinate coordinates environment) = true) :
    (body coordinates i.val j (project coordinates left) (project coordinates right)).eval environment = bit (environment j) := by
  have branches := split_branches formula basis i left right found
  rw [body, mux_value, Gates.eval_compileRow, Gates.eval_compileRow, Gates.eval_compileRow,
    truth_bit, truth_bit, truth_bit, ← Table.coordinate_getD]
  have actual := BranchImage.branch_holds formula (.basis basis) i
    (Gates.coordinate coordinates environment i.val) (Gates.coordinate coordinates environment)
  simp only [accepted, Result.holds, relations, Bool.true_and, Bool.and_true, beq_self_eq_true] at actual
  cases chosen : Gates.coordinate coordinates environment i.val with
  | false =>
      rw [chosen, branches.1] at actual
      simp only [Bool.false_eq_true, if_false]
      exact congrArg bit (expression_value (project coordinates left) j environment ((project_holds coordinates left environment).trans actual))
  | true =>
      rw [chosen, branches.2] at actual
      simp only [if_true]
      exact congrArg bit (expression_value (project coordinates right) j environment ((project_holds coordinates right environment).trans actual))

def instruction (n : Nat) (basis : List Row) (coordinates : Array Row) (i : Fin n) (left right : List Row)
    (j : Fin (freeIndices n basis).length) : Instruction :=
  ⟨j.val,body coordinates i.val j.val left right⟩

theorem instruction_fixes {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (inside : RowsWithin n basis) (triangular : Triangular basis) (i : Fin n) (left right : List Row)
    (found : split formula basis i = some (left,right)) (j : Fin (freeIndices n basis).length)
    (environment : Nat → Bool)
    (accepted : CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) environment) = true) :
    (instruction n basis (Table.coordinates n basis) i
      (project (Table.coordinates n basis) left) (project (Table.coordinates n basis) right) j).bind environment = environment := by
  apply FunctionalSubstitution.bind_fixes
  have relations : holds basis (Gates.coordinate (Table.coordinates n basis) environment) = true := by
    rw [Table.coordinates_value n basis inside]
    exact fill_holds basis triangular _
  change environment j.val = truth ((body (Table.coordinates n basis) i.val j.val
    (project (Table.coordinates n basis) left) (project (Table.coordinates n basis) right)).eval environment)
  rw [body_value formula basis i _ left right found _ environment relations accepted, truth_bit]


def branchCandidates {n : Nat} (formula : CNFFormula n) (basis : List Row) (coordinates : Array Row) (i : Fin n) : List Instruction :=
  match split formula basis i with
  | none => []
  | some (left,right) =>
      let leftRows := project coordinates left
      let rightRows := project coordinates right
      (List.finRange (freeIndices n basis).length).map (instruction n basis coordinates i leftRows rightRows)

theorem branchCandidates_fixes {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (inside : RowsWithin n basis) (triangular : Triangular basis) (i : Fin n) (call : Instruction)
    (member : call ∈ branchCandidates formula basis (Table.coordinates n basis) i) (environment : Nat → Bool)
    (accepted : CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) environment) = true) :
    call.bind environment = environment := by
  unfold branchCandidates at member
  cases found : split formula basis i with
  | none => simp [found] at member
  | some pair =>
      rcases pair with ⟨left,right⟩
      simp only [found, List.mem_map] at member
      obtain ⟨j,_,rfl⟩ := member
      exact instruction_fixes formula basis inside triangular i left right found j environment accepted

def candidates {n : Nat} (formula : CNFFormula n) (basis : List Row) : List Instruction :=
  let coordinates := Table.coordinates n basis
  FunctionalPivot.candidates formula basis ++ (List.finRange n).flatMap (branchCandidates formula basis coordinates)

theorem candidates_entails {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (inside : RowsWithin n basis) (triangular : Triangular basis) (environment : Nat → Bool)
    (accepted : truth ((Acceptance.compile (Table.coordinates n basis) formula).eval environment) = true)
    (call : Instruction) (member : call ∈ candidates formula basis) : call.bind environment = environment := by
  rcases List.mem_append.mp member with previous | generated
  · exact FunctionalPivot.candidates_entails formula basis environment accepted call previous
  · obtain ⟨i,_,hit⟩ := List.mem_flatMap.mp generated
    rw [Acceptance.eval_compile, truth_bit] at accepted
    exact branchCandidates_fixes formula basis inside triangular i call hit environment accepted

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Program :=
  FunctionalSubstitution.prepare (candidates formula basis) (Acceptance.compile (Table.coordinates n basis) formula)

theorem compile_correct {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (inside : RowsWithin n basis) (triangular : Triangular basis) :
    FunctionalSubstitution.decideProgram (Cone.pruneCone (compile formula basis)) = true ↔
      ∃ assignment : Assignment n, CNFFormula.eval formula (extendAssignment assignment) = true ∧
        holds basis (extendAssignment assignment) = true := by
  rw [FunctionalPivot.decide_prune, compile, FunctionalSubstitution.prepare_correct _ _
    (candidates_entails formula basis inside triangular)]
  simp only [Acceptance.eval_compile, truth_bit]
  constructor
  · rintro ⟨environment,accepted⟩
    let assignment : Assignment n := fun i => Gates.coordinate (Table.coordinates n basis) environment i.val
    have relations : holds basis (Gates.coordinate (Table.coordinates n basis) environment) = true := by
      rw [Table.coordinates_value n basis inside]
      exact fill_holds basis triangular _
    exact ⟨assignment,(formula_eval_restrict formula _).trans accepted,
      (AtomSource.holds_restrict n basis inside _).trans relations⟩
  · rintro ⟨assignment,accepted,relations⟩
    have recovered := (Decision.table_lift n basis inside (projectFree n basis assignment)).trans
      (parameterLift_projectFree n basis triangular assignment relations)
    refine ⟨extendAssignment (projectFree n basis assignment), ?_⟩
    rw [← formula_eval_restrict formula _]
    exact (congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) recovered).trans accepted

def decideResult {n : Nat} (formula : CNFFormula n) : Result → Bool
  | .contradiction => false
  | .basis basis => FunctionalSubstitution.decideProgram (Cone.pruneCone (compile formula basis))

theorem decideResult_eq_original {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) :
    decideResult formula result = JointFeedback.decideResult formula result := by
  apply Bool.eq_iff_iff.mpr
  rw [JointFeedback.decideResult_correct formula result inside triangular]
  cases result with
  | contradiction => simp [decideResult, Result.holds]
  | basis basis =>
      rw [decideResult, compile_correct formula basis inside triangular]
      simp only [Bool.and_eq_true, Result.holds]

def decideRows {n : Nat} (formula : CNFFormula n) (rows : List Row) : Bool :=
  decideResult formula (BranchImage.generate formula rows)

theorem decideRows_eq_original {n : Nat} (formula : CNFFormula n) (rows : List Row)
    (inside : RowsWithin n rows) : decideRows formula rows = BranchImage.decideRows formula rows := by
  have valid := BranchImage.generate_invariants formula rows inside
  exact decideResult_eq_original formula _ valid.1 valid.2

def decideData (data : List (List Row)) : Bool :=
  let image := AtomImage.generate (Atoms.table data)
  let formula := Subsumption.reduce (Atoms.compile data)
  decideRows formula image.kernel

theorem decideData_eq_original (n : Nat) (data : List (List Row))
    (valid : ∀ row ∈ data.flatten, Table.RowValid n row) :
    decideData data = BranchImage.decideData data := decideRows_eq_original _ _ (AtomSource.kernel_within n data valid)

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  match Atoms.generate formula with
  | .contradiction => false
  | .basis basis => decideData (Atoms.data basis formula)

theorem decideFormula_eq_original {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = BranchImage.decideFormula formula := by
  cases generated : Atoms.generate formula with
  | contradiction => simp [decideFormula, BranchImage.decideFormula, generated]
  | basis basis =>
      simp only [decideFormula, BranchImage.decideFormula, generated]
      exact decideData_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  rw [decideFormula_eq_original, BranchImage.decideFormula_correct]

def decideBits (bits : List Bool) : Bool :=
  match Encoding.parse bits with
  | none => false
  | some input => decideFormula input.2

theorem decideBits_eq_original (bits : List Bool) : decideBits bits = Encoding.decideBits bits := by
  rw [← BranchImage.decideBits_eq_original]
  cases parsed : Encoding.parse bits with
  | none => simp [decideBits, BranchImage.decideBits, parsed]
  | some input => simp [decideBits, BranchImage.decideBits, parsed, decideFormula_eq_original]

theorem decideBits_iff_rootVerify (bits : List Bool) :
    decideBits bits = true ↔ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧
      ∃ assignment : Nat → Bool, CNFSATVerify input.2 (CNFSATNode.root input.1) assignment := by
  rw [decideBits_eq_original, Encoding.decideBits_iff_rootVerify]

theorem decideBits_no (bits : List Bool) :
    decideBits bits = false ↔ ¬ ∃ input : Encoding.Input, Encoding.parse bits = some input ∧ CNFSatisfiable input.2 := by
  rw [decideBits_eq_original, Encoding.decideBits_no]

theorem decideBits_invalid (bits : List Bool) (invalid : Encoding.parse bits = none) : decideBits bits = false := by
  simp [decideBits, invalid]

theorem mux_small (selector left right : Fragment) (a : BooleanValues.Code selector.code)
    (b : BooleanValues.Code left.code) (c : BooleanValues.Code right.code) :
    BooleanValues.Code (mux selector left right).code :=
  BooleanValues.fragment_xor _ _
    (BooleanValues.fragment_and _ _ (BooleanValues.fragment_not _ a) b)
    (BooleanValues.fragment_and _ _ a c)

theorem body_small (coordinates : Array Row) (i j : Nat) (left right : List Row) :
    BooleanValues.Code (body coordinates i j left right).code :=
  mux_small _ _ _ (BooleanValues.compile_row _) (BooleanValues.compile_row _) (BooleanValues.compile_row _)

theorem branchCandidates_small {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (coordinates : Array Row) (i : Fin n) (call : Instruction)
    (member : call ∈ branchCandidates formula basis coordinates i) : BooleanValues.Code call.body.code := by
  unfold branchCandidates at member
  cases found : split formula basis i with
  | none => simp [found] at member
  | some pair =>
      rcases pair with ⟨left,right⟩
      simp only [found] at member
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
      exact body_small _ _ _ _ _

theorem candidate_small {n : Nat} (formula : CNFFormula n) (basis : List Row) (call : Instruction)
    (member : call ∈ candidates formula basis) : BooleanValues.Code call.body.code := by
  rcases List.mem_append.mp member with previous | generated
  · exact FunctionalPivot.candidate_small formula basis call previous
  · obtain ⟨i,_,hit⟩ := List.mem_flatMap.mp generated
    exact branchCandidates_small formula basis _ i call hit

theorem compile_small {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    BooleanValues.Code (compile formula basis).code :=
  FunctionalSubstitution.execute_small _ _ (BooleanValues.acceptance _ formula)
    (fun call member => candidate_small formula basis call
      ((FunctionalSubstitution.select_sublist [] _).subset member))

theorem close_small {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    BooleanValues.Code (FunctionalSubstitution.close (Cone.pruneCone (compile formula basis))).code :=
  BooleanValues.boolean_fold _ _ (BooleanValues.pruneCone _ (compile_small formula basis))

theorem expression_length (n : Nat) (basis rows : List Row) (address : Nat) :
    (expression (project (Table.coordinates n basis) rows) address).vars.length ≤ n+1 := by
  unfold expression
  cases found : (project (Table.coordinates n basis) rows).find? (fun row => decide (address ∈ row.vars)) with
  | none => simp
  | some row =>
      obtain ⟨original,_,rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
      have valid := Table.combine_valid _ _ (Table.coordinates_valid n basis) original.vars
        (⟨[],original.rhs⟩ : Row) (by simp [Table.RowValid,Parity.Within])
      have bound := Table.row_length_le _ _ valid
      have width := Table.freeWidth_le n basis
      have merged := Parity.merge_length (Table.combine (Table.coordinates n basis) original.vars
        ⟨[],original.rhs⟩).vars [address]
      simp only [Row.xor, List.length_singleton] at *
      omega

theorem body_size (n : Nat) (basis : List Row) (i j : Nat) (left right : List Row) :
    (body (Table.coordinates n basis) i j
      (project (Table.coordinates n basis) left) (project (Table.coordinates n basis) right)).code.size ≤ 12+8*n := by
  have a := Gates.compileRow_size ((Table.coordinates n basis).getD i Gates.zeroRow)
  have rowLength := Table.row_length_le _ _ (Table.read_valid _ _ (Table.coordinates_valid n basis) i)
  have width := Table.freeWidth_le n basis
  have b := Gates.compileRow_size (expression (project (Table.coordinates n basis) left) j)
  have bl := expression_length n basis left j
  have c := Gates.compileRow_size (expression (project (Table.coordinates n basis) right) j)
  have cl := expression_length n basis right j
  simp only [body, mux, Fragment.xor, Fragment.and, Fragment.not, Fragment.binary, Fragment.unary,
    Array.size_push, Array.size_append, Array.size_map]
  omega

theorem branchCandidates_length {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (coordinates : Array Row) (i : Fin n) : (branchCandidates formula basis coordinates i).length ≤ n := by
  unfold branchCandidates
  cases split formula basis i with
  | none => simp
  | some pair =>
      rcases pair with ⟨left,right⟩
      simpa only [List.length_map, List.length_finRange] using Table.freeWidth_le n basis

theorem candidates_length {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (candidates formula basis).length ≤ 3*formula.length+n*n := by
  have total : ∀ indices : List (Fin n),
      (indices.flatMap (branchCandidates formula basis (Table.coordinates n basis))).length ≤ indices.length*n := by
    intro indices
    induction indices with
    | nil => simp
    | cons i rest ih =>
        have head := branchCandidates_length formula basis (Table.coordinates n basis) i
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        nlinarith
  have generated := total (List.finRange n)
  simp only [List.length_finRange] at generated
  have previous := FunctionalPivot.candidates_length formula basis
  simp only [candidates, List.length_append]
  omega

theorem candidate_size {n : Nat} (formula : CNFFormula n) (basis : List Row) (call : Instruction)
    (member : call ∈ candidates formula basis) : call.body.code.size ≤ 12+8*n := by
  rcases List.mem_append.mp member with previous | generated
  · have bound := FunctionalPivot.candidate_size formula basis call previous
    omega
  · obtain ⟨i,_,hit⟩ := List.mem_flatMap.mp generated
    unfold branchCandidates at hit
    cases found : split formula basis i with
    | none => simp [found] at hit
    | some pair =>
        rcases pair with ⟨left,right⟩
        simp only [found] at hit
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hit
        exact body_size n basis i.val j.val left right

theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (compile formula basis).code.size ≤ 3+n+2*n*n+3*formula.length+3*SATJoint.literalCount formula+
      (3*formula.length+n*n)*(12+8*n) := by
  have budget : ∀ calls : List Instruction, (∀ call ∈ calls, call.body.code.size ≤ 12+8*n) →
      (calls.map (·.body.code.size)).sum ≤ calls.length*(12+8*n) := by
    intro calls bounds
    induction calls with
    | nil => simp
    | cons call rest ih =>
        have tail := ih (fun other member => bounds other (by simp [member]))
        have head := bounds call (by simp)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
  have calls := budget (candidates formula basis) (fun call member => candidate_size formula basis call member)
  have count := candidates_length formula basis
  have prepared := FunctionalSubstitution.prepare_size (candidates formula basis)
    (Acceptance.compile (Table.coordinates n basis) formula)
  have initial := Decision.initial_nodes formula basis
  have width := Table.freeWidth_le n basis
  change (compile formula basis).code.size ≤ _ at prepared
  nlinarith

def selected {n : Nat} (formula : CNFFormula n) (basis : List Row) : List Instruction :=
  FunctionalSubstitution.select [] (candidates formula basis)

theorem selected_eliminated {n : Nat} (formula : CNFFormula n) (basis : List Row) (call : Instruction)
    (member : call ∈ selected formula basis) : call.address ∉ FunctionalSubstitution.inputs (compile formula basis).code :=
  FunctionalSubstitution.prepare_eliminates _ _ call member

def readCompiled {n : Nat} (formula : CNFFormula n) (basis : List Row) (assignment : Nat → Bool) : Bool :=
  let finite : Assignment n := fun i => assignment i.val
  let environment := extendAssignment (projectFree n basis finite)
  holds basis assignment && FunctionalAffine.legal (selected formula basis) environment &&
    truth ((compile formula basis).eval environment)

theorem readCompiled_value {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (inside : RowsWithin n basis) (triangular : Triangular basis) (assignment : Nat → Bool) :
    readCompiled formula basis assignment = (CNFFormula.eval formula assignment && holds basis assignment) := by
  let finite : Assignment n := fun i => assignment i.val
  let environment := extendAssignment (projectFree n basis finite)
  by_cases relations : holds basis assignment = true
  · have finiteRelations : holds basis (extendAssignment finite) = true :=
      (AtomSource.holds_restrict n basis inside assignment).trans relations
    have recovered := (Decision.table_lift n basis inside (projectFree n basis finite)).trans
      (parameterLift_projectFree n basis triangular finite finiteRelations)
    have initial : (Acceptance.compile (Table.coordinates n basis) formula).eval environment =
        bit (CNFFormula.eval formula assignment) := by
      rw [Acceptance.eval_compile, ← formula_eval_restrict formula _]
      have value := congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) recovered
      exact congrArg bit (value.trans (formula_eval_restrict formula assignment))
    by_cases legal : FunctionalAffine.legal (selected formula basis) environment = true
    · have fixed := FunctionalAffine.legal_fixed _ _ legal
      have compiled : (compile formula basis).eval environment = bit (CNFFormula.eval formula assignment) := by
        rw [compile, FunctionalSubstitution.prepare, FunctionalSubstitution.eval_execute]
        change (Acceptance.compile (Table.coordinates n basis) formula).eval
          (FunctionalSubstitution.fill (selected formula basis) environment) = _
        rw [fixed]
        exact initial
      change (holds basis assignment && FunctionalAffine.legal (selected formula basis) environment &&
        truth ((compile formula basis).eval environment)) = _
      simp [relations, legal, compiled]
    · have rejected : CNFFormula.eval formula assignment = false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        apply legal
        apply FunctionalAffine.legal_of_fixed
        intro call member
        apply candidates_entails formula basis inside triangular environment
        · rw [initial,truth_bit]
          exact accepted
        · exact (FunctionalSubstitution.select_sublist [] _).subset member
      change (holds basis assignment && FunctionalAffine.legal (selected formula basis) environment &&
        truth ((compile formula basis).eval environment)) = _
      simp [legal, rejected]
  · simp [readCompiled, relations]

def readResult {n : Nat} (formula : CNFFormula n) : Result → (Nat → Bool) → Bool
  | .contradiction, _ => false
  | .basis basis, assignment => readCompiled formula basis assignment

theorem readResult_value {n : Nat} (formula : CNFFormula n) (result : Result)
    (inside : result.within n) (triangular : result.triangular) (assignment : Nat → Bool) :
    readResult formula result assignment = (CNFFormula.eval formula assignment && result.holds assignment) := by
  cases result with
  | contradiction => simp [readResult,Result.holds]
  | basis basis => exact readCompiled_value formula basis inside triangular assignment

def jointValue (data : List (List Row)) (target : Nat → Bool) : Bool :=
  let image := AtomImage.generate (Atoms.table data)
  let formula := Subsumption.reduce (Atoms.compile data)
  readResult formula (BranchImage.generate formula image.kernel) target

theorem jointValue_eq_original (n : Nat) (data : List (List Row))
    (valid : ∀ row ∈ data.flatten, Table.RowValid n row) (target : Nat → Bool) :
    jointValue data target = AtomSource.jointValue data target := by
  have inside := AtomSource.kernel_within n data valid
  have generated := BranchImage.generate_invariants (Subsumption.reduce (Atoms.compile data)) _ inside
  rw [jointValue, readResult_value _ _ generated.1 generated.2,
    BranchImage.generate_holds _ _ inside, AtomSource.jointValue, Bool.and_comm]

def sourceAction {n : Nat} (formula : CNFFormula n) (basis : List Row) (source : Source n) : Source n :=
  fun assignment =>
    let input := extendAssignment assignment
    if holds basis input && jointValue (Atoms.data basis formula) (Atoms.read (Atoms.data basis formula) input)
    then source assignment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) (source : Source n) :
    zeroProjector formula source = sourceAction formula basis source := by
  rw [AtomSource.original_projector formula basis generated source]
  funext assignment
  simp only [AtomSource.sourceAction, sourceAction,
    jointValue_eq_original n _ (Atoms.data_valid basis (Atoms.generated_within formula basis generated) formula)]

end SaturationMonoid.ComplexityProjection.SATSource.Affine.ConditionalPivot

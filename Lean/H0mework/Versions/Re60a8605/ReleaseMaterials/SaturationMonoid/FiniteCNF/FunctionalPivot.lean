import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalAffine

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalPivot

open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open FunctionalRelations (Relation)
open FunctionalSubstitution (Instruction)

def residual (coordinates : Array Row) {n : Nat} (relation : Relation n) (address : Nat) : Row :=
  (coordinates.getD relation.output.var.val Gates.zeroRow).xor ⟨[address],false⟩

def body (coordinates : Array Row) {n : Nat} (relation : Relation n) (address : Nat) : Fragment :=
  (Gates.compileRow (residual coordinates relation address)).xor (FunctionalAffine.body coordinates relation)

theorem body_eval (coordinates : Array Row) {n : Nat} (relation : Relation n) (address : Nat)
    (environment : Nat → Bool) :
    (body coordinates relation address).eval environment = bit
      ((Gates.coordinate coordinates environment relation.output.var.val ^^ environment address) ^^
        relation.value (Gates.coordinate coordinates environment)) := by
  simp only [body, Fragment.eval_xor, Gates.eval_compileRow, FunctionalAffine.body_eval, truth_bit]
  rw [residual, Table.value_xor, ← Table.coordinate_getD]
  simp [Gates.value, Row.eval, Parity.eval]

def call (coordinates : Array Row) {n : Nat} (relation : Relation n) (address : Nat) : Instruction :=
  ⟨address,body coordinates relation address⟩

theorem call_fixes (coordinates : Array Row) {n : Nat} (relation : Relation n) (address : Nat)
    (environment : Nat → Bool) (accepted : relation.holds (Gates.coordinate coordinates environment) = true) :
    (call coordinates relation address).bind environment = environment := by
  have value := congrFun (relation.bind_fixed _ accepted) relation.output.var.val
  simp only [Relation.bind, Function.update_self] at value
  apply FunctionalSubstitution.bind_fixes
  change environment address = truth ((body coordinates relation address).eval environment)
  rw [body_eval, truth_bit, value]
  cases Gates.coordinate coordinates environment relation.output.var.val <;> cases environment address <;> rfl

def choose (coordinates : Array Row) {n : Nat} (relation : Relation n) : Option Instruction :=
  ((coordinates.getD relation.output.var.val Gates.zeroRow).vars.map (call coordinates relation)).find?
    (FunctionalSubstitution.ready [])

theorem choose_fixes (coordinates : Array Row) {n : Nat} (relation : Relation n) (instruction : Instruction)
    (found : choose coordinates relation = some instruction) (environment : Nat → Bool)
    (accepted : relation.holds (Gates.coordinate coordinates environment) = true) : instruction.bind environment = environment := by
  have member := List.mem_of_find?_eq_some found
  obtain ⟨address, _, equal⟩ := List.mem_map.mp member
  subst instruction
  exact call_fixes coordinates relation address environment accepted

theorem choose_ready (coordinates : Array Row) {n : Nat} (relation : Relation n) (instruction : Instruction)
    (found : choose coordinates relation = some instruction) : FunctionalSubstitution.ready [] instruction = true :=
  List.find?_some found

theorem choose_address (coordinates : Array Row) {n : Nat} (relation : Relation n) (instruction : Instruction)
    (found : choose coordinates relation = some instruction) :
    instruction.address ∈ (coordinates.getD relation.output.var.val Gates.zeroRow).vars := by
  obtain ⟨address, member, equal⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
  subst instruction
  exact member

theorem body_small (coordinates : Array Row) {n : Nat} (relation : Relation n) (address : Nat) :
    BooleanValues.Code (body coordinates relation address).code :=
  BooleanValues.fragment_xor _ _ (BooleanValues.compile_row _) (FunctionalAffine.body_small coordinates relation)

theorem body_size {n : Nat} (basis : List Row) (relation : Relation n) (address : Nat) :
    (body (Table.coordinates n basis) relation address).code.size ≤ 10 + 6*n := by
  have rowLength := Table.row_length_le _ _
    (Table.read_valid _ _ (Table.coordinates_valid n basis) relation.output.var.val)
  have width : (freeIndices n basis).length ≤ n := by
    simpa only [freeIndices, List.length_range] using List.length_filter_le
      (fun i => decide (i ∉ pivots basis)) (List.range n)
  have residualLength : (residual (Table.coordinates n basis) relation address).vars.length ≤ n+1 := by
    have bound := Parity.merge_length (Table.coordinates n basis |>.getD relation.output.var.val Gates.zeroRow).vars [address]
    simp only [List.length_singleton] at bound
    exact bound.trans (Nat.add_le_add_right (rowLength.trans width) 1)
  have part := Gates.compileRow_size (residual (Table.coordinates n basis) relation address)
  have right := FunctionalAffine.body_size basis relation
  simp only [body, Fragment.xor, Fragment.binary, Array.size_push, Array.size_append, Array.size_map]
  omega

def candidates {n : Nat} (formula : CNFFormula n) (basis : List Row) : List Instruction :=
  (FunctionalRelations.extract formula).filterMap (choose (Table.coordinates n basis))

theorem candidates_entails {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (environment : Nat → Bool)
    (accepted : truth ((Acceptance.compile (Table.coordinates n basis) formula).eval environment) = true)
    (instruction : Instruction) (member : instruction ∈ candidates formula basis) : instruction.bind environment = environment := by
  obtain ⟨relation, generated, found⟩ := List.mem_filterMap.mp member
  rw [Acceptance.eval_compile, truth_bit] at accepted
  exact choose_fixes _ relation instruction found environment
    (FunctionalRelations.extract_entails formula relation generated _ accepted)

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Program :=
  FunctionalSubstitution.prepare (candidates formula basis) (Acceptance.compile (Table.coordinates n basis) formula)

theorem compile_correct {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) :
    FunctionalSubstitution.decideProgram (compile formula basis) = true ↔ CNFSatisfiable formula := by
  rw [compile, FunctionalSubstitution.prepare_correct _ _
    (candidates_entails formula basis)]
  exact FunctionalAffine.initial_satisfiable formula basis generated

theorem decide_prune (program : Program) :
    FunctionalSubstitution.decideProgram (Cone.pruneCone program) = FunctionalSubstitution.decideProgram program := by
  apply Bool.eq_iff_iff.mpr
  simp only [FunctionalSubstitution.decideProgram_correct, Cone.eval_pruneCone]

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  match Atoms.generate formula with
  | .contradiction => false
  | .basis basis => FunctionalSubstitution.decideProgram (Cone.pruneCone (compile formula basis))

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  cases generated : Atoms.generate formula with
  | contradiction =>
      have rejected : ¬ CNFSatisfiable formula := by
        rintro ⟨assignment, accepted⟩
        rw [Atoms.generated_contradiction_eval formula generated] at accepted
        exact Bool.noConfusion accepted
      simp [decideFormula, generated, rejected]
  | basis basis =>
      simp only [decideFormula, generated, decide_prune]
      exact compile_correct formula basis generated

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

theorem candidate_small {n : Nat} (formula : CNFFormula n) (basis : List Row) (call : Instruction)
    (member : call ∈ candidates formula basis) : BooleanValues.Code call.body.code := by
  obtain ⟨relation, _, found⟩ := List.mem_filterMap.mp member
  obtain ⟨address, _, equal⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
  subst call
  exact body_small _ _ _

theorem compile_small {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    BooleanValues.Code (compile formula basis).code :=
  FunctionalSubstitution.execute_small _ _ (BooleanValues.acceptance _ formula)
    (fun call member => candidate_small formula basis call
      ((FunctionalSubstitution.select_sublist [] _).subset member))

theorem close_small {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    BooleanValues.Code (FunctionalSubstitution.close (Cone.pruneCone (compile formula basis))).code :=
  BooleanValues.boolean_fold _ _ (BooleanValues.pruneCone _ (compile_small formula basis))

theorem candidates_length {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (candidates formula basis).length ≤ 3 * formula.length :=
  (List.length_filterMap_le _ _).trans (FunctionalRelations.extract_length formula)

theorem candidate_size {n : Nat} (formula : CNFFormula n) (basis : List Row) (call : Instruction)
    (member : call ∈ candidates formula basis) : call.body.code.size ≤ 10 + 6 * n := by
  obtain ⟨relation, _, found⟩ := List.mem_filterMap.mp member
  obtain ⟨address, _, equal⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
  subst call
  exact body_size _ _ _

theorem candidates_size {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    ((candidates formula basis).map (·.body.code.size)).sum ≤ 3 * formula.length * (10 + 6 * n) := by
  have bound : ∀ calls : List Instruction, (∀ call ∈ calls, call.body.code.size ≤ 10+6*n) →
      (calls.map (·.body.code.size)).sum ≤ calls.length * (10+6*n) := by
    intro calls
    induction calls with
    | nil => simp
    | cons call rest ih =>
        intro bounded
        have tail := ih (fun other member => bounded other (by simp [member]))
        have first := bounded call (by simp)
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        nlinarith
  exact (bound _ (candidate_size formula basis)).trans (Nat.mul_le_mul_right _ (candidates_length formula basis))

theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) :
    (compile formula basis).code.size ≤
      3 + n + 2*n*n + 3*formula.length + 3*SATJoint.literalCount formula + 3*formula.length*(10+6*n) := by
  have shared := FunctionalSubstitution.prepare_size (candidates formula basis) (Acceptance.compile (Table.coordinates n basis) formula)
  have original := Atoms.initial_nodes formula basis generated
  have added := candidates_size formula basis
  change (compile formula basis).code.size ≤ _ at shared
  omega

def selected {n : Nat} (formula : CNFFormula n) (basis : List Row) : List Instruction :=
  FunctionalSubstitution.select [] (candidates formula basis)

theorem selected_eliminated {n : Nat} (formula : CNFFormula n) (basis : List Row) (call : Instruction)
    (member : call ∈ selected formula basis) : call.address ∉ FunctionalSubstitution.inputs (compile formula basis).code :=
  FunctionalSubstitution.prepare_eliminates _ _ call member

def lift {n : Nat} (formula : CNFFormula n) (basis : List Row) (environment : Nat → Bool) : Assignment n :=
  fun i => Gates.coordinate (Table.coordinates n basis)
    (FunctionalSubstitution.fill (selected formula basis) environment) i.val

theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Row) (environment : Nat → Bool) :
    (compile formula basis).eval environment = bit (CNFFormula.eval formula (extendAssignment (lift formula basis environment))) := by
  rw [compile, FunctionalSubstitution.prepare, FunctionalSubstitution.eval_execute, Acceptance.eval_compile]
  exact congrArg bit (formula_eval_restrict formula _).symm

def action {n : Nat} (formula : CNFFormula n) (basis : List Row) (source : Source n)
    (environment : Nat → Bool) : ℚ :=
  ((compile formula basis).eval environment : ℚ) * source (lift formula basis environment)

def zeroExtension {n : Nat} (formula : CNFFormula n) (basis : List Row) (source : (Nat → Bool) → ℚ) : Source n :=
  fun assignment =>
    let environment := extendAssignment (projectFree n basis assignment)
    if holds basis (extendAssignment assignment) && FunctionalAffine.legal (selected formula basis) environment then source environment else 0

theorem original_projector {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) (source : Source n) :
    zeroProjector formula source = zeroExtension formula basis (action formula basis source) := by
  funext assignment
  let environment := extendAssignment (projectFree n basis assignment)
  have inside := Atoms.generated_within formula basis generated
  have triangular := Atoms.generated_triangular formula basis generated
  have recovery (relations : holds basis (extendAssignment assignment) = true) :
      Gates.lift n (Table.coordinates n basis) (projectFree n basis assignment) = assignment :=
    (Decision.table_lift n basis inside _).trans (parameterLift_projectFree n basis triangular assignment relations)
  have initial (relations : holds basis (extendAssignment assignment) = true) :
      (Acceptance.compile (Table.coordinates n basis) formula).eval environment =
        bit (CNFFormula.eval formula (extendAssignment assignment)) := by
    rw [Acceptance.eval_compile, ← formula_eval_restrict formula _]
    exact congrArg (fun x => bit (CNFFormula.eval formula (extendAssignment x))) (recovery relations)
  by_cases guard : holds basis (extendAssignment assignment) = true ∧ FunctionalAffine.legal (selected formula basis) environment = true
  · have filled := FunctionalAffine.legal_fixed (selected formula basis) environment guard.2
    have restored : lift formula basis environment = assignment := by
      funext i
      change Gates.coordinate (Table.coordinates n basis)
        (FunctionalSubstitution.fill (selected formula basis) environment) i.val = assignment i
      rw [filled]
      exact congrFun (recovery guard.1) i
    have value : (compile formula basis).eval environment =
        bit (CNFFormula.eval formula (extendAssignment assignment)) := by rw [compile_value, restored]
    rw [zeroProjector_apply]
    change _ = if (holds basis (extendAssignment assignment) && FunctionalAffine.legal (selected formula basis) environment) = true
      then action formula basis source environment else 0
    rw [guard.1, guard.2]
    simp only [Bool.and_self, ↓reduceIte]
    rw [action, value, restored]
    simp only [bit]
    split <;> simp_all
  · have rejected : CNFFormula.eval formula (extendAssignment assignment) ≠ true := by
      intro accepted
      have relations := Atoms.generated_relations formula basis generated _ accepted
      apply guard
      refine ⟨relations, FunctionalAffine.legal_of_fixed _ _ ?_⟩
      intro call member
      apply candidates_entails formula basis environment
      · rw [initial relations, truth_bit]
        exact accepted
      · exact (FunctionalSubstitution.select_sublist [] _).subset member
    rw [zeroProjector_apply]
    simp only [zeroExtension]
    have failed : (holds basis (extendAssignment assignment) && FunctionalAffine.legal (selected formula basis) environment) = false := by
      simpa only [Bool.and_eq_false_iff, Bool.not_eq_true, not_and_or] using guard
    simp only [show extendAssignment (projectFree n basis assignment) = environment from rfl, failed]
    simp [rejected]


end SaturationMonoid.ComplexityProjection.SATSource.FunctionalPivot

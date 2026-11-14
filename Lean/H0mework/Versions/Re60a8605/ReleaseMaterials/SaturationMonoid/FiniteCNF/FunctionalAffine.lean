import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalRelations
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Atoms.Consumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalSubstitution

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalAffine

open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open FunctionalRelations (Relation)
open FunctionalSubstitution (Instruction)

def literalBody {n : Nat} (coordinates : Array Row) (literal : CNFLiteral n) : Fragment :=
  let row := Gates.compileRow (coordinates.getD literal.var.val Gates.zeroRow)
  if literal.positive then row else row.not

theorem literalBody_eval {n : Nat} (coordinates : Array Row) (literal : CNFLiteral n)
    (environment : Nat → Bool) :
    (literalBody coordinates literal).eval environment = bit (literal.eval (Gates.coordinate coordinates environment)) := by
  cases polarity : literal.positive <;>
    simp [literalBody, polarity, Gates.eval_compileRow, CNFLiteral.eval,
      Table.coordinate_getD, truth_bit]

def body {n : Nat} (coordinates : Array Row) (relation : Relation n) : Fragment :=
  let value := (literalBody coordinates relation.left).and (literalBody coordinates relation.right)
  if relation.output.positive then value else value.not

theorem body_eval {n : Nat} (coordinates : Array Row) (relation : Relation n) (environment : Nat → Bool) :
    (body coordinates relation).eval environment = bit (relation.value (Gates.coordinate coordinates environment)) := by
  cases polarity : relation.output.positive <;>
    simp [body, Relation.value, polarity, literalBody_eval, truth_bit]

def instruction {n : Nat} (basis : List Row) (relation : Relation n) : Option Instruction :=
  if relation.output.var.val ∈ freeIndices n basis then
    some ⟨(freeIndices n basis).idxOf relation.output.var.val, body (Table.coordinates n basis) relation⟩
  else none

def candidates {n : Nat} (formula : CNFFormula n) (basis : List Row) : List Instruction :=
  (FunctionalRelations.extract formula).filterMap (instruction basis)

theorem coordinate_free (n : Nat) (basis : List Row) (inside : RowsWithin n basis)
    (i : Nat) (free : i ∈ freeIndices n basis) (environment : Nat → Bool) :
    Gates.coordinate (Table.coordinates n basis) environment i = environment ((freeIndices n basis).idxOf i) := by
  rw [Table.coordinates_value n basis inside]
  rw [fill_read basis _ i ((mem_freeIndices n basis i).mp free).2]
  simp only [freeSeed, free, if_pos]

theorem instruction_fixes {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (inside : RowsWithin n basis) (relation : Relation n) (generated : relation ∈ FunctionalRelations.extract formula)
    (call : Instruction) (found : instruction basis relation = some call)
    (environment : Nat → Bool)
    (accepted : CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) environment) = true) :
    call.bind environment = environment := by
  unfold instruction at found
  split at found
  · rename_i free
    cases Option.some.inj found
    have value := congrFun (relation.bind_fixed _
      (FunctionalRelations.extract_entails formula relation generated _ accepted)) relation.output.var.val
    simp only [Relation.bind, Function.update_self] at value
    rw [coordinate_free n basis inside _ free] at value
    apply FunctionalSubstitution.bind_fixes
    rw [body_eval, truth_bit]
    exact value.symm
  · cases found

theorem candidates_entails {n : Nat} (formula : CNFFormula n) (basis : List Row) (inside : RowsWithin n basis)
    (environment : Nat → Bool)
    (accepted : truth ((Acceptance.compile (Table.coordinates n basis) formula).eval environment) = true)
    (call : Instruction) (member : call ∈ candidates formula basis) : call.bind environment = environment := by
  obtain ⟨relation, generated, found⟩ := List.mem_filterMap.mp member
  rw [Acceptance.eval_compile, truth_bit] at accepted
  exact instruction_fixes formula basis inside relation generated call found environment accepted

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Program :=
  FunctionalSubstitution.prepare (candidates formula basis) (Acceptance.compile (Table.coordinates n basis) formula)

theorem initial_satisfiable {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) :
    (∃ environment : Nat → Bool, truth ((Acceptance.compile (Table.coordinates n basis) formula).eval environment) = true) ↔
      CNFSatisfiable formula := by
  simp only [Acceptance.eval_compile, truth_bit]
  constructor
  · rintro ⟨environment, accepted⟩
    exact ⟨Gates.coordinate (Table.coordinates n basis) environment, accepted⟩
  · intro accepted
    obtain ⟨parameters, accepted⟩ := (Atoms.satisfiable_iff_free formula basis generated).mp accepted
    refine ⟨extendAssignment parameters, ?_⟩
    have recovered := Decision.table_lift n basis (Atoms.generated_within formula basis generated) parameters
    rw [← recovered] at accepted
    exact (formula_eval_restrict formula (Gates.coordinate (Table.coordinates n basis) (extendAssignment parameters))) ▸ accepted

theorem compile_correct {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (generated : Atoms.generate formula = .basis basis) :
    FunctionalSubstitution.decideProgram (compile formula basis) = true ↔ CNFSatisfiable formula := by
  rw [compile, FunctionalSubstitution.prepare_correct _ _
    (candidates_entails formula basis (Atoms.generated_within formula basis generated))]
  exact initial_satisfiable formula basis generated

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

theorem literalBody_small {n : Nat} (coordinates : Array Row) (literal : CNFLiteral n) :
    BooleanValues.Code (literalBody coordinates literal).code := by
  unfold literalBody
  split
  · exact BooleanValues.compile_row _
  · exact BooleanValues.fragment_not _ (BooleanValues.compile_row _)

theorem body_small {n : Nat} (coordinates : Array Row) (relation : Relation n) :
    BooleanValues.Code (body coordinates relation).code := by
  have both := BooleanValues.fragment_and _ _ (literalBody_small coordinates relation.left)
    (literalBody_small coordinates relation.right)
  unfold body
  split
  · exact both
  · exact BooleanValues.fragment_not _ both

theorem candidate_small {n : Nat} (formula : CNFFormula n) (basis : List Row) (call : Instruction)
    (member : call ∈ candidates formula basis) : BooleanValues.Code call.body.code := by
  obtain ⟨relation, _, found⟩ := List.mem_filterMap.mp member
  unfold instruction at found
  split at found
  · cases Option.some.inj found
    exact body_small _ _
  · cases found

theorem compile_small {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    BooleanValues.Code (compile formula basis).code :=
  FunctionalSubstitution.execute_small _ _ (BooleanValues.acceptance _ formula)
    (fun call member => candidate_small formula basis call
      ((FunctionalSubstitution.select_sublist [] _).subset member))

theorem close_small {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    BooleanValues.Code (FunctionalSubstitution.close (Cone.pruneCone (compile formula basis))).code :=
  BooleanValues.boolean_fold _ _ (BooleanValues.pruneCone _ (compile_small formula basis))

theorem literalBody_size {n : Nat} (coordinates : Array Row) (literal : CNFLiteral n) :
    (literalBody coordinates literal).code.size ≤ 2 + 2 * (coordinates.getD literal.var.val Gates.zeroRow).vars.length := by
  have size := Gates.compileRow_size (coordinates.getD literal.var.val Gates.zeroRow)
  cases polarity : literal.positive <;>
    simp only [literalBody, polarity, Bool.false_eq_true, if_false, if_true,
      Fragment.not, Fragment.unary, Array.size_push] <;> omega

theorem body_size {n : Nat} (basis : List Row) (relation : Relation n) :
    (body (Table.coordinates n basis) relation).code.size ≤ 6 + 4 * n := by
  have width : (freeIndices n basis).length ≤ n := by
    simpa only [freeIndices, List.length_range] using List.length_filter_le
      (fun i => decide (i ∉ pivots basis)) (List.range n)
  have leftRow := Table.row_length_le _ _ (Table.read_valid _ _ (Table.coordinates_valid n basis) relation.left.var.val)
  have rightRow := Table.row_length_le _ _ (Table.read_valid _ _ (Table.coordinates_valid n basis) relation.right.var.val)
  have left := literalBody_size (Table.coordinates n basis) relation.left
  have right := literalBody_size (Table.coordinates n basis) relation.right
  cases polarity : relation.output.positive <;>
    simp only [body, polarity, Bool.false_eq_true, if_false, if_true,
      Fragment.not, Fragment.unary, Fragment.and, Fragment.binary,
      Array.size_push, Array.size_append, Array.size_map] <;> omega

theorem candidates_length {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (candidates formula basis).length ≤ 3 * formula.length :=
  (List.length_filterMap_le _ _).trans (FunctionalRelations.extract_length formula)

theorem candidate_size {n : Nat} (formula : CNFFormula n) (basis : List Row) (call : Instruction)
    (member : call ∈ candidates formula basis) : call.body.code.size ≤ 6 + 4 * n := by
  obtain ⟨relation, _, found⟩ := List.mem_filterMap.mp member
  unfold instruction at found
  split at found
  · cases Option.some.inj found
    exact body_size _ _
  · cases found

theorem candidates_size {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    ((candidates formula basis).map (·.body.code.size)).sum ≤ 3 * formula.length * (6 + 4 * n) := by
  have bound : ∀ calls : List Instruction, (∀ call ∈ calls, call.body.code.size ≤ 6+4*n) →
      (calls.map (·.body.code.size)).sum ≤ calls.length * (6+4*n) := by
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
      3 + n + 2*n*n + 3*formula.length + 3*SATJoint.literalCount formula + 3*formula.length*(6+4*n) := by
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

def legal (instructions : List Instruction) (environment : Nat → Bool) : Bool :=
  instructions.all (fun call => environment call.address == truth (call.body.eval environment))

theorem legal_fixed (instructions : List Instruction) (environment : Nat → Bool)
    (accepted : legal instructions environment = true) :
    FunctionalSubstitution.fill instructions environment = environment := by
  apply FunctionalSubstitution.fill_fixes
  intro call member
  apply FunctionalSubstitution.bind_fixes
  exact beq_iff_eq.mp ((List.all_eq_true.mp accepted) call member)

theorem legal_of_fixed (instructions : List Instruction) (environment : Nat → Bool)
    (fixed : ∀ call ∈ instructions, call.bind environment = environment) : legal instructions environment = true := by
  apply List.all_eq_true.mpr
  intro call member
  have value := congrFun (fixed call member) call.address
  simp only [Instruction.bind, FunctionalSubstitution.bind, Function.update_self] at value
  exact beq_iff_eq.mpr value.symm

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
    if holds basis (extendAssignment assignment) && legal (selected formula basis) environment then source environment else 0

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
  by_cases guard : holds basis (extendAssignment assignment) = true ∧ legal (selected formula basis) environment = true
  · have filled := legal_fixed (selected formula basis) environment guard.2
    have restored : lift formula basis environment = assignment := by
      funext i
      change Gates.coordinate (Table.coordinates n basis)
        (FunctionalSubstitution.fill (selected formula basis) environment) i.val = assignment i
      rw [filled]
      exact congrFun (recovery guard.1) i
    have value : (compile formula basis).eval environment =
        bit (CNFFormula.eval formula (extendAssignment assignment)) := by rw [compile_value, restored]
    rw [zeroProjector_apply]
    change _ = if (holds basis (extendAssignment assignment) && legal (selected formula basis) environment) = true
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
      refine ⟨relations, legal_of_fixed _ _ ?_⟩
      intro call member
      apply candidates_entails formula basis inside environment
      · rw [initial relations, truth_bit]
        exact accepted
      · exact (FunctionalSubstitution.select_sublist [] _).subset member
    rw [zeroProjector_apply]
    simp only [zeroExtension]
    have failed : (holds basis (extendAssignment assignment) && legal (selected formula basis) environment) = false := by
      simpa only [Bool.and_eq_false_iff, Bool.not_eq_true, not_and_or] using guard
    simp only [show extendAssignment (projectFree n basis assignment) = environment from rfl, failed]
    simp [rejected]

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalAffine

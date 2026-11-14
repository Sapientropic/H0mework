import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Row
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Decision

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.Gates

open InterferenceProgram

def zeroRow : Row := ⟨[], false⟩

def value (row : Row) (environment : Nat → Bool) : Bool :=
  row.rhs ^^ row.eval environment

def coordinate (coordinates : Array Row) (environment : Nat → Bool) (i : Nat) : Bool :=
  value (coordinates.toList.getD i zeroRow) environment

def compileTerms : List Nat → Fragment → Fragment
  | [], initial => initial
  | i :: rest, initial => compileTerms rest (initial.xor (Fragment.input i))

def compileRow (row : Row) : Fragment :=
  compileTerms row.vars (Fragment.constant (bit row.rhs))

theorem eval_compileTerms (terms : List Nat) (initial : Fragment) (environment : Nat → Bool)
    (first : Bool) (initialValue : initial.eval environment = bit first) :
    (compileTerms terms initial).eval environment = bit (first ^^ Parity.eval environment terms) := by
  induction terms generalizing initial first with
  | nil => simpa [compileTerms, Parity.eval] using initialValue
  | cons i rest ih =>
      rw [compileTerms]
      have next : (initial.xor (Fragment.input i)).eval environment =
          bit (first ^^ environment i) := by simp only [Fragment.eval_xor, Fragment.eval_input,
            initialValue, truth_bit]
      rw [ih _ _ next]
      simp only [Parity.eval, Bool.xor_assoc]

theorem eval_compileRow (row : Row) (environment : Nat → Bool) :
    (compileRow row).eval environment = bit (value row environment) :=
  eval_compileTerms row.vars _ environment row.rhs (Fragment.eval_constant environment _)

theorem compileTerms_size (terms : List Nat) (initial : Fragment) :
    (compileTerms terms initial).code.size = initial.code.size + 2 * terms.length := by
  induction terms generalizing initial with
  | nil => simp [compileTerms]
  | cons i rest ih =>
      simp [compileTerms, ih, Fragment.xor, Fragment.binary, Fragment.input]
      omega

theorem compileRow_size (row : Row) :
    (compileRow row).code.size = 1 + 2 * row.vars.length := by
  simp [compileRow, compileTerms_size, Fragment.constant]

structure CoordinateCode where
  code : Array Node
  outputs : List Nat
  deriving Repr

/-- A row is appended once; all original literal occurrences will use its output address. -/
def compileRows : List Row → CoordinateCode
  | [] => ⟨#[.constant 0], []⟩
  | row :: rest =>
      let previous := compileRows rest
      let generated := compileRow row
      ⟨join previous.code generated.code,
        (previous.code.size + generated.output.val) :: previous.outputs⟩

theorem compileRows_nonempty (rows : List Row) : 0 < (compileRows rows).code.size := by
  cases rows with
  | nil => simp [compileRows]
  | cons row rest =>
      simp only [compileRows, join_size]
      have positive := (compileRow row).output.isLt
      omega

theorem compileRows_outputs_length (rows : List Row) :
    (compileRows rows).outputs.length = rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp [compileRows, ih]

theorem compileRows_output_bound (rows : List Row) (i : Nat) :
    (compileRows rows).outputs.getD i 0 < (compileRows rows).code.size := by
  induction rows generalizing i with
  | nil => simp [compileRows]
  | cons row rest ih =>
      cases i with
      | zero =>
          simp only [compileRows, List.getD_cons_zero, join_size]
          exact Nat.add_lt_add_left (compileRow row).output.isLt _
      | succ i =>
          simp only [compileRows, List.getD_cons_succ, join_size]
          exact Nat.lt_of_lt_of_le (ih i) (Nat.le_add_right _ _)

theorem compileRows_zero (rows : List Row) (environment : Nat → Bool) :
    (run environment (compileRows rows).code).getD 0 0 = 0 := by
  induction rows with
  | nil => simp [compileRows, run, runCode, Node.run, Array.getD]
  | cons row rest ih =>
      simp only [compileRows, run_join']
      rw [getD_append_left _ _ _ (by simpa using compileRows_nonempty rest), ih]

theorem eval_compileRows (rows : List Row) (environment : Nat → Bool) (i : Nat) :
    (run environment (compileRows rows).code).getD ((compileRows rows).outputs.getD i 0) 0 =
      bit (value (rows.getD i zeroRow) environment) := by
  induction rows generalizing i with
  | nil => simp [compileRows, run, runCode, Node.run, Array.getD, zeroRow, value, Row.eval,
      Parity.eval, bit]
  | cons row rest ih =>
      cases i with
      | zero =>
          simp only [compileRows, List.getD_cons_zero, run_join']
          rw [← run_size environment (compileRows rest).code, getD_append_right]
          exact eval_compileRow row environment
      | succ i =>
          simp only [compileRows, List.getD_cons_succ, run_join']
          rw [getD_append_left _ _ _ (by simpa using compileRows_output_bound rest i)]
          exact ih i

def originalEnvironment (n freeWidth : Nat) (coordinates : Array Row)
    (environment : Nat → Bool) : Nat → Bool :=
  fun i => if i < n then coordinate coordinates environment i else environment (freeWidth + (i - n))

/-- The same recursive lookup supplies the coordinate address and its visited cells. -/
def lookup : List Nat → Nat → Nat × Nat
  | [], _ => (0, 1)
  | value :: _, 0 => (value, 1)
  | _ :: rest, i + 1 => let next := lookup rest i; (next.1, next.2 + 1)

theorem lookup_value (outputs : List Nat) (i : Nat) : (lookup outputs i).1 = outputs.getD i 0 := by
  induction outputs generalizing i with
  | nil => simp [lookup]
  | cons value rest ih => cases i <;> simp [lookup, ih]

theorem lookup_visits (outputs : List Nat) (i : Nat) : (lookup outputs i).2 ≤ outputs.length + 1 := by
  induction outputs generalizing i with
  | nil => simp [lookup]
  | cons value rest ih =>
      cases i with
      | zero => simp only [lookup, List.length_cons]; omega
      | succ i =>
          simp only [lookup, List.length_cons]
          have bound := ih i
          omega

def rewriteNode (n freeWidth size : Nat) (outputs : List Nat) : Node → Node
  | .input i => if i < n then .bxor (lookup outputs i).1 0 else .input (freeWidth + (i - n))
  | node => node.shift size

theorem run_rewriteNode (n freeWidth : Nat) (coordinates : Array Row)
    (environment : Nat → Bool) (values : Array ℤ) (node : Node) :
    (rewriteNode n freeWidth (compileRows coordinates.toList).code.size
      (compileRows coordinates.toList).outputs node).run environment
      (run environment (compileRows coordinates.toList).code ++ values) =
    node.run (originalEnvironment n freeWidth coordinates environment) values := by
  cases node <;> simp only [rewriteNode]
  case input i =>
    by_cases source : i < n
    · simp only [source, if_true, Node.run, lookup_value]
      rw [getD_append_left _ _ _ (by simpa using compileRows_output_bound coordinates.toList i),
        getD_append_left _ _ 0 (by simpa using compileRows_nonempty coordinates.toList),
        eval_compileRows, compileRows_zero]
      simp only [truth_bit]
      change bit (value (coordinates.toList.getD i zeroRow) environment ^^ false) = _
      simp only [Bool.xor_false, originalEnvironment, if_pos source, coordinate]
    · simp [source, originalEnvironment, Node.run]
  all_goals
    rw [← run_size environment (compileRows coordinates.toList).code, Node.run_shift]
    rfl

theorem runCode_rewrite (n freeWidth : Nat) (coordinates : Array Row)
    (environment : Nat → Bool) (values : Array ℤ) (code : List Node) :
    runCode environment (run environment (compileRows coordinates.toList).code ++ values)
      (code.map (rewriteNode n freeWidth (compileRows coordinates.toList).code.size
        (compileRows coordinates.toList).outputs)) =
      run environment (compileRows coordinates.toList).code ++
        runCode (originalEnvironment n freeWidth coordinates environment) values code := by
  induction code generalizing values with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.map_cons, runCode, run_rewriteNode, push_append]
      exact ih _

def compile {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) : Program :=
  let source := compileRows coordinates.toList
  let original := InterferenceProgram.compile formula
  let code := source.code ++ original.code.map (rewriteNode n freeWidth source.code.size source.outputs)
  ⟨code,
    ⟨source.code.size + original.weight.val, by
      simpa only [code, Array.size_append, Array.size_map] using
        Nat.add_lt_add_left original.weight.isLt source.code.size⟩,
    ⟨source.code.size + original.phase.val, by
      simpa only [code, Array.size_append, Array.size_map] using
        Nat.add_lt_add_left original.phase.isLt source.code.size⟩⟩

theorem run_compile {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) (environment : Nat → Bool) :
    run environment (compile freeWidth coordinates formula).code =
      run environment (compileRows coordinates.toList).code ++
        run (originalEnvironment n freeWidth coordinates environment) (InterferenceProgram.compile formula).code := by
  simp only [compile, run, Array.toList_append, Array.toList_map, runCode_append]
  have equation := runCode_rewrite n freeWidth coordinates environment #[]
    (InterferenceProgram.compile formula).code.toList
  simp only [Array.append_empty] at equation
  exact equation

theorem eval_compile {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) (environment : Nat → Bool) :
    (compile freeWidth coordinates formula).eval environment =
      (InterferenceProgram.compile formula).eval (originalEnvironment n freeWidth coordinates environment) := by
  simp only [Program.eval]
  rw [run_compile]
  simp only [compile]
  rw [← run_size environment (compileRows coordinates.toList).code,
    getD_append_right, getD_append_right]

def Bounded (freeWidth : Nat) (coordinates : Array Row) : Prop :=
  ∀ row ∈ coordinates.toList, Parity.Within freeWidth row.vars

theorem getD_within (freeWidth : Nat) (rows : List Row)
    (inside : ∀ row ∈ rows, Parity.Within freeWidth row.vars) (i : Nat) :
    Parity.Within freeWidth (rows.getD i zeroRow).vars := by
  induction rows generalizing i with
  | nil => simp [zeroRow, Parity.Within]
  | cons row rest ih =>
      cases i with
      | zero => exact inside row (by simp)
      | succ i => exact ih (fun value hit => inside value (by simp [hit])) i

theorem coordinate_pack {freeWidth m : Nat} (coordinates : Array Row)
    (inside : Bounded freeWidth coordinates) (assignment : Assignment freeWidth)
    (dual : Fin m → Bool) (i : Nat) :
    coordinate coordinates (PhaseSource.pack assignment dual) i =
      coordinate coordinates (extendAssignment assignment) i := by
  unfold coordinate value Row.eval
  congr 1
  apply Parity.eval_congr
  intro address hit
  have valid := getD_within freeWidth coordinates.toList inside i address hit
  exact (PhaseSource.pack_source assignment dual ⟨address, valid⟩).trans
    (extendAssignment_apply assignment ⟨address, valid⟩).symm

def lift {freeWidth : Nat} (n : Nat) (coordinates : Array Row)
    (assignment : Assignment freeWidth) : Assignment n :=
  fun i => coordinate coordinates (extendAssignment assignment) i.val

theorem originalEnvironment_pack {n freeWidth m : Nat} (coordinates : Array Row)
    (inside : Bounded freeWidth coordinates) (assignment : Assignment freeWidth)
    (dual : Fin m → Bool) :
    originalEnvironment n freeWidth coordinates (PhaseSource.pack assignment dual) =
      PhaseSource.pack (lift n coordinates assignment) dual := by
  funext i
  by_cases source : i < n
  · simp only [originalEnvironment, if_pos source, PhaseSource.pack, dif_pos source]
    exact coordinate_pack coordinates inside assignment dual i
  · have outside : ¬ freeWidth + (i - n) < freeWidth := by omega
    simp only [originalEnvironment, if_neg source, PhaseSource.pack, dif_neg source,
      dif_neg outside, Nat.add_sub_cancel_left]

theorem eval_compile_pack {n freeWidth : Nat} (coordinates : Array Row)
    (inside : Bounded freeWidth coordinates) (formula : CNFFormula n)
    (assignment : Assignment freeWidth) (dual : Fin formula.length → Bool) :
    (compile freeWidth coordinates formula).eval (PhaseSource.pack assignment dual) =
      PhaseSource.phaseSign formula (lift n coordinates assignment) dual := by
  rw [eval_compile, originalEnvironment_pack coordinates inside,
    InterferenceDecision.eval_compile_pack]

open scoped BigOperators

/-- The sum is the semantic consumer of the emitted finite program. -/
theorem dual_sum {n freeWidth : Nat} (coordinates : Array Row)
    (inside : Bounded freeWidth coordinates) (formula : CNFFormula n)
    (assignment : Assignment freeWidth) :
    (∑ dual : Fin formula.length → Bool,
      (compile freeWidth coordinates formula).eval (PhaseSource.pack assignment dual)) =
      (2 : ℤ) ^ formula.length *
        if CNFFormula.eval formula (extendAssignment (lift n coordinates assignment)) then 1 else 0 := by
  simp only [eval_compile_pack coordinates inside]
  exact PhaseSource.dual_sum formula (lift n coordinates assignment)

theorem dual_action {n freeWidth : Nat} (coordinates : Array Row)
    (inside : Bounded freeWidth coordinates) (formula : CNFFormula n)
    (source : Source n) (assignment : Assignment freeWidth) :
    (∑ dual : Fin formula.length → Bool,
      ((compile freeWidth coordinates formula).eval (PhaseSource.pack assignment dual) : ℚ) *
        source (lift n coordinates assignment)) =
      (2 : ℚ) ^ formula.length * zeroProjector formula source (lift n coordinates assignment) := by
  have original := congrFun (PhaseSource.dualAction_eq_projector formula source)
    (lift n coordinates assignment)
  simpa only [PhaseSource.dualAction, eval_compile_pack coordinates inside, Pi.smul_apply,
    smul_eq_mul] using original

def rowTerms (rows : List Row) : Nat := (rows.map (fun row => row.vars.length)).sum

theorem compileRows_size (rows : List Row) :
    (compileRows rows).code.size = 1 + rows.length + 2 * rowTerms rows := by
  induction rows with
  | nil => simp [compileRows, rowTerms]
  | cons row rest ih =>
      simp only [compileRows, join_size, compileRow_size, ih, List.length_cons,
        rowTerms, List.map_cons, List.sum_cons]
      simp only [rowTerms] at ih
      omega

def nodeBudget {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) : Nat :=
  3 + coordinates.size + 2 * rowTerms coordinates.toList +
    4 * formula.length + 3 * SATJoint.literalCount formula

theorem compile_size {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) :
    (compile freeWidth coordinates formula).code.size ≤ nodeBudget coordinates formula := by
  have original := InterferenceDecision.compile_size formula
  simp only [compile, Array.size_append, Array.size_map, compileRows_size,
    Array.length_toList, nodeBudget]
  omega

def sharedCompile {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) : Program := (compile freeWidth coordinates formula).share

theorem eval_sharedCompile {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) (environment : Nat → Bool) :
    (sharedCompile freeWidth coordinates formula).eval environment =
      (InterferenceProgram.compile formula).eval
        (originalEnvironment n freeWidth coordinates environment) := by
  rw [sharedCompile, Program.eval_share, eval_compile]

theorem sharedCompile_forward {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) : Reduce.Forward (sharedCompile freeWidth coordinates formula).code :=
  Program.share_forward _

theorem sharedCompile_size {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) :
    (sharedCompile freeWidth coordinates formula).code.size ≤ nodeBudget coordinates formula + 1 := by
  exact (Program.share_size _).trans (Nat.add_le_add_right (compile_size _ _ _) 1)

theorem sharedCompile_refs {n : Nat} (freeWidth : Nat) (coordinates : Array Row)
    (formula : CNFFormula n) (i : Nat)
    (index : i < (sharedCompile freeWidth coordinates formula).code.size)
    (reference : Nat)
    (used : reference ∈ (sharedCompile freeWidth coordinates formula).code[i].refs) :
    reference < nodeBudget coordinates formula + 1 :=
  (sharedCompile_forward freeWidth coordinates formula i index reference used).trans_le
    (Nat.le_trans (Nat.le_of_lt index) (sharedCompile_size freeWidth coordinates formula))

theorem eval_sharedCompile_pack {n freeWidth : Nat} (coordinates : Array Row)
    (inside : Bounded freeWidth coordinates) (formula : CNFFormula n)
    (assignment : Assignment freeWidth) (dual : Fin formula.length → Bool) :
    (sharedCompile freeWidth coordinates formula).eval (PhaseSource.pack assignment dual) =
      PhaseSource.phaseSign formula (lift n coordinates assignment) dual := by
  rw [sharedCompile, Program.eval_share, eval_compile_pack coordinates inside]

/-- Source lookups and opcode/reference-field visits of the actual rewrite pass. -/
def rewriteNodeVisits (n : Nat) (outputs : List Nat) : Node → Nat
  | .input i => if i < n then (lookup outputs i).2 + 3 else 3
  | node => node.refs.length + 1

theorem rewriteNodeVisits_bound (n : Nat) (outputs : List Nat) (node : Node) :
    rewriteNodeVisits n outputs node ≤ outputs.length + 4 := by
  cases node <;> simp only [rewriteNodeVisits, Node.refs, List.length_cons, List.length_nil]
  case input i =>
    have bound := lookup_visits outputs i
    split <;> omega
  all_goals omega

def rewriteVisits (n : Nat) (outputs : List Nat) : List Node → Nat
  | [] => 1
  | node :: rest => rewriteNodeVisits n outputs node + rewriteVisits n outputs rest + 1

theorem rewriteVisits_bound (n : Nat) (outputs : List Nat) (code : List Node) :
    rewriteVisits n outputs code ≤ code.length * (outputs.length + 5) + 1 := by
  induction code with
  | nil => simp [rewriteVisits]
  | cons node rest ih =>
      have first := rewriteNodeVisits_bound n outputs node
      simp only [rewriteVisits, List.length_cons]
      nlinarith

def compileRewriteVisits {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) : Nat :=
  rewriteVisits n (compileRows coordinates.toList).outputs (InterferenceProgram.compile formula).code.toList

theorem compileRewriteVisits_bound {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) :
    compileRewriteVisits coordinates formula ≤
      (2 + 4 * formula.length + 3 * SATJoint.literalCount formula) * (coordinates.size + 5) + 1 := by
  have visits := rewriteVisits_bound n (compileRows coordinates.toList).outputs
    (InterferenceProgram.compile formula).code.toList
  have size := InterferenceDecision.compile_size formula
  simp only [compileRows_outputs_length, Array.length_toList] at visits
  unfold compileRewriteVisits
  nlinarith

/-- Each binary constructor shifts its already-built right fragment once. -/
def clauseShifts {n : Nat} : CNFClause n → Nat
  | [] => 0
  | _ :: rest => clauseShifts rest + (compileClause rest).code.size

theorem clauseShifts_bound {n : Nat} (clause : CNFClause n) :
    clauseShifts clause ≤ (compileClause clause).code.size ^ 2 := by
  induction clause with
  | nil => simp [clauseShifts]
  | cons literal rest ih =>
      have positive : 0 < (compileLiteral literal).code.size :=
        Nat.zero_lt_of_lt (compileLiteral literal).output.isLt
      simp only [clauseShifts, compileClause, Fragment.and, Fragment.binary,
        Array.size_push, Array.size_append, Array.size_map]
      nlinarith

def phaseShifts {n : Nat} (offset : Nat) : CNFFormula n → Nat
  | [] => 0
  | clause :: rest => clauseShifts clause + phaseShifts (offset + 1) rest +
      (compileClause clause).code.size + (compilePhase (offset + 1) rest).code.size

theorem phaseShifts_bound {n : Nat} (formula : CNFFormula n) (offset : Nat) :
    phaseShifts offset formula ≤ (compilePhase offset formula).code.size ^ 2 := by
  induction formula generalizing offset with
  | nil => simp [phaseShifts]
  | cons clause rest ih =>
      have clauseBound := clauseShifts_bound clause
      have tail := ih (offset + 1)
      simp only [phaseShifts, compilePhase, Fragment.xor, Fragment.and, Fragment.binary,
        Fragment.input, Array.size_push, Array.size_append, Array.size_map]
      simp only [Array.size, List.length_cons, List.length_nil] at *
      nlinarith

def coordinateShifts : List Row → Nat
  | [] => 0
  | row :: rest => row.vars.length + (compileRow row).code.size + coordinateShifts rest

theorem coordinateShifts_eq (rows : List Row) :
    coordinateShifts rows = rows.length + 3 * rowTerms rows := by
  induction rows with
  | nil => simp [coordinateShifts, rowTerms]
  | cons row rest ih =>
      simp only [coordinateShifts, compileRow_size, ih, List.length_cons,
        rowTerms, List.map_cons, List.sum_cons]
      omega

/-- This ledger counts source list cells, shifted node records and the rewrite's index reads.
Array allocation, integer/address bit operations, and an optional `share` pass have their own costs. -/
def constructionVisits {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) : Nat :=
  coordinates.size + rowTerms coordinates.toList + formula.length + SATJoint.literalCount formula +
    coordinateShifts coordinates.toList + phaseShifts n formula + compileRewriteVisits coordinates formula

theorem constructionVisits_bound {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) :
    constructionVisits coordinates formula ≤
      2 * coordinates.size + 4 * rowTerms coordinates.toList + formula.length + SATJoint.literalCount formula +
      (1 + 4 * formula.length + 3 * SATJoint.literalCount formula) ^ 2 +
      (2 + 4 * formula.length + 3 * SATJoint.literalCount formula) * (coordinates.size + 5) + 1 := by
  have shifts := phaseShifts_bound formula n
  have size := InterferenceDecision.compilePhase_size formula n
  have rewriteBound := compileRewriteVisits_bound coordinates formula
  simp only [constructionVisits, coordinateShifts_eq, Array.length_toList]
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.Affine.Gates

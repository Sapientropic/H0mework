import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.PhaseSource
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Encoding
import Mathlib.Logic.Equiv.Fin.Basic
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Program
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.Shared

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceDecision

open scoped BigOperators

/-- Semantic finite binding, kept outside the executable DAG driver. -/
def sumOver : List Nat → ((Nat → Bool) → ℤ) → (Nat → Bool) → ℤ
  | [], value, environment => value environment
  | address :: rest, value, environment =>
      sumOver rest value (Function.update environment address false) +
      sumOver rest value (Function.update environment address true)

theorem sumOver_congr (addresses : List Nat) (left right : (Nat → Bool) → ℤ)
    (same : ∀ environment, left environment = right environment) (environment : Nat → Bool) :
    sumOver addresses left environment = sumOver addresses right environment := by
  induction addresses generalizing environment with
  | nil => exact same environment
  | cons address rest ih => simp only [sumOver, ih]

theorem sumOver_add (addresses : List Nat) (left right : (Nat → Bool) → ℤ)
    (environment : Nat → Bool) :
    sumOver addresses (fun env => left env + right env) environment =
      sumOver addresses left environment + sumOver addresses right environment := by
  induction addresses generalizing environment with
  | nil => rfl
  | cons address rest ih => simp only [sumOver, ih]; ring

/-- Fill precisely one original contiguous address block. -/
def fill {width : Nat} (environment : Nat → Bool) (offset : Nat)
    (values : Fin width → Bool) : Nat → Bool :=
  fun address => if h : offset ≤ address ∧ address < offset + width
    then values ⟨address-offset, by omega⟩ else environment address

@[simp] theorem fill_inside {width : Nat} (environment : Nat → Bool) (offset : Nat)
    (values : Fin width → Bool) (index : Fin width) :
    fill environment offset values (offset+index.val) = values index := by
  simp [fill, index.isLt]

theorem fill_outside {width : Nat} (environment : Nat → Bool) (offset : Nat)
    (values : Fin width → Bool) (address : Nat)
    (outside : ¬(offset ≤ address ∧ address < offset + width)) :
    fill environment offset values address = environment address := by
  simp [fill, outside]

@[simp] theorem fill_zero (environment : Nat → Bool) (offset : Nat)
    (values : Fin 0 → Bool) : fill environment offset values = environment := by
  funext address
  simp [fill]

theorem fill_succ {width : Nat} (environment : Nat → Bool) (offset : Nat)
    (head : Bool) (tail : Fin width → Bool) :
    fill environment offset (Fin.cons head tail) =
      fill (Function.update environment offset head) (offset+1) tail := by
  funext address
  by_cases atHead : address = offset
  · subst address
    simp [fill]
  · by_cases inside : offset ≤ address ∧ address < offset + (width+1)
    · have insideTail : offset+1 ≤ address ∧ address < offset+1+width := by omega
      simp only [fill, dif_pos inside, dif_pos insideTail]
      have index : (⟨address-offset, by omega⟩ : Fin (width+1)) =
          (⟨address-(offset+1), by omega⟩ : Fin width).succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [index, Fin.cons_succ]
    · have outsideTail : ¬(offset+1 ≤ address ∧ address < offset+1+width) := by omega
      simp only [fill, dif_neg inside, dif_neg outsideTail]
      exact (Function.update_of_ne atHead _ _).symm

theorem sum_finite_cons {width : Nat} (value : (Fin (width+1) → Bool) → ℤ) :
    (∑ values : Fin (width+1) → Bool, value values) =
      (∑ tail : Fin width → Bool, value (Fin.cons false tail)) +
      (∑ tail : Fin width → Bool, value (Fin.cons true tail)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (width+1) => Bool)).sum_comp value]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  exact add_comm _ _

theorem sumOver_rangeFrom (width offset : Nat) (value : (Nat → Bool) → ℤ)
    (environment : Nat → Bool) :
    sumOver (List.range' offset width) value environment =
      ∑ values : Fin width → Bool, value (fill environment offset values) := by
  induction width generalizing offset environment with
  | zero => simp [sumOver]
  | succ width ih =>
      rw [List.range'_succ, sumOver, ih, ih, sum_finite_cons]
      simp only [fill_succ]

theorem sumOver_range (width : Nat) (value : (Nat → Bool) → ℤ)
    (environment : Nat → Bool) :
    sumOver (List.range width) value environment =
      ∑ values : Fin width → Bool, value (fill environment 0 values) := by
  simpa only [List.range_eq_range'] using sumOver_rangeFrom width 0 value environment

def zeroEnvironment : Nat → Bool := fun _ => false

theorem fill_append_pack {n m : Nat} (assignment : Assignment n) (dual : Fin m → Bool) :
    fill zeroEnvironment 0 (Fin.append assignment dual) = PhaseSource.pack assignment dual := by
  funext address
  by_cases first : address < n
  · have inside : 0 ≤ address ∧ address < 0+(n+m) := by omega
    simp only [fill, dif_pos inside, Nat.sub_zero, PhaseSource.pack, dif_pos first]
    exact Fin.append_left assignment dual ⟨address, first⟩
  · by_cases second : address-n < m
    · have inside : 0 ≤ address ∧ address < 0+(n+m) := by omega
      simp only [fill, dif_pos inside, Nat.sub_zero, PhaseSource.pack, dif_neg first, dif_pos second]
      have index : (⟨address, by omega⟩ : Fin (n+m)) =
          Fin.natAdd n (⟨address-n, second⟩ : Fin m) := by
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
      rw [index, Fin.append_right]
    · have outside : ¬(0 ≤ address ∧ address < 0+(n+m)) := by omega
      simp only [fill, dif_neg outside, PhaseSource.pack, dif_neg first, dif_neg second]
      rfl

theorem sumOver_range_pack (n m : Nat) (value : (Nat → Bool) → ℤ) :
    sumOver (List.range (n+m)) value zeroEnvironment =
      ∑ assignment : Assignment n, ∑ dual : Fin m → Bool,
        value (PhaseSource.pack assignment dual) := by
  rw [sumOver_range]
  rw [← (Fin.appendEquiv n m).sum_comp (fun values => value (fill zeroEnvironment 0 values))]
  rw [Fintype.sum_prod_type]
  change (∑ assignment : Assignment n, ∑ dual : Fin m → Bool,
    value (fill zeroEnvironment 0 (Fin.append assignment dual))) = _
  simp only [fill_append_pack]

open InterferenceProgram

theorem sign_bit (value : Bool) : InterferenceProgram.sign (InterferenceProgram.bit value) =
    PhaseSource.sign value := by
  cases value <;> rfl

theorem phaseValue_sign {n : Nat} (formula : CNFFormula n) (offset : Nat)
    (environment : Nat → Bool) :
    PhaseSource.sign (phaseValue offset environment formula) =
      ∏ j : Fin formula.length,
        PhaseSource.sign (environment (offset+j.val) && !(CNFClause.eval (formula.get j) environment)) := by
  induction formula generalizing offset with
  | nil => simp [phaseValue]
  | cons clause rest ih =>
      change PhaseSource.sign (phaseValue offset environment (clause::rest)) =
        ∏ j : Fin (rest.length+1), PhaseSource.sign
          (environment (offset+j.val) && !(CNFClause.eval ((clause::rest).get j) environment))
      rw [phaseValue, PhaseSource.sign_xor, Fin.prod_univ_succ
        (fun j : Fin (rest.length+1) => PhaseSource.sign
          (environment (offset+j.val) && !(CNFClause.eval ((clause::rest).get j) environment))), ih]
      simp only [Fin.val_zero, Nat.add_zero, List.get_cons_zero, Fin.val_succ]
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      congr 3
      omega

theorem clause_eval_pack {n m : Nat} (clause : CNFClause n) (assignment : Assignment n)
    (dual : Fin m → Bool) :
    CNFClause.eval clause (PhaseSource.pack assignment dual) =
      CNFClause.eval clause (extendAssignment assignment) := by
  unfold CNFClause.eval
  congr 1
  funext literal
  simp only [CNFLiteral.eval, PhaseSource.pack_source, extendAssignment_apply]

theorem eval_compile_pack {n : Nat} (formula : CNFFormula n) (assignment : Assignment n)
    (dual : Fin formula.length → Bool) :
    (compile formula).eval (PhaseSource.pack assignment dual) = PhaseSource.phaseSign formula assignment dual := by
  rw [eval_compile, sign_bit, phaseValue_sign]
  unfold PhaseSource.phaseSign PhaseSource.character PhaseSource.residual
  apply Finset.prod_congr rfl
  intro j _
  rw [PhaseSource.pack_dual, clause_eval_pack]

/-- Reuse the same generated code and add the two actual root-value operations. -/
def amplitude (program : Program) : Fragment :=
  let phase : Fragment := ⟨program.code, program.phase⟩
  (phase.unary Node.phase).unary (fun signRef => Node.mul program.weight.val signRef)

theorem amplitude_size (program : Program) :
    (amplitude program).code.size = program.code.size+2 := by simp [amplitude, Fragment.unary]

theorem eval_amplitude (program : Program) (environment : Nat → Bool) :
    (amplitude program).eval environment = program.eval environment := by
  change (((⟨program.code, program.phase⟩ : Fragment).unary Node.phase).unary
    (fun signRef => Node.mul program.weight.val signRef)).eval environment = _
  rw [Fragment.eval_unary]
  change (run environment (program.code.push (.phase program.phase.val))).getD program.weight.val 0 *
    (run environment (program.code.push (.phase program.phase.val))).getD program.code.size 0 = _
  rw [run_push]
  rw [getD_push_old _ _ _ (by simp)]
  have last := getD_push_last (run environment program.code)
    ((Node.phase program.phase.val).run environment (run environment program.code))
  rw [run_size] at last
  rw [last]
  rfl

def addFragments (left right : Fragment) : Fragment := left.binary right Node.add

theorem eval_addFragments (left right : Fragment) (environment : Nat → Bool) :
    (addFragments left right).eval environment = left.eval environment + right.eval environment := by
  rw [addFragments, Fragment.eval_binary]
  simp only [Node.run, ← run_size environment left.code, getD_append_right]
  rw [getD_append_left _ _ _ (by simp)]
  rfl

def fromAmplitude (fragment : Fragment) : Program :=
  ⟨fragment.code.push (.constant 0),
    ⟨fragment.output.val, by have h := fragment.output.isLt; simp only [Array.size_push]; omega⟩,
    ⟨fragment.code.size, by simp⟩⟩

theorem eval_fromAmplitude (fragment : Fragment) (environment : Nat → Bool) :
    (fromAmplitude fragment).eval environment = fragment.eval environment := by
  simp only [fromAmplitude, Program.eval, run_push, Node.run]
  rw [getD_push_old _ _ _ (by simp)]
  have last := getD_push_last (run environment fragment.code) (0 : ℤ)
  rw [run_size] at last
  rw [last]
  simp [InterferenceProgram.sign, Fragment.eval]

/-- The odd final address retains the complete amplitude of both cofactors. -/
def eliminateOne (program : Program) (address : Nat) : Program :=
  fromAmplitude (addFragments (amplitude (program.cofactor address false))
    (amplitude (program.cofactor address true)))

theorem eliminateOne_size (program : Program) (address : Nat) :
    (eliminateOne program address).code.size = 2*program.code.size+6 := by
  simp [eliminateOne, fromAmplitude, addFragments, Fragment.binary, amplitude_size]
  omega

theorem eval_eliminateOne (program : Program) (address : Nat) (environment : Nat → Bool) :
    (eliminateOne program address).eval environment =
      program.eval (Function.update environment address false) +
      program.eval (Function.update environment address true) := by
  rw [eliminateOne, eval_fromAmplitude, eval_addFragments, eval_amplitude, eval_amplitude,
    Program.eval_cofactor, Program.eval_cofactor]

/-- Tail-first execution matches the full nested binding, including repeated raw addresses. -/
def eliminateAll : List Nat → Program → Program
  | [], program => program
  | [address], program => (eliminateOne program address).share
  | left :: right :: rest, program => ((eliminateAll rest program).eliminatePair left right).share

theorem eval_eliminateAll (addresses : List Nat) (program : Program) (environment : Nat → Bool) :
    (eliminateAll addresses program).eval environment = sumOver addresses program.eval environment := by
  induction addresses using List.twoStepInduction generalizing environment with
  | nil => rfl
  | singleton address =>
      rw [eliminateAll, Program.eval_share, eval_eliminateOne]
      rfl
  | cons_cons left right rest ih =>
      rw [eliminateAll, Program.eval_share, Program.eval_eliminatePair]
      simp only [ih, sumOver]
      ring

def close {n : Nat} (formula : CNFFormula n) : Program :=
  eliminateAll (List.range (n+formula.length)) (compile formula)

theorem eval_close {n : Nat} (formula : CNFFormula n) :
    (close formula).eval zeroEnvironment = PhaseSource.numerator formula := by
  rw [close, eval_eliminateAll, sumOver_range_pack]
  simp only [eval_compile_pack, PhaseSource.numerator]

/-- The same source evaluator records each actual node invocation. -/
def runCounted (environment : Nat → Bool) : Array ℤ → List Node → Array ℤ × Nat
  | values, [] => (values, 0)
  | values, node :: rest =>
      let next := runCounted environment (values.push (node.run environment values)) rest
      (next.1, next.2+1)

theorem runCounted_eq (environment : Nat → Bool) (values : Array ℤ) (code : List Node) :
    runCounted environment values code = (runCode environment values code, code.length) := by
  induction code generalizing values with
  | nil => rfl
  | cons node rest ih => simp only [runCounted, ih, runCode, List.length_cons]

structure Reading where
  value : ℤ
  nodeVisits : Nat
  rootReads : Nat
  deriving Repr

/-- Two final array reads consume the same fully evaluated generated code. -/
def readProgram (program : Program) : Reading :=
  let execution := runCounted zeroEnvironment #[] program.code.toList
  let weight := execution.1.getD program.weight.val 0
  let phase := execution.1.getD program.phase.val 0
  ⟨weight * InterferenceProgram.sign phase, execution.2, 2⟩

theorem readProgram_value (program : Program) :
    (readProgram program).value = program.eval zeroEnvironment := by
  simp only [readProgram, runCounted_eq, Program.eval, run]

theorem readProgram_visits (program : Program) :
    (readProgram program).nodeVisits = program.code.size ∧
      (readProgram program).rootReads = 2 := by
  simp only [readProgram, runCounted_eq, Array.length_toList, and_self]

theorem readProgram_roots_inBounds (program : Program) :
    program.weight.val < (runCounted zeroEnvironment #[] program.code.toList).1.size ∧
      program.phase.val < (runCounted zeroEnvironment #[] program.code.toList).1.size := by
  rw [runCounted_eq]
  change program.weight.val < (run zeroEnvironment program.code).size ∧
    program.phase.val < (run zeroEnvironment program.code).size
  simp only [run_size, program.weight.isLt, program.phase.isLt, and_self]

def decideFormula {n : Nat} (formula : CNFFormula n) : Bool :=
  decide (0 < (readProgram (close formula)).value)

theorem decideFormula_correct {n : Nat} (formula : CNFFormula n) :
    decideFormula formula = true ↔ CNFSatisfiable formula := by
  simp only [decideFormula, decide_eq_true_eq, readProgram_value, eval_close,
    PhaseSource.numerator_pos_iff_satisfiable]

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

def nodeBudget : Nat → Nat → Nat
  | 0, nodes => nodes
  | 1, nodes => 2*nodes+7
  | steps+2, nodes => 4*nodeBudget steps nodes+18

theorem eliminateAll_size (addresses : List Nat) (program : Program) :
    (eliminateAll addresses program).code.size ≤ nodeBudget addresses.length program.code.size := by
  induction addresses using List.twoStepInduction with
  | nil => rfl
  | singleton address =>
      have bound := Program.share_size (eliminateOne program address)
      simpa only [eliminateAll, List.length_cons, List.length_nil, nodeBudget, eliminateOne_size,
        Nat.add_assoc] using bound
  | cons_cons left right rest ih _ =>
      have bound := Program.share_size ((eliminateAll rest program).eliminatePair left right)
      rw [Program.eliminatePair_size] at bound
      simp only [eliminateAll, List.length_cons, nodeBudget]
      omega

/-- Every entry is an actual generated program, in execution order. -/
def states : List Nat → Program → List Program
  | [], program => [program]
  | [address], program => [program, (eliminateOne program address).share]
  | left :: right :: rest, program => states rest program ++
      [((eliminateAll rest program).eliminatePair left right).share]

theorem states_nodeBudget (addresses : List Nat) (program state : Program)
    (member : state ∈ states addresses program) :
    state.code.size ≤ nodeBudget addresses.length program.code.size := by
  induction addresses using List.twoStepInduction with
  | nil =>
      have same := List.mem_singleton.mp member
      subst state
      exact le_rfl
  | singleton address =>
      rcases List.mem_cons.mp member with rfl | last
      · simp only [List.length_cons, List.length_nil, nodeBudget]
        omega
      · have same := List.mem_singleton.mp last
        subst state
        exact eliminateAll_size [address] program
  | cons_cons left right rest ih _ =>
      simp only [states, List.mem_append, List.mem_singleton] at member
      rcases member with earlier | rfl
      · have before := ih earlier
        simp only [List.length_cons, nodeBudget]
        omega
      · exact eliminateAll_size (left :: right :: rest) program

theorem states_length (addresses : List Nat) (program : Program) :
    (states addresses program).length = (addresses.length+1)/2+1 := by
  induction addresses using List.twoStepInduction with
  | nil => rfl
  | singleton address => simp [states]
  | cons_cons left right rest ih _ =>
      simp only [states, List.length_append, List.length_cons, List.length_nil, ih]
      omega

theorem compileLiteral_size {n : Nat} (literal : CNFLiteral n) :
    (compileLiteral literal).code.size ≤ 2 := by
  cases positive : literal.positive <;>
    simp [compileLiteral, positive, Fragment.input, Fragment.not, Fragment.unary]

theorem compileClause_size {n : Nat} (clause : CNFClause n) :
    (compileClause clause).code.size ≤ 1+3*clause.length := by
  induction clause with
  | nil => simp [compileClause, Fragment.constant]
  | cons literal rest ih =>
      have bound := compileLiteral_size literal
      simp only [compileClause, Fragment.and, Fragment.binary, Array.size_push,
        Array.size_append, Array.size_map, List.length_cons]
      omega

theorem compilePhase_size {n : Nat} (formula : CNFFormula n) (offset : Nat) :
    (compilePhase offset formula).code.size ≤
      1+4*formula.length+3*SATJoint.literalCount formula := by
  induction formula generalizing offset with
  | nil => simp [compilePhase, Fragment.constant, SATJoint.literalCount]
  | cons clause rest ih =>
      have bound := compileClause_size clause
      have tail := ih (offset+1)
      simp only [compilePhase, Fragment.xor, Fragment.and, Fragment.binary, Fragment.input,
        Array.size_push, Array.size_append, Array.size_map, List.length_cons]
      simp only [SATJoint.literalCount, List.map_cons, List.sum_cons] at *
      have inputSize : (#[Node.input offset] : Array Node).size = 1 := rfl
      omega

theorem compile_size {n : Nat} (formula : CNFFormula n) :
    (compile formula).code.size ≤ 2+4*formula.length+3*SATJoint.literalCount formula := by
  have bound := compilePhase_size formula n
  simp only [compile, Array.size_push]
  omega

theorem close_reading_visits {n : Nat} (formula : CNFFormula n) :
    (readProgram (close formula)).nodeVisits ≤
        nodeBudget (n+formula.length) (compile formula).code.size ∧
      (readProgram (close formula)).rootReads = 2 := by
  have visits := readProgram_visits (close formula)
  refine ⟨?_, visits.2⟩
  rw [visits.1]
  simpa only [close, List.length_range] using eliminateAll_size (List.range (n+formula.length)) (compile formula)

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceDecision

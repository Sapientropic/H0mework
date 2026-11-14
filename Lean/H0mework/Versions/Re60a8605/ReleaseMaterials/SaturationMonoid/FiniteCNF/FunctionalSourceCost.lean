import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalSourceCost.Acceptance
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.SharedFunctional
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalFeedback.Cost

/-! One query/basis occurrence generates the coordinate table, both candidate
    families and the initial acceptance program. All three consumers share the
    actual generated table. This frontend leaves feedback, substitution and
    terminal reading to their own paired execution contracts. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.FunctionalSourceCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open FunctionalSubstitution (Instruction)
open FunctionalSchedule.Cost (inputSize)

structure Prepared where
  private mk ::
  table : Array Row
  free : Nat
  candidates : List Instruction
  initial : Program
  cells : Nat
  deriving Repr

def Prepared.size (source : Prepared) : Nat :=
  AffineCollect.tableSize source.table+inputSize source.candidates+source.initial.code.size+12

def generate {q : Nat} (query : CNFFormula q) (basis : List Row) : Prepared :=
  let table := ConditionalCandidateCost.coordinates q basis
  let free := ConditionalCandidateCost.width q basis
  let functional := ConditionalCandidateCost.Functional.candidates table.value query
  let conditional := ConditionalCandidateCost.branches query basis table.value free.value (List.finRange q)
  let candidates := functional.value++conditional.value
  let initial := Initial.compile table.value query
  ⟨table.value,free.value,candidates,initial.value,
    table.cells+free.cells+functional.cells+conditional.cells+initial.cells+
      2*(AffineCarrier.cellSize basis+AffineCollect.tableSize table.value+
        inputSize functional.value+inputSize conditional.value+inputSize candidates+initial.value.code.size)+2*q+28⟩

theorem generate_table {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (generate query basis).table=Table.coordinates q basis := rfl

theorem generate_free {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (generate query basis).free=(freeIndices q basis).length := rfl

theorem generate_candidates {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (generate query basis).candidates=ConditionalPivot.candidates query basis :=
  ConditionalCandidateCost.candidates_value query basis

theorem generate_initial {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (generate query basis).initial=Acceptance.compile (generate query basis).table query :=
  Initial.compile_value (generate query basis).table query

theorem generate_eval {q : Nat} (query : CNFFormula q) (basis : List Row) (environment : Nat → Bool) :
    (generate query basis).initial.eval environment=bit (CNFFormula.eval query (Gates.coordinate (generate query basis).table environment)) := by
  rw [generate_initial,Acceptance.eval_compile]

theorem generate_entails {q : Nat} (query : CNFFormula q) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin q basis) (environment : Nat → Bool)
    (accepted : truth ((generate query basis).initial.eval environment)=true)
    (call : Instruction) (present : call ∈ (generate query basis).candidates) : call.bind environment=environment := by
  rw [generate_initial,generate_table] at accepted
  rw [generate_candidates] at present
  exact ConditionalPivot.candidates_entails query basis valid.2 valid.1 environment accepted call present

theorem generate_initial_small {q : Nat} (query : CNFFormula q) (basis : List Row) :
    BooleanValues.Code (generate query basis).initial.code := by
  rw [generate_initial]
  exact BooleanValues.acceptance _ query

theorem generate_candidate_small {q : Nat} (query : CNFFormula q) (basis : List Row)
    (call : Instruction) (present : call ∈ (generate query basis).candidates) : BooleanValues.Code call.body.code := by
  rw [generate_candidates] at present
  exact ConditionalPivot.candidate_small query basis call present

def initialBound (q clauses literals : Nat) : Nat := 3+q+2*q*q+3*clauses+3*literals

theorem generate_initial_size {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (generate query basis).initial.code.size ≤ initialBound q query.length (Extract.literalCount query) := by
  have source := Decision.initial_nodes query basis
  have width := Table.freeWidth_le q basis
  rw [generate_initial,generate_table]
  unfold initialBound
  change (Acceptance.compile (Table.coordinates q basis) query).code.size ≤
    3+q+2*q*q+3*query.length+3*SATJoint.literalCount query
  nlinarith

theorem generate_count {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (generate query basis).candidates.length ≤ 3*query.length+q*q := by
  rw [generate_candidates]
  exact ConditionalPivot.candidates_length query basis

def candidatesBound (q clauses : Nat) : Nat := (3*clauses+q*q)*(20+8*q)+1

theorem generate_candidate_size {q : Nat} (query : CNFFormula q) (basis : List Row) :
    inputSize (generate query basis).candidates ≤ candidatesBound q query.length := by
  have each : ∀ call ∈ (generate query basis).candidates, FunctionalSchedule.Cost.instructionSize call ≤ 20+8*q := by
    intro call present
    rw [generate_candidates] at present
    have body := ConditionalPivot.candidate_size query basis call present
    unfold FunctionalSchedule.Cost.instructionSize
    omega
  have sumBound : ∀ source : List Instruction, (∀ call ∈ source,FunctionalSchedule.Cost.instructionSize call ≤ 20+8*q) →
      (source.map FunctionalSchedule.Cost.instructionSize).sum ≤ source.length*(20+8*q) := by
    intro source bounded
    induction source with
    | nil => simp
    | cons call rest ih =>
        have first := bounded call (by simp)
        have tail := ih (fun instruction member => bounded instruction (by simp [member]))
        simp only [List.map_cons,List.sum_cons,List.length_cons]
        nlinarith
  have source := sumBound (generate query basis).candidates each
  have count := generate_count query basis
  unfold inputSize candidatesBound
  nlinarith

def sizeBudget (q clauses literals : Nat) : Nat :=
  AffineCarrier.Cost.cellBound q+candidatesBound q clauses+initialBound q clauses literals+12

theorem generate_size {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (generate query basis).size ≤ sizeBudget q query.length (Extract.literalCount query) := by
  have table := AffineCollect.Cost.coordinate_size q basis
  have candidates := generate_candidate_size query basis
  have initial := generate_initial_size query basis
  simp only [Prepared.size,sizeBudget,generate_table]
  omega

theorem generate_counter {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (generate query basis).cells=(ConditionalCandidateCost.candidates query basis).cells+
      (Initial.compile (Table.coordinates q basis) query).cells+
      2*(generate query basis).initial.code.size+12 := by
  simp only [generate,ConditionalCandidateCost.candidates,ConditionalCandidateCost.coordinates_value]
  omega

def frontendBudget (q clauses literals basisSize : Nat) : Nat :=
  ConditionalCandidateCost.candidatesBudget q clauses literals basisSize+
    Initial.compileBudget (AffineCarrier.Cost.cellBound q) clauses literals+
    2*initialBound q clauses literals+12

theorem generate_cells {q : Nat} (query : CNFFormula q) (basis : List Row) (valid : Triangular basis ∧ RowsWithin q basis) :
    (generate query basis).cells ≤ frontendBudget q query.length (Extract.literalCount query) (AffineCarrier.cellSize basis) := by
  have source := ConditionalCandidateCost.candidates_cells query basis valid
  have initial := Initial.compile_cells (Table.coordinates q basis) query (AffineCarrier.Cost.cellBound q)
    (AffineCollect.Cost.coordinate_size q basis)
  have stored := generate_initial_size query basis
  rw [generate_counter]
  unfold frontendBudget
  omega

def compile {q : Nat} (query : CNFFormula q) (basis : List Row) : CapacityMatching.SourceCost.Counted Program :=
  let source := generate query basis
  let output := FunctionalFeedback.Cost.prepare source.candidates source.initial
  ⟨output.value,source.cells+output.visits+2*(source.size+output.value.code.size)+8⟩

theorem compile_value {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (compile query basis).value=FunctionalFeedback.prepare (ConditionalPivot.candidates query basis)
      (Acceptance.compile (Table.coordinates q basis) query) := by
  simp only [compile,FunctionalFeedback.Cost.prepare_value,generate_candidates,generate_initial,generate_table]

theorem feedback_size (source : List Instruction) (program : Program) :
    (FunctionalFeedback.Cost.prepare source program).value.code.size ≤
      program.code.size+2*source.length*inputSize source+1 := by
  have generated := FunctionalFeedback.Cost.generate_storage source
  have terms := FunctionalFeedback.Cost.bodyTerms_le_inputSize (FunctionalFeedback.Cost.generate source).value
  simp only [FunctionalFeedback.Cost.prepare,SharedFunctional.execute_size]
  omega

def compiledNodes (q clauses literals : Nat) : Nat :=
  initialBound q clauses literals+2*(3*clauses+q*q)*candidatesBound q clauses+1

theorem compile_size {q : Nat} (query : CNFFormula q) (basis : List Row) :
    (compile query basis).value.code.size ≤ compiledNodes q query.length (Extract.literalCount query) := by
  have output := feedback_size (generate query basis).candidates (generate query basis).initial
  have count := generate_count query basis
  have stored := generate_candidate_size query basis
  have initial := generate_initial_size query basis
  have multiplied : (generate query basis).candidates.length*inputSize (generate query basis).candidates ≤
      (3*query.length+q*q)*candidatesBound q query.length := Nat.mul_le_mul count stored
  simp only [compile,compiledNodes]
  nlinarith

theorem feedbackBudget_mono (count size nodes total records bound : Nat)
    (hcount : count ≤ total) (hsize : size ≤ records) (hnodes : nodes ≤ bound) :
    FunctionalFeedback.Cost.prepareBudget count size nodes ≤ FunctionalFeedback.Cost.prepareBudget total records bound := by
  simp only [FunctionalFeedback.Cost.prepareBudget,FunctionalFeedback.Cost.generateBudget_eq]
  gcongr

def compileBudget (q clauses literals basisSize : Nat) : Nat :=
  frontendBudget q clauses literals basisSize+
    FunctionalFeedback.Cost.prepareBudget (3*clauses+q*q) (candidatesBound q clauses) (initialBound q clauses literals)+
    2*(sizeBudget q clauses literals+compiledNodes q clauses literals)+8

theorem compile_cells {q : Nat} (query : CNFFormula q) (basis : List Row) (valid : Triangular basis ∧ RowsWithin q basis) :
    (compile query basis).cells ≤ compileBudget q query.length (Extract.literalCount query) (AffineCarrier.cellSize basis) := by
  have source := generate_cells query basis valid
  have stored := generate_size query basis
  have output := compile_size query basis
  have execution := (FunctionalFeedback.Cost.prepare_visits (generate query basis).candidates (generate query basis).initial).trans
    (feedbackBudget_mono _ _ _ _ _ _ (generate_count query basis) (generate_candidate_size query basis) (generate_initial_size query basis))
  simp only [compile] at output ⊢
  unfold compileBudget
  omega

end SaturationMonoid.ComplexityProjection.SATSource.FunctionalSourceCost

import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.ForcedBranches

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ForcedBranches.Cost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open FunctionalSubstitution (Instruction)
open CapacityMatching.RowCost (rowCells rowsCells)
open FunctionalSchedule.Cost (inputSize instructionSize)

def forceStorage (size : Nat) : Nat := 2*size+14
def forceBudget (size : Nat) : Nat := ConditionalCandidateCost.Code.compileBudget size+10*size+24

theorem force_length (table : Array Row) (i : Nat) (value : Bool) :
    (force table i value).value.length ≤ 1 := by
  cases shape : (table.getD i Gates.zeroRow).vars <;> simp only [force,shape,List.length_nil,List.length_singleton] <;> omega

theorem force_storage (table : Array Row) (i : Nat) (value : Bool) (size : Nat)
    (bounded : AffineCollect.tableSize table ≤ size) :
    inputSize (force table i value).value ≤ forceStorage size := by
  have row := ConditionalCandidateCost.Code.tableRead_size table i
  rw [ConditionalCandidateCost.Code.tableRead_value] at row
  cases shape : (table.getD i Gates.zeroRow).vars with
  | nil => simp only [force,shape,FunctionalSchedule.Cost.inputSize_nil,forceStorage]; omega
  | cons address rest =>
      have code := ConditionalCandidateCost.Code.compileRow_size
        ⟨rest,(table.getD i Gates.zeroRow).rhs ^^ value⟩
      simp only [rowCells,shape,List.length_cons] at row
      simp only [force,shape,FunctionalSchedule.Cost.inputSize_cons,
        FunctionalSchedule.Cost.inputSize_nil,instructionSize,forceStorage]
      simp only at code
      omega

theorem force_cells (table : Array Row) (i : Nat) (value : Bool) (size : Nat)
    (bounded : AffineCollect.tableSize table ≤ size) :
    (force table i value).cells ≤ forceBudget size := by
  have row := ConditionalCandidateCost.Code.tableRead_size table i
  rw [ConditionalCandidateCost.Code.tableRead_value] at row
  cases shape : (table.getD i Gates.zeroRow).vars with
  | nil => simp only [force,shape,forceBudget]; omega
  | cons address rest =>
      have code := ConditionalCandidateCost.Code.compileRow_size
        ⟨rest,(table.getD i Gates.zeroRow).rhs ^^ value⟩
      have length : rest.length ≤ size := by
        simp only [rowCells,shape,List.length_cons] at row
        omega
      have billed := (ConditionalCandidateCost.Code.compileRow_cells
        ⟨rest,(table.getD i Gates.zeroRow).rhs ^^ value⟩).trans
          (ConditionalCandidateCost.Code.compileBudget_mono _ _ length)
      simp only [force,shape,forceBudget]
      simp only at code
      omega

theorem force_small (table : Array Row) (i : Nat) (value : Bool) (item : Instruction)
    (member : item ∈ (force table i value).value) : BooleanValues.Code item.body.code := by
  simp only [force] at member
  split at member
  · simp at member
  · simp only [List.mem_singleton] at member
    subst item
    rw [ConditionalCandidateCost.Code.compileRow_value]
    exact BooleanValues.compile_row _

def branchStorage (n : Nat) : Nat :=
  ConditionalCandidateCost.branchStorage n+forceStorage (AffineCarrier.Cost.cellBound n)

theorem branch_storage {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (i : Fin n) :
    inputSize (branch formula basis (Table.coordinates n basis) (freeIndices n basis).length i).value ≤
      branchStorage n := by
  have table := AffineCollect.Cost.coordinate_size n basis
  have leftForce := force_storage (Table.coordinates n basis) i.val true _ table
  have rightForce := force_storage (Table.coordinates n basis) i.val false _ table
  have original := ConditionalCandidateCost.branchCandidates_storage formula basis valid i
  cases left : (AffineRelationExtractionCost.branch formula (.basis basis) i false).value with
  | contradiction =>
      simpa only [branch,left,branchStorage] using
        leftForce.trans (Nat.le_add_left _ _)
  | basis a =>
      cases right : (AffineRelationExtractionCost.branch formula (.basis basis) i true).value with
      | contradiction =>
          simpa only [branch,left,right,branchStorage] using
            rightForce.trans (Nat.le_add_left _ _)
      | basis b =>
          simp only [ConditionalCandidateCost.branchCandidates,ConditionalCandidateCost.split,left,right] at original
          simpa only [branch,left,right,branchStorage] using original.trans (Nat.le_add_right _ _)

def branchBudget (n clauses literals basisSize : Nat) : Nat :=
  ConditionalCandidateCost.branchBudget n clauses literals basisSize+
    forceBudget (AffineCarrier.Cost.cellBound n)+2*forceStorage (AffineCarrier.Cost.cellBound n)+8

theorem branch_cells {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (i : Fin n) :
    (branch formula basis (Table.coordinates n basis) (freeIndices n basis).length i).cells ≤
      branchBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  have ends := ConditionalCandidateCost.split_cells formula basis valid i
  have table := AffineCollect.Cost.coordinate_size n basis
  have leftWork := force_cells (Table.coordinates n basis) i.val true _ table
  have rightWork := force_cells (Table.coordinates n basis) i.val false _ table
  have leftSize := force_storage (Table.coordinates n basis) i.val true _ table
  have rightSize := force_storage (Table.coordinates n basis) i.val false _ table
  have original := ConditionalCandidateCost.branchCandidates_cells formula basis valid i
  cases left : (AffineRelationExtractionCost.branch formula (.basis basis) i false).value with
  | contradiction =>
      simp only [ConditionalCandidateCost.split,left] at ends
      simp only [branch,left,branchBudget,ConditionalCandidateCost.branchBudget]
      omega
  | basis a =>
      cases right : (AffineRelationExtractionCost.branch formula (.basis basis) i true).value with
      | contradiction =>
          simp only [ConditionalCandidateCost.split,left,right] at ends
          simp only [branch,left,right,branchBudget,ConditionalCandidateCost.branchBudget]
          omega
      | basis b =>
          simp only [ConditionalCandidateCost.branchCandidates,ConditionalCandidateCost.split,left,right] at original
          simp only [branch,left,right,branchBudget]
          omega

theorem branch_length {n : Nat} (formula : CNFFormula n) (basis : List Row) (i : Fin n) :
    (branch formula basis (Table.coordinates n basis) (freeIndices n basis).length i).value.length ≤ n := by
  have leftForce := force_length (Table.coordinates n basis) i.val true
  have rightForce := force_length (Table.coordinates n basis) i.val false
  have count := Table.freeWidth_le n basis
  have positive := i.isLt
  simp only [branch]
  split <;> simp only [ConditionalCandidateCost.makeCalls_length,List.length_finRange] <;> omega

theorem branch_small {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (table : Array Row) (free : Nat) (i : Fin n) (item : Instruction)
    (member : item ∈ (branch formula basis table free i).value) : BooleanValues.Code item.body.code := by
  simp only [branch] at member
  split at member
  · exact force_small _ _ _ item member
  · exact force_small _ _ _ item member
  · simp only [ConditionalCandidateCost.makeCalls_value] at member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact ConditionalPivot.body_small _ _ _ _ _

theorem branches_storage {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (indices : List (Fin n)) :
    inputSize (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length indices).value ≤
      indices.length*branchStorage n+1 := by
  induction indices with
  | nil => simp [branches]
  | cons i rest ih =>
      have first := branch_storage formula basis valid i
      have sumBound : inputSize (branch formula basis (Table.coordinates n basis) (freeIndices n basis).length i).value+
          inputSize (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length rest).value ≤
          (rest.length+1)*branchStorage n+2 := by nlinarith
      simp only [branches,ConditionalCandidateCost.Functional.inputSize_append,List.length_cons]
      omega

def branchesBudget (n clauses literals basisSize : Nat) : Nat :=
  n*(branchBudget n clauses literals basisSize+4*(n+1)*branchStorage n+12)+1

theorem branches_cells_aux {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (indices : List (Fin n)) (length : indices.length ≤ n) :
    (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length indices).cells ≤
      indices.length*(branchBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis)+
        4*(n+1)*branchStorage n+12)+1 := by
  induction indices with
  | nil => simp [branches]
  | cons i rest ih =>
      have tail := ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) length)
      have first := branch_cells formula basis valid i
      have firstSize := branch_storage formula basis valid i
      have tailSize := branches_storage formula basis valid rest
      simp only [branches,List.length_cons] at *
      nlinarith

theorem branches_cells {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length (List.finRange n)).cells ≤
      branchesBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  simpa only [branchesBudget,List.length_finRange] using branches_cells_aux formula basis valid (List.finRange n) (by simp)

theorem branches_length {n : Nat} (formula : CNFFormula n) (basis : List Row) (indices : List (Fin n)) :
    (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length indices).value.length ≤ indices.length*n := by
  induction indices with
  | nil => simp [branches]
  | cons i rest ih =>
      have first := branch_length formula basis i
      simp only [branches,List.length_append,List.length_cons]
      nlinarith

theorem branches_small {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (table : Array Row) (free : Nat) (indices : List (Fin n)) (item : Instruction)
    (member : item ∈ (branches formula basis table free indices).value) : BooleanValues.Code item.body.code := by
  induction indices with
  | nil => simp [branches] at member
  | cons i rest ih =>
      rcases List.mem_append.mp member with first | tail
      · exact branch_small formula basis table free i item first
      · exact ih tail

def outputStorage (n clauses : Nat) : Nat := ConditionalCandidateCost.priorStorage n clauses+n*branchStorage n+1

theorem generate_storage {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    inputSize (generate formula basis).value ≤ outputStorage n formula.length := by
  have table := AffineCollect.Cost.coordinate_size n basis
  have prior := ConditionalCandidateCost.Functional.filter_storage (Table.coordinates n basis)
    (ConditionalCandidateCost.Functional.relations formula).value _ table
  have count := ConditionalCandidateCost.Functional.relations_length formula
  have total : inputSize (ConditionalCandidateCost.Functional.candidates (Table.coordinates n basis) formula).value ≤
      ConditionalCandidateCost.priorStorage n formula.length := by
    simp only [ConditionalCandidateCost.Functional.candidates,ConditionalCandidateCost.priorStorage]
    nlinarith
  have conditional := branches_storage formula basis valid (List.finRange n)
  simp only [List.length_finRange] at conditional
  simp only [generate,ConditionalCandidateCost.coordinates_value,ConditionalCandidateCost.width_value,
    ConditionalCandidateCost.Functional.inputSize_append,outputStorage]
  omega

def generateBudget (n clauses literals basisSize : Nat) : Nat :=
  AffineCollect.Cost.coordinateBudget n+ConditionalCandidateCost.widthBudget n basisSize+
    ConditionalCandidateCost.Functional.candidatesBudget clauses literals (AffineCarrier.Cost.cellBound n)+
    branchesBudget n clauses literals basisSize+2*(AffineCarrier.Cost.cellBound n+outputStorage n clauses+1)+2*n+20

theorem generate_cells {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (generate formula basis).cells ≤ generateBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  have table := AffineCollect.Cost.coordinate_size n basis
  have tableWork := ConditionalCandidateCost.coordinates_cells n basis valid
  have freeWork := ConditionalCandidateCost.width_cells n basis valid
  have priorWork := ConditionalCandidateCost.Functional.candidates_cells (Table.coordinates n basis) formula _ table
  have conditional := branches_cells formula basis valid
  have output := generate_storage formula basis valid
  have priorPos := FunctionalSchedule.Cost.inputSize_pos (ConditionalCandidateCost.Functional.candidates (Table.coordinates n basis) formula).value
  have nextPos := FunctionalSchedule.Cost.inputSize_pos
    (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length (List.finRange n)).value
  simp only [generate,ConditionalCandidateCost.coordinates_value,ConditionalCandidateCost.width_value,
    ConditionalCandidateCost.Functional.inputSize_append] at output
  simp only [generate,ConditionalCandidateCost.coordinates_value,ConditionalCandidateCost.width_value,generateBudget]
  omega

theorem generate_length {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (generate formula basis).value.length ≤ 3*formula.length+n*n := by
  have prior := ConditionalCandidateCost.Functional.candidates_length (Table.coordinates n basis) formula
  have conditional := branches_length formula basis (List.finRange n)
  simp only [List.length_finRange] at conditional
  simp only [generate,ConditionalCandidateCost.coordinates_value,ConditionalCandidateCost.width_value,List.length_append]
  omega

theorem generate_small {n : Nat} (formula : CNFFormula n) (basis : List Row) (item : Instruction)
    (member : item ∈ (generate formula basis).value) : BooleanValues.Code item.body.code := by
  rcases List.mem_append.mp member with prior | conditional
  · apply FunctionalPivot.candidate_small formula basis item
    simpa only [ConditionalCandidateCost.coordinates_value,ConditionalCandidateCost.Functional.candidates_value] using prior
  · exact branches_small formula basis _ _ (List.finRange n) item conditional

/-- This is the same generated candidate occurrence as `generate`; retaining the
    table during compilation lets the initial program share its one construction. -/
def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Counted Program :=
  let table := ConditionalCandidateCost.coordinates n basis
  let free := ConditionalCandidateCost.width n basis
  let functional := ConditionalCandidateCost.Functional.candidates table.value formula
  let conditional := branches formula basis table.value free.value (List.finRange n)
  let calls := functional.value++conditional.value
  let generatedCells := table.cells+free.cells+functional.cells+conditional.cells+
    2*(AffineCollect.tableSize table.value+inputSize functional.value+inputSize conditional.value)+2*n+20
  let initial := FunctionalSourceCost.Initial.compile table.value formula
  let output := FunctionalFeedback.Cost.prepare calls initial.value
  ⟨output.value,generatedCells+initial.cells+output.visits+
    2*(AffineCarrier.cellSize basis+AffineCollect.tableSize table.value+inputSize calls+
      initial.value.code.size+output.value.code.size)+20⟩

theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (compile formula basis).value=FunctionalFeedback.prepare (generate formula basis).value
      (Acceptance.compile (Table.coordinates n basis) formula) := by
  simp only [compile,generate,FunctionalFeedback.Cost.prepare_value,
    FunctionalSourceCost.Initial.compile_value,ConditionalCandidateCost.coordinates_value]

theorem compile_counter {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (compile formula basis).cells=(generate formula basis).cells+
      (FunctionalSourceCost.Initial.compile (Table.coordinates n basis) formula).cells+
      (FunctionalFeedback.Cost.prepare (generate formula basis).value
        (FunctionalSourceCost.Initial.compile (Table.coordinates n basis) formula).value).visits+
      2*(AffineCarrier.cellSize basis+AffineCollect.tableSize (Table.coordinates n basis)+
        inputSize (generate formula basis).value+
        (FunctionalSourceCost.Initial.compile (Table.coordinates n basis) formula).value.code.size+
        (compile formula basis).value.code.size)+20 := rfl

theorem initial_size {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (FunctionalSourceCost.Initial.compile (Table.coordinates n basis) formula).value.code.size ≤
      FunctionalSourceCost.initialBound n formula.length (Extract.literalCount formula) := by
  have source := FunctionalSourceCost.generate_initial_size formula basis
  simpa only [FunctionalSourceCost.generate_initial,FunctionalSourceCost.generate_table,
    FunctionalSourceCost.Initial.compile_value] using source

def compiledNodes (n clauses literals : Nat) : Nat :=
  FunctionalSourceCost.initialBound n clauses literals+2*(3*clauses+n*n)*outputStorage n clauses+1

theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).value.code.size ≤ compiledNodes n formula.length (Extract.literalCount formula) := by
  have output := FunctionalSourceCost.feedback_size (generate formula basis).value
    (FunctionalSourceCost.Initial.compile (Table.coordinates n basis) formula).value
  have count := generate_length formula basis
  have storage := generate_storage formula basis valid
  have initial := initial_size formula basis
  have multiplied : (generate formula basis).value.length*inputSize (generate formula basis).value ≤
      (3*formula.length+n*n)*outputStorage n formula.length := Nat.mul_le_mul count storage
  change (compile formula basis).value.code.size ≤ _ at output
  unfold compiledNodes
  nlinarith

def compileBudget (n clauses literals basisSize : Nat) : Nat :=
  generateBudget n clauses literals basisSize+
    FunctionalSourceCost.Initial.compileBudget (AffineCarrier.Cost.cellBound n) clauses literals+
    FunctionalFeedback.Cost.prepareBudget (3*clauses+n*n) (outputStorage n clauses)
      (FunctionalSourceCost.initialBound n clauses literals)+
    2*(basisSize+AffineCarrier.Cost.cellBound n+outputStorage n clauses+
      FunctionalSourceCost.initialBound n clauses literals+compiledNodes n clauses literals)+20

theorem compile_cells {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).cells ≤ compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  have generated := generate_cells formula basis valid
  have storage := generate_storage formula basis valid
  have table := AffineCollect.Cost.coordinate_size n basis
  have initial := FunctionalSourceCost.Initial.compile_cells (Table.coordinates n basis) formula _ table
  have initialSize := initial_size formula basis
  have execution := (FunctionalFeedback.Cost.prepare_visits (generate formula basis).value
    (FunctionalSourceCost.Initial.compile (Table.coordinates n basis) formula).value).trans
      (FunctionalSourceCost.feedbackBudget_mono _ _ _ _ _ _ (generate_length formula basis) storage initialSize)
  have output := compile_size formula basis valid
  rw [compile_counter]
  unfold compileBudget
  omega

theorem compile_small {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    BooleanValues.Code (compile formula basis).value.code := by
  rw [compile_value,FunctionalFeedback.prepare]
  exact FunctionalSubstitution.execute_small _ _ (BooleanValues.acceptance _ formula)
    (fun item member => generate_small formula basis item (FunctionalFeedback.generate_member _ item member))

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (FunctionalAffine.legal (FunctionalFeedback.generate (generate formula basis).value) point &&
      truth ((compile formula basis).value.eval point))=
      CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  rw [compile_value]
  exact generated_read formula basis valid point

theorem selected_eliminated {n : Nat} (formula : CNFFormula n) (basis : List Row) (item : Instruction)
    (selected : item ∈ FunctionalFeedback.generate (generate formula basis).value) :
    item.address ∉ FunctionalSubstitution.inputs (compile formula basis).value.code := by
  rw [compile_value]
  exact FunctionalFeedback.prepare_eliminates _ _ item selected

theorem compile_correct {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    FunctionalSubstitution.decideProgram (Cone.pruneCone (compile formula basis).value)=true ↔
      ∃ point : Assignment n, CNFFormula.eval formula (extendAssignment point)=true ∧
        holds basis (extendAssignment point)=true := by
  rw [FunctionalPivot.decide_prune,compile_value,FunctionalFeedback.prepare_correct _ _
    (generate_entails formula basis valid)]
  simp only [Acceptance.eval_compile,truth_bit]
  constructor
  · rintro ⟨environment,accepted⟩
    let point : Assignment n := fun i => Gates.coordinate (Table.coordinates n basis) environment i.val
    have relations : holds basis (Gates.coordinate (Table.coordinates n basis) environment)=true := by
      rw [Table.coordinates_value n basis valid.2]
      exact fill_holds basis valid.1 _
    exact ⟨point,(formula_eval_restrict formula _).trans accepted,
      (AtomSource.holds_restrict n basis valid.2 _).trans relations⟩
  · rintro ⟨point,accepted,relations⟩
    have recovered := (Decision.table_lift n basis valid.2 (projectFree n basis point)).trans
      (parameterLift_projectFree n basis valid.1 point relations)
    refine ⟨extendAssignment (projectFree n basis point),?_⟩
    rw [← formula_eval_restrict formula _]
    exact (congrArg (fun x => CNFFormula.eval formula (extendAssignment x)) recovered).trans accepted

end SaturationMonoid.ComplexityProjection.SATSource.ForcedBranches.Cost

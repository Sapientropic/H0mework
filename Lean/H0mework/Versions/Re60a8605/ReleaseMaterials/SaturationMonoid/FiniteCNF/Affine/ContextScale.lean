import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.StrongFeedbackScale
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.SharedSourceScale

/-!
The fixed context is physically joined to every probe before Gaussian initialization.
The paired counters cover that initialization and the final emitted seed setup;
the phase families cover the actual remaining strong-feedback structures. They are
source-record contracts, not a unit-cost charge for the feedback engine or TM time.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineContextScale
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowsCells rowCells)
open StrongFeedbackScale (Family phaseStates augmentedClauses augmentedLiterals sourceRecords)

abbrev Counted := CapacityMatching.SourceCost.Counted

def probeRows {n : Nat} (clause : CNFClause n) : Counted (List Row) :=
  ⟨clause.map Propagation.badLiteral,5*clause.length+1⟩

theorem probeRows_storage {n : Nat} (clause : CNFClause n) :
    rowsCells (probeRows clause).value=3*clause.length := by
  change rowsCells (clause.map Propagation.badLiteral)=_
  rw [AffineCollect.Cost.rows_size,AffineCarrier.Cost.bad_terms,List.length_map]
  omega

theorem probe_inside {n : Nat} (context : List Row) (inside : RowsWithin n context) (clause : CNFClause n) :
    RowsWithin n (context++clause.map Propagation.badLiteral) := by
  intro row member
  rcases List.mem_append.mp member with old | fresh
  · exact inside row old
  · exact AffineCarrier.Cost.bad_inside clause row fresh

structure Initialization where
  result : Result
  cells : Nat
  deriving Repr

def querySetup {n : Nat} (context : List Row) (clause : CNFClause n) : Initialization :=
  let probe := probeRows clause
  let joined := CapacityMatching.RowCost.append context probe.value
  let reduced := EliminateCost.run joined.value
  ⟨reduced.result,probe.cells+joined.cells+reduced.cells+
    2*rowsCells joined.value+2*AffineCarrier.resultSize reduced.result+3⟩

theorem querySetup_result {n : Nat} (context : List Row) (clause : CNFClause n) :
    (querySetup context clause).result=eliminate (context++clause.map Propagation.badLiteral) := by
  simp only [querySetup,CapacityMatching.RowCost.append,probeRows,EliminateCost.run_result]

def gaussianBudget (n storage : Nat) : Nat := storage*(2*n+EliminateCost.insertCellBudget n+6)+1

theorem gaussian_cells (n : Nat) (rows : List Row) (inside : RowsWithin n rows) :
    (EliminateCost.run rows).cells ≤ gaussianBudget n (rowsCells rows) := by
  have bounds := AffineCarrier.Cost.row_measures rows
  apply (EliminateCost.run_cells n rows inside).trans
  unfold gaussianBudget
  nlinarith [Nat.mul_le_mul_right (2*n+5) bounds.2,
    Nat.mul_le_mul_right (EliminateCost.insertCellBudget n+1) bounds.1]

def queryBudget (n contextStorage : Nat) : Nat :=
  gaussianBudget n (contextStorage+6)+4*contextStorage+45+2*(AffineCarrier.Cost.cellBound n+1)

theorem querySetup_cells {n : Nat} (context : List Row) (inside : RowsWithin n context)
    (clause : CNFClause n) (binary : clause.length=2) :
    (querySetup context clause).cells ≤ queryBudget n (rowsCells context) := by
  have valid := probe_inside context inside clause
  have reduced := gaussian_cells n _ valid
  have output := AffineCarrier.Cost.result_size n (eliminate (context++clause.map Propagation.badLiteral))
    (eliminate_triangular _) (eliminate_within n _ valid)
  have probe := probeRows_storage clause
  change rowsCells (clause.map Propagation.badLiteral)=_ at probe
  rw [binary] at probe
  norm_num at probe
  simp only [CapacityMatching.RowCost.rowsCells_append,probe] at reduced
  simp only [querySetup,probeRows,CapacityMatching.RowCost.append,
    CapacityMatching.RowCost.rowsCells_append,EliminateCost.run_result,binary,probe]
  unfold queryBudget
  omega

def reject {n : Nat} (formula : CNFFormula n) (context : List Row) (clause : CNFClause n) : Counted Bool :=
  let prepared := querySetup context clause
  let generated := TightFeedback.iterate formula (n+1) prepared.result
  ⟨match generated with | .contradiction => true | .basis _ => false,prepared.cells⟩

theorem reject_value {n : Nat} (formula : CNFFormula n) (context : List Row) (clause : CNFClause n) :
    (reject formula context clause).value=AffineBinaryContext.reject formula context clause := by
  simp only [reject,querySetup_result,TightFeedback.generate,AffineBinaryContext.reject]
  rfl

structure Scan (n : Nat) where
  value : BinaryRelations.Scan n
  queryCells : Nat

def scan {n : Nat} (formula : CNFFormula n) (context : List Row) : CNFFormula n → Scan n
  | [] => ⟨⟨none,0⟩,0⟩
  | clause::rest =>
      if clause ∈ formula then scan formula context rest
      else
        let checked := reject formula context clause
        if checked.value then ⟨⟨some clause,1⟩,checked.cells⟩
        else let next := scan formula context rest
             ⟨⟨next.value.answer,next.value.queries+1⟩,checked.cells+next.queryCells⟩

theorem scan_value {n : Nat} (formula : CNFFormula n) (context : List Row) (candidates : CNFFormula n) :
    (scan formula context candidates).value=AffineBinaryContext.scan formula context candidates := by
  induction candidates with
  | nil => rfl
  | cons clause rest ih =>
      simp only [scan,AffineBinaryContext.scan,reject_value]
      split <;> simp only [ih]
      split <;> rfl

theorem scan_cells {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context)
    (candidates : CNFFormula n) (binary : ∀ clause ∈ candidates,clause.length=2) :
    (scan formula context candidates).queryCells ≤
      (scan formula context candidates).value.queries*queryBudget n (rowsCells context) := by
  induction candidates with
  | nil => simp [scan]
  | cons clause rest ih =>
      have tail := ih (fun c member => binary c (by simp [member]))
      have first := querySetup_cells context inside clause (binary clause (by simp))
      simp only [scan]
      split
      · exact tail
      · split <;> simp only [reject]
        · simpa using first
        · nlinarith

structure Trace (n : Nat) where
  value : BinaryRelations.Execution n
  sources : List (CNFFormula n)
  queryCells : Nat

def run {n : Nat} (context : List Row) (candidates : CNFFormula n) : Nat → CNFFormula n → Trace n
  | 0,formula => ⟨⟨formula,0⟩,[formula],0⟩
  | fuel+1,formula =>
      let attempt := scan formula context candidates
      match attempt.value.answer with
      | none => ⟨⟨formula,attempt.value.queries⟩,[formula],attempt.queryCells⟩
      | some clause =>
          let next := run context candidates fuel (clause::formula)
          ⟨⟨next.value.formula,attempt.value.queries+next.value.queries⟩,
            formula::next.sources,attempt.queryCells+next.queryCells⟩

theorem run_value {n : Nat} (context : List Row) (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (run context candidates fuel formula).value=AffineBinaryContext.run context candidates fuel formula := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases found : (AffineBinaryContext.scan formula context candidates).answer <;>
        simp only [run,AffineBinaryContext.run,scan_value,found,ih]

theorem run_cells {n : Nat} (context : List Row) (inside : RowsWithin n context) (candidates : CNFFormula n)
    (binary : ∀ clause ∈ candidates,clause.length=2) (fuel : Nat) (formula : CNFFormula n) :
    (run context candidates fuel formula).queryCells ≤
      (run context candidates fuel formula).value.queries*queryBudget n (rowsCells context) := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      have first := scan_cells formula context inside candidates binary
      cases found : (scan formula context candidates).value.answer with
      | none => simpa only [run,found] using first
      | some clause =>
          have tail := ih (clause::formula)
          simp only [run,found]
          nlinarith

def generate {n : Nat} (formula : CNFFormula n) (context : List Row) : Trace n :=
  run context (BinaryRelations.inventory n) (BinaryRelations.inventory n).length formula

theorem generate_value {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (generate formula context).value=AffineBinaryContext.generate formula context := run_value _ _ _ _

theorem generate_queryCells {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context) :
    (generate formula context).queryCells ≤ 16*n^4*queryBudget n (rowsCells context) := by
  have charged := run_cells context inside (BinaryRelations.inventory n)
    (fun clause member => BinaryRelations.inventory_clause clause member) (BinaryRelations.inventory n).length formula
  change (generate formula context).queryCells ≤ (generate formula context).value.queries*_ at charged
  rw [generate_value] at charged
  exact charged.trans (Nat.mul_le_mul_right _ (AffineBinaryContext.generate_queries formula context))

theorem run_final {n : Nat} (context : List Row) (candidates : CNFFormula n) (fuel : Nat) (formula : CNFFormula n) :
    (run context candidates fuel formula).value.formula ∈ (run context candidates fuel formula).sources := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      cases found : (scan formula context candidates).value.answer with
      | none => simp [run,found]
      | some clause =>
          simpa only [run,found] using List.mem_cons_of_mem formula (ih (clause::formula))

theorem run_sources_length {n : Nat} (context : List Row) (candidates : CNFFormula n) (fuel : Nat)
    (formula : CNFFormula n) : (run context candidates fuel formula).sources.length ≤ fuel+1 := by
  induction fuel generalizing formula with
  | zero => simp [run]
  | succ fuel ih =>
      cases found : (scan formula context candidates).value.answer with
      | none => simp [run,found]
      | some clause => simpa only [run,found,List.length_cons] using Nat.add_le_add_right (ih (clause::formula)) 1

theorem run_family {n : Nat} (context : List Row) (candidates : CNFFormula n)
    (binary : ∀ clause ∈ candidates,clause.length=2) (fuel : Nat) (formula source : CNFFormula n)
    (member : source ∈ (run context candidates fuel formula).sources) :
    source.length ≤ formula.length+fuel ∧ Extract.literalCount source ≤ Extract.literalCount formula+2*fuel := by
  induction fuel generalizing formula with
  | zero =>
      have same : source=formula := by simpa [run] using member
      subst source
      simp
  | succ fuel ih =>
      cases found : (scan formula context candidates).value.answer with
      | none =>
          have same : source=formula := by simpa [run,found] using member
          subst source
          constructor <;> omega
      | some clause =>
          simp only [run,found,List.mem_cons] at member
          rcases member with rfl | later
          · constructor <;> omega
          · have tail := ih (clause::formula) later
            rw [scan_value] at found
            have clauseSize := binary clause (AffineBinaryContext.scan_spec formula context candidates clause found).1
            simp only [List.length_cons,Extract.literalCount,List.map_cons,List.sum_cons,clauseSize] at tail
            change _ ≤ _ ∧ (source.map List.length).sum ≤ (formula.map List.length).sum+_
            constructor <;> omega

theorem generate_family {n : Nat} (formula : CNFFormula n) (context : List Row) (source : CNFFormula n)
    (member : source ∈ (generate formula context).sources) :
    source.length ≤ augmentedClauses n formula.length ∧
      Extract.literalCount source ≤ augmentedLiterals n (Extract.literalCount formula) := by
  have bounded := run_family context (BinaryRelations.inventory n)
    (fun clause present => BinaryRelations.inventory_clause clause present) _ formula source member
  simpa only [BinaryRelations.inventory_length,augmentedClauses,augmentedLiterals,← Nat.mul_assoc,Nat.reduceMul] using bounded

theorem generate_sources_length {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (generate formula context).sources.length ≤ 4*n*n+1 := by
  simpa only [generate,BinaryRelations.inventory_length] using run_sources_length context (BinaryRelations.inventory n) _ formula

private theorem sum_bound {α : Type} (measure : α → Nat) (items : List α) (bound : Nat)
    (each : ∀ item ∈ items,measure item ≤ bound) : (items.map measure).sum ≤ items.length*bound := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have first := each item (by simp)
      have tail := ih (fun value member => each value (by simp [member]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

theorem retained_storage {n : Nat} (formula : CNFFormula n) (context : List Row) :
    ((generate formula context).sources.map sourceRecords).sum ≤
      (4*n*n+1)*(3*augmentedLiterals n (Extract.literalCount formula)+2*augmentedClauses n formula.length+1) := by
  have each : ∀ source ∈ (generate formula context).sources,
      sourceRecords source ≤ 3*augmentedLiterals n (Extract.literalCount formula)+2*augmentedClauses n formula.length+1 := by
    intro source member
    have bounded := generate_family formula context source member
    unfold sourceRecords
    omega
  exact (sum_bound sourceRecords _ _ each).trans (Nat.mul_le_mul_right _ (generate_sources_length formula context))

/-- The context may be any within rows; it need not be entailed by the naked CNF. -/
theorem query_phase_family {n : Nat} (original : CNFFormula n) (context : List Row) (inside : RowsWithin n context)
    (source : CNFFormula n) (member : source ∈ (generate original context).sources) (clause : CNFClause n)
    (candidate : clause ∈ BinaryRelations.inventory n) (round : Nat) (basis : List Row)
    (state : Result.basis basis ∈ phaseStates source
      (TightFeedback.iterate source round (querySetup context clause).result)) :
    rowsCells (context++clause.map Propagation.badLiteral)=rowsCells context+6 ∧
      Family n (augmentedClauses n original.length) (augmentedLiterals n (Extract.literalCount original)) basis source := by
  have bounded := generate_family original context source member
  rw [querySetup_result] at state
  have valid := StrongFeedbackScale.iterate_phase_family source _ (probe_inside context inside clause) round basis state
  have size := probeRows_storage clause
  change rowsCells (clause.map Propagation.badLiteral)=_ at size
  rw [BinaryRelations.inventory_clause clause candidate] at size
  refine ⟨?_,StrongFeedbackScale.family basis ⟨valid.1,valid.2.1⟩ source _ _ bounded.1 bounded.2⟩
  rw [CapacityMatching.RowCost.rowsCells_append,size]

theorem query_prefix_storage {n : Nat} (context : List Row) (inside : RowsWithin n context)
    (clause : CNFClause n) (takeCount : Nat) :
    AffineCarrier.resultSize (eliminate ((context++clause.map Propagation.badLiteral).take takeCount)) ≤
      AffineCarrier.Cost.cellBound n+1 :=
  StrongFeedbackScale.eliminate_prefix_storage n _ (probe_inside context inside clause) takeCount

theorem query_phase_storage {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context)
    (clause : CNFClause n) (round : Nat) :
    ((phaseStates formula (TightFeedback.iterate formula round (querySetup context clause).result)).map
      AffineCarrier.resultSize).sum ≤ 5*(AffineCarrier.Cost.cellBound n+1) := by
  rw [querySetup_result]
  have joined := probe_inside context inside clause
  exact StrongFeedbackScale.phaseStates_storage formula _
    (TightFeedback.iterate_invariants formula round _ (eliminate_within n _ joined) (eliminate_triangular _)).symm

def seedRows {n : Nat} (formula : CNFFormula n) (context : List Row) : List Row :=
  context++Extract.extract formula++(CapacityMatching.RowCost.prepare formula).value

theorem seedRows_inside {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context) :
    RowsWithin n (seedRows formula context) := by
  have learned := StrongFeedbackScale.seed_rows_within formula
  intro row member
  rw [seedRows,List.append_assoc] at member
  rcases List.mem_append.mp member with original | added
  · exact inside row original
  · exact learned row added

def seedStorage (n clauses literals contextStorage : Nat) : Nat :=
  contextStorage+5*clauses+CapacityMatching.RowCost.prepareStorage n clauses literals

theorem seedRows_storage {n : Nat} (formula : CNFFormula n) (context : List Row) :
    rowsCells (seedRows formula context) ≤ seedStorage n formula.length (Extract.literalCount formula) (rowsCells context) := by
  have original := StrongFeedbackScale.original_initial_storage formula
  simp only [seedRows,CapacityMatching.RowCost.rowsCells_append,seedStorage]
  rw [CapacityMatching.RowCost.rowsCells_append] at original
  omega

def seedSetup {n : Nat} (formula : CNFFormula n) (context : List Row) : Initialization :=
  let extracted := Extract.run formula
  let prepared := CapacityMatching.RowCost.prepare formula
  let first := CapacityMatching.RowCost.append context extracted.rows
  let joined := CapacityMatching.RowCost.append first.value prepared.value
  let reduced := EliminateCost.run joined.value
  ⟨reduced.result,extracted.visits+prepared.cells+first.cells+joined.cells+reduced.cells+
    2*rowsCells joined.value+2*AffineCarrier.resultSize reduced.result+3⟩

theorem seedSetup_result {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (seedSetup formula context).result=eliminate (seedRows formula context) := by
  simp only [seedSetup,seedRows,CapacityMatching.RowCost.append,Extract.extract,EliminateCost.run_result]

def extractBudget (clauses literals : Nat) : Nat := clauses*(56*literals+40*clauses+42)+1

def seedBudget (n clauses literals contextStorage : Nat) : Nat :=
  extractBudget clauses literals+CapacityMatching.RowCost.prepareBudget n clauses literals+
    gaussianBudget n (seedStorage n clauses literals contextStorage)+
      6*seedStorage n clauses literals contextStorage+2*(AffineCarrier.Cost.cellBound n+1)+17

theorem seedSetup_cells {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context) :
    (seedSetup formula context).cells ≤ seedBudget n formula.length (Extract.literalCount formula) (rowsCells context) := by
  have extracted := Extract.run_visits formula
  have prepared := CapacityMatching.RowCost.prepare_cells formula
  have storage := seedRows_storage formula context
  have joined := seedRows_inside formula context inside
  have reduced := (gaussian_cells n _ joined).trans (show gaussianBudget n (rowsCells (seedRows formula context)) ≤
      gaussianBudget n (seedStorage n formula.length (Extract.literalCount formula) (rowsCells context)) by
    unfold gaussianBudget
    gcongr)
  have output := AffineCarrier.Cost.result_size n (eliminate (seedRows formula context))
    (eliminate_triangular _) (eliminate_within n _ joined)
  simp only [seedRows,CapacityMatching.RowCost.rowsCells_append] at storage
  simp only [seedSetup,CapacityMatching.RowCost.append,EliminateCost.run_result,
    CapacityMatching.RowCost.rowsCells_append]
  change (Extract.run formula).visits+_+(2*rowsCells context+2*rowsCells (Extract.extract formula)+5)+
    (2*(rowsCells context+rowsCells (Extract.extract formula))+2*rowsCells (CapacityMatching.RowCost.prepare formula).value+5)+
    (EliminateCost.run (seedRows formula context)).cells+
    2*(rowsCells context+rowsCells (Extract.extract formula)+rowsCells (CapacityMatching.RowCost.prepare formula).value)+
    2*AffineCarrier.resultSize (eliminate (seedRows formula context))+3 ≤ _
  unfold seedBudget extractBudget
  nlinarith

/-- The fields are generated together. The public constraint value below recognizes
the sealed original `JointEmission.Output` without running its producer twice. -/
structure Emission (n : Nat) where
  binary : Trace n
  context : List Row
  strong : Result
  setupCells : Nat

def emit {n : Nat} (formula : CNFFormula n) (context : List Row) : Emission n :=
  let enhanced := generate formula context
  let initialized := seedSetup enhanced.value.formula context
  let strong := TightFeedback.iterate enhanced.value.formula (n+1) initialized.result
  ⟨enhanced,context,strong,enhanced.queryCells+initialized.cells+
    2*(sourceRecords enhanced.value.formula+rowsCells context+AffineCarrier.resultSize strong)+5⟩

theorem emit_query {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).binary.value.formula=(AffineJointEmission.emit formula context).query := by
  simp only [emit,generate_value,AffineJointEmission.emit_query]

theorem emit_context {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).context=(AffineJointEmission.emit formula context).context := rfl

theorem emit_strong {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).strong=(AffineJointEmission.emit formula context).strong := by
  simp only [emit,seedSetup_result,seedRows,generate_value,AffineJointEmission.emit_strong,
    AffineBinaryContext.seed,TightFeedback.generate]

theorem emit_queries {n : Nat} (formula : CNFFormula n) (context : List Row) :
    (emit formula context).binary.value.queries=(AffineJointEmission.emit formula context).queries := by
  simp only [emit,generate_value,AffineJointEmission.emit]

def constraints {n : Nat} (output : Emission n) : AffineClauses.Formula :=
  match output.strong with
  | .contradiction => [[]]
  | .basis basis => AffineClauseImage.liftCNF output.binary.value.formula++
      (output.context++basis).map (fun row => [row])

theorem constraints_value {n : Nat} (formula : CNFFormula n) (context : List Row) :
    constraints (emit formula context)=AffineJointEmission.constraints (AffineJointEmission.emit formula context) := by
  simp only [constraints,emit_query,emit_context,emit_strong,AffineJointEmission.constraints]
  rfl

theorem emit_read {n : Nat} (formula : CNFFormula n) (context : List Row) (input : Nat → Bool) :
    AffineClauses.formulaRead (constraints (emit formula context)) input=
      (CNFFormula.eval formula input && holds context input) := by
  rw [constraints_value,AffineJointEmission.constraints_read,AffineJointEmission.emit_read]

theorem final_phase_family {n : Nat} (original : CNFFormula n) (context : List Row) (inside : RowsWithin n context)
    (round : Nat) (basis : List Row)
    (state : Result.basis basis ∈ phaseStates (generate original context).value.formula
      (TightFeedback.iterate (generate original context).value.formula round
        (seedSetup (generate original context).value.formula context).result)) :
    Family n (augmentedClauses n original.length) (augmentedLiterals n (Extract.literalCount original))
      basis (generate original context).value.formula := by
  have final := run_final context (BinaryRelations.inventory n) (BinaryRelations.inventory n).length original
  change (generate original context).value.formula ∈ (generate original context).sources at final
  have bounds := generate_family original context _ final
  rw [seedSetup_result] at state
  have valid := StrongFeedbackScale.iterate_phase_family _ _ (seedRows_inside _ context inside) round basis state
  exact StrongFeedbackScale.family basis ⟨valid.1,valid.2.1⟩ _ _ _ bounds.1 bounds.2

theorem queryBudget_mono (n N storage large : Nat) (width : n ≤ N) (size : storage ≤ large) :
    queryBudget n storage ≤ queryBudget N large := by
  unfold queryBudget gaussianBudget EliminateCost.insertCellBudget EliminateCost.reduceCellBudget AffineCarrier.Cost.cellBound
  gcongr

theorem seedBudget_mono (n N clauses more literals terms contextStorage contextMore : Nat)
    (width : n ≤ N) (number : clauses ≤ more) (count : literals ≤ terms) (contextSize : contextStorage ≤ contextMore) :
    seedBudget n clauses literals contextStorage ≤ seedBudget N more terms contextMore := by
  have rowBound := StrongFeedbackScale.prepareStorage_mono n N clauses more literals terms width number count
  have prepareBound := StrongFeedbackScale.prepareBudget_mono n N clauses more literals terms width number count
  unfold seedBudget seedStorage extractBudget gaussianBudget EliminateCost.insertCellBudget
    EliminateCost.reduceCellBudget AffineCarrier.Cost.cellBound
  gcongr

def emissionBudget (n clauses literals contextStorage : Nat) : Nat :=
  16*n^4*queryBudget n contextStorage+
    seedBudget n (augmentedClauses n clauses) (augmentedLiterals n literals) contextStorage+
      2*(3*augmentedLiterals n literals+2*augmentedClauses n clauses+1+
        contextStorage+AffineCarrier.Cost.cellBound n+1)+5

theorem emit_setupCells {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context) :
    (emit formula context).setupCells ≤ emissionBudget n formula.length (Extract.literalCount formula) (rowsCells context) := by
  have queried := generate_queryCells formula context inside
  have number := AffineBinaryContext.generate_length formula context
  have terms := AffineBinaryContext.generate_literals formula context
  have initialized := seedSetup_cells (generate formula context).value.formula context inside
  rw [generate_value] at initialized
  have enlarged := seedBudget_mono n n _ (augmentedClauses n formula.length) _
    (augmentedLiterals n (Extract.literalCount formula)) (rowsCells context) (rowsCells context)
    (by rfl) number terms (by rfl)
  have strongValid := AffineBinaryContext.seed_valid formula context inside
  have stored := AffineCarrier.Cost.result_size n (AffineBinaryContext.seed formula context) strongValid.1 strongValid.2
  have same : (emit formula context).strong=AffineBinaryContext.seed formula context :=
    (emit_strong formula context).trans (AffineJointEmission.emit_strong formula context)
  change (generate formula context).queryCells+_+
    2*(sourceRecords (generate formula context).value.formula+rowsCells context+
      AffineCarrier.resultSize (emit formula context).strong)+5 ≤ _
  rw [same,generate_value]
  unfold emissionBudget sourceRecords augmentedClauses augmentedLiterals at *
  omega

theorem emissionBudget_mono (n N clauses more literals terms contextStorage contextMore : Nat)
    (width : n ≤ N) (number : clauses ≤ more) (count : literals ≤ terms) (contextSize : contextStorage ≤ contextMore) :
    emissionBudget n clauses literals contextStorage ≤ emissionBudget N more terms contextMore := by
  have queryBound := queryBudget_mono n N contextStorage contextMore width contextSize
  have clauseBound : augmentedClauses n clauses ≤ augmentedClauses N more := by unfold augmentedClauses; gcongr
  have literalBound : augmentedLiterals n literals ≤ augmentedLiterals N terms := by unfold augmentedLiterals; gcongr
  have seedBound := seedBudget_mono n N _ _ _ _ _ _ width clauseBound literalBound contextSize
  unfold emissionBudget AffineCarrier.Cost.cellBound
  gcongr

theorem final_initial_storage {n : Nat} (formula : CNFFormula n) (context : List Row) :
    rowsCells (seedRows (generate formula context).value.formula context) ≤
      seedStorage n (augmentedClauses n formula.length) (augmentedLiterals n (Extract.literalCount formula)) (rowsCells context) := by
  have actual := seedRows_storage (generate formula context).value.formula context
  rw [generate_value] at actual ⊢
  have number := AffineBinaryContext.generate_length formula context
  have terms := AffineBinaryContext.generate_literals formula context
  have enlarged := StrongFeedbackScale.prepareStorage_mono n n _ (augmentedClauses n formula.length) _
    (augmentedLiterals n (Extract.literalCount formula)) (by rfl) number terms
  unfold seedStorage augmentedClauses augmentedLiterals at *
  omega

theorem kernel_inside (n : Nat) (table : Array Row) (inside : AtomImage.SourceWithin n table) :
    RowsWithin table.size (AtomImage.generate table).kernel :=
  fun row member => ((AtomImage.generate_valid n table inside).2 row member).2

theorem kernel_storage (n : Nat) (table : Array Row) (inside : AtomImage.SourceWithin n table) :
    rowsCells (AtomImage.generate table).kernel ≤ table.size*(table.size+2) := by
  have each := StrongFeedbackScale.rows_storage table.size (AtomImage.generate table).kernel
    (AtomImage.generate_valid n table inside).2
  have count := AtomImage.generate_count table
  exact each.trans (Nat.mul_le_mul_right _ (by omega))

def sourceEmit (formula : AffineClauses.Formula) : Emission (AffineClauseImage.width formula) :=
  let table := AffineClauseImage.table formula
  let image := AtomImage.generate table
  emit (AffineClauseImage.atomFormula formula) image.kernel

theorem sourceEmit_query (formula : AffineClauses.Formula) :
    (sourceEmit formula).binary.value.formula =
      (AffineJointEmission.emit (AffineClauseImage.atomFormula formula)
        (AtomImage.generate (AffineClauseImage.table formula)).kernel).query := emit_query _ _

theorem sourceEmit_constraints (formula : AffineClauses.Formula) :
    constraints (sourceEmit formula)=AffineJointEmission.constraints
      (AffineJointEmission.emit (AffineClauseImage.atomFormula formula)
        (AtomImage.generate (AffineClauseImage.table formula)).kernel) := constraints_value _ _

theorem sourceEmit_read (formula : AffineClauses.Formula) (input : Nat → Bool) :
    AffineClauses.formulaRead (constraints (sourceEmit formula))
      (Gates.coordinate (AffineClauseImage.table formula) input)=AffineClauses.formulaRead formula input := by
  rw [sourceEmit_constraints,AffineJointEmission.constraints_read,AffineJointEmission.emit_source_read]

theorem sourceEmit_allows (formula : AffineClauses.Formula) (target : Nat → Bool) :
    AffineClauses.formulaRead (constraints (sourceEmit formula)) target=
      AffineSharedSource.allows (AffineSharedSource.generate formula) target := by
  rw [sourceEmit_constraints,AffineSharedSource.generate_allows,
    AffineJointEmission.constraints_read,AffineJointEmission.emit_read,AffineClauseImage.constraints_read]

private theorem source_counts (formula : AffineClauses.Formula) :
    (AffineClauseImage.atomFormula formula).length=formula.length+1 ∧
      Extract.literalCount (AffineClauseImage.atomFormula formula)=AffineClauses.Cost.rowCount formula+1 := by
  constructor
  · change (Atoms.compile (AffineClauseImage.violations formula)).length=formula.length+1
    simp only [Atoms.compile_length,AffineClauseImage.violations,List.length_map]
  · change Extract.literalCount (Atoms.compile (AffineClauseImage.violations formula))=_
    rw [StrongFeedbackScale.compile_literals]
    simp [AffineClauseImage.violations,List.length_flatten,AffineClauses.Cost.rowCount,Function.comp_def]

def sourceClauses (records rows : Nat) : Nat := records+1+4*(rows+1)^2
def sourceLiterals (rows : Nat) : Nat := rows+1+8*(rows+1)^2
def contextBound (rows : Nat) : Nat := (rows+1)*(rows+3)

private theorem source_dimensions (formula : AffineClauses.Formula) :
    AffineClauseImage.width formula ≤ AffineClauses.Cost.rowCount formula+1 ∧
    augmentedClauses (AffineClauseImage.width formula) (AffineClauseImage.atomFormula formula).length ≤
      sourceClauses (AffineClauses.formulaSize formula) (AffineClauses.Cost.rowCount formula) ∧
    augmentedLiterals (AffineClauseImage.width formula) (Extract.literalCount (AffineClauseImage.atomFormula formula)) ≤
      sourceLiterals (AffineClauses.Cost.rowCount formula) := by
  have dimension := AffineJointResidual.observation_width formula
  have counts := source_counts formula
  have number : formula.length ≤ AffineClauses.formulaSize formula := by
    rw [AffineClauses.Cost.formula_size]
    omega
  have square := Nat.mul_le_mul dimension dimension
  refine ⟨dimension,?_,?_⟩
  · rw [counts.1]
    unfold augmentedClauses sourceClauses
    nlinarith
  · rw [counts.2]
    unfold augmentedLiterals sourceLiterals
    nlinarith

theorem source_context_storage (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula) :
    rowsCells (sourceEmit formula).context ≤ contextBound (AffineClauses.Cost.rowCount formula) := by
  have actual := kernel_storage n (AffineClauseImage.table formula) (AffineClauseImage.source_within n formula inside)
  rw [AffineClauseImage.table_size] at actual
  have dimension := (source_dimensions formula).1
  change rowsCells (AtomImage.generate (AffineClauseImage.table formula)).kernel ≤ _
  apply actual.trans
  unfold contextBound
  exact Nat.mul_le_mul dimension (by omega)

def sourceSetupBudget (rows records : Nat) : Nat :=
  emissionBudget (rows+1) (records+1) (rows+1) (contextBound rows)

theorem sourceEmit_setupCells (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula) :
    (sourceEmit formula).setupCells ≤ sourceSetupBudget (AffineClauses.Cost.rowCount formula) (AffineClauses.formulaSize formula) := by
  have bounded := kernel_inside n (AffineClauseImage.table formula) (AffineClauseImage.source_within n formula inside)
  rw [AffineClauseImage.table_size] at bounded
  have actual := emit_setupCells (AffineClauseImage.atomFormula formula) _ bounded
  have counts := source_counts formula
  have number : formula.length ≤ AffineClauses.formulaSize formula := by
    rw [AffineClauses.Cost.formula_size]
    omega
  have contextSize := source_context_storage n formula inside
  change rowsCells (AtomImage.generate (AffineClauseImage.table formula)).kernel ≤ _ at contextSize
  exact actual.trans (emissionBudget_mono _ _ _ _ _ _ _ _ (source_dimensions formula).1
    (by rw [counts.1]; omega) (by rw [counts.2]) contextSize)

/-- Every actual query phase stays in the one source dimension, including its decoded atom,
signed-capacity and matching structures. The bounds depend only on original records/row count. -/
theorem source_query_family (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula)
    (query : CNFFormula (AffineClauseImage.width formula)) (member : query ∈ (sourceEmit formula).binary.sources)
    (probe : CNFClause (AffineClauseImage.width formula)) (round : Nat) (basis : List Row)
    (state : Result.basis basis ∈ phaseStates query
      (TightFeedback.iterate query round (querySetup (sourceEmit formula).context probe).result)) :
    AffineClauseImage.width formula ≤ AffineClauses.Cost.rowCount formula+1 ∧
      Family (AffineClauseImage.width formula) (sourceClauses (AffineClauses.formulaSize formula) (AffineClauses.Cost.rowCount formula))
        (sourceLiterals (AffineClauses.Cost.rowCount formula)) basis query := by
  have contextInside := kernel_inside n (AffineClauseImage.table formula) (AffineClauseImage.source_within n formula inside)
  rw [AffineClauseImage.table_size] at contextInside
  have bounds := generate_family (AffineClauseImage.atomFormula formula) _ query member
  have dimensions := source_dimensions formula
  rw [querySetup_result] at state
  have valid := StrongFeedbackScale.iterate_phase_family query _ (probe_inside _ contextInside probe) round basis state
  exact ⟨dimensions.1,StrongFeedbackScale.family basis ⟨valid.1,valid.2.1⟩ query _ _
    (bounds.1.trans dimensions.2.1) (bounds.2.trans dimensions.2.2)⟩

theorem source_final_family (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula)
    (round : Nat) (basis : List Row)
    (state : Result.basis basis ∈ phaseStates (sourceEmit formula).binary.value.formula
      (TightFeedback.iterate (sourceEmit formula).binary.value.formula round
        (seedSetup (sourceEmit formula).binary.value.formula (sourceEmit formula).context).result)) :
    Family (AffineClauseImage.width formula) (sourceClauses (AffineClauses.formulaSize formula) (AffineClauses.Cost.rowCount formula))
      (sourceLiterals (AffineClauses.Cost.rowCount formula)) basis (sourceEmit formula).binary.value.formula := by
  have contextInside := kernel_inside n (AffineClauseImage.table formula) (AffineClauseImage.source_within n formula inside)
  rw [AffineClauseImage.table_size] at contextInside
  have final := run_final (AtomImage.generate (AffineClauseImage.table formula)).kernel
    (BinaryRelations.inventory (AffineClauseImage.width formula))
    (BinaryRelations.inventory (AffineClauseImage.width formula)).length (AffineClauseImage.atomFormula formula)
  have bounds := generate_family (AffineClauseImage.atomFormula formula) _ _ final
  have dimensions := source_dimensions formula
  rw [seedSetup_result] at state
  have valid := StrongFeedbackScale.iterate_phase_family _ _ (seedRows_inside _ _ contextInside) round basis state
  exact StrongFeedbackScale.family basis ⟨valid.1,valid.2.1⟩ _ _ _
    (bounds.1.trans dimensions.2.1) (bounds.2.trans dimensions.2.2)

theorem source_final_initial_storage (n : Nat) (formula : AffineClauses.Formula)
    (inside : AffineClauses.Within n formula) :
    rowsCells (seedRows (sourceEmit formula).binary.value.formula (sourceEmit formula).context) ≤
      seedStorage (AffineClauses.Cost.rowCount formula+1)
        (sourceClauses (AffineClauses.formulaSize formula) (AffineClauses.Cost.rowCount formula))
        (sourceLiterals (AffineClauses.Cost.rowCount formula)) (contextBound (AffineClauses.Cost.rowCount formula)) := by
  have actual := final_initial_storage (AffineClauseImage.atomFormula formula)
    (AtomImage.generate (AffineClauseImage.table formula)).kernel
  have contextSize := source_context_storage n formula inside
  have dimensions := source_dimensions formula
  have rowsBound := StrongFeedbackScale.prepareStorage_mono _ _ _ _ _ _ dimensions.1 dimensions.2.1 dimensions.2.2
  change rowsCells (AtomImage.generate (AffineClauseImage.table formula)).kernel ≤ _ at contextSize
  apply actual.trans
  unfold seedStorage
  exact Nat.add_le_add (Nat.add_le_add contextSize (Nat.mul_le_mul_left 5 dimensions.2.1)) rowsBound

private theorem image_storage (n q : Nat) (state : AtomImage.State) (valid : state.Valid n q)
    (count : state.basis.length+state.kernel.length ≤ q) :
    AffineForget.Cost.imageSize state ≤ q*(n+q+3)+2 := by
  have tags := sum_bound AffineForget.Cost.tagSize state.basis (n+q+3) (by
    intro row member
    have left := Table.row_length_le n row.coeff (valid.1 row member).1
    have right := Table.row_length_le q row.label (valid.1 row member).2
    change row.vars.length ≤ n at left
    unfold AffineForget.Cost.tagSize rowCells
    omega)
  change AffineForget.Cost.tagsSize state.basis ≤ _ at tags
  have kernel := StrongFeedbackScale.rows_storage q state.kernel valid.2
  have scaled := Nat.mul_le_mul_right (n+q+3) count
  unfold AffineForget.Cost.imageSize
  nlinarith

theorem source_image_prefix_storage (n : Nat) (formula : AffineClauses.Formula)
    (inside : AffineClauses.Within n formula) (takeCount : Nat) :
    AffineForget.Cost.imageSize (AtomImage.runFrom AtomImage.initial
      ((AtomImage.tagged (AffineClauseImage.table formula)).take takeCount)) ≤
      (AffineClauses.Cost.rowCount formula+1)*(n+AffineClauses.Cost.rowCount formula+4)+2 := by
  let table := AffineClauseImage.table formula
  have sourceInside := AffineClauseImage.source_within n formula inside
  have valid := AtomImage.runFrom_valid n table.size AtomImage.initial (by simp [AtomImage.State.Valid,AtomImage.initial])
    ((AtomImage.tagged table).take takeCount) (fun row member =>
      AtomImage.tagged_within n table sourceInside row (List.mem_of_mem_take member))
  have count := AtomImage.runFrom_count AtomImage.initial ((AtomImage.tagged table).take takeCount)
  have length : ((AtomImage.tagged table).take takeCount).length ≤ table.size := by
    simp only [List.length_take,AtomImage.tagged,List.length_ofFn]
    exact Nat.min_le_right _ _
  have countBound : (AtomImage.runFrom AtomImage.initial ((AtomImage.tagged table).take takeCount)).basis.length+
      (AtomImage.runFrom AtomImage.initial ((AtomImage.tagged table).take takeCount)).kernel.length ≤ table.size := by
    rw [count]
    simpa only [AtomImage.initial,List.length_nil,Nat.zero_add] using length
  have bounded := image_storage n table.size _ valid countBound
  have dimension : table.size ≤ AffineClauses.Cost.rowCount formula+1 := by
    rw [AffineClauseImage.table_size]
    exact (source_dimensions formula).1
  apply bounded.trans
  exact Nat.add_le_add_right (Nat.mul_le_mul dimension (by omega)) 2

def sourceImageBudget (n rows records : Nat) : Nat :=
  (records+(rows+1))*(2*(n+(rows+1))+5)+(rows+1)*(n*AtomImage.stepBudget n (rows+1)+(rows+1)+11)+2

/-- This reuses the already paid tagged Gaussian ledger; the original raw row-term
count, including duplicate addresses, remains in its bound. -/
theorem source_image_visits (n : Nat) (formula : AffineClauses.Formula) (inside : AffineClauses.Within n formula) :
    AtomImage.generateVisits (AffineClauseImage.table formula) ≤
      sourceImageBudget n (AffineClauses.Cost.rowCount formula) (AffineClauses.formulaSize formula) := by
  have actual := AtomImage.generateVisits_bound n (AffineClauseImage.table formula)
    (AffineClauseImage.source_within n formula inside)
  have sourceTerms := AffineSharedSource.Scale.table_terms formula
  rw [AffineSharedSource.generate_table] at sourceTerms
  have records : AffineClauses.Cost.termCount formula ≤ AffineClauses.formulaSize formula := by
    rw [AffineClauses.Cost.formula_size]
    omega
  have terms := sourceTerms.trans records
  rw [AffineClauseImage.table_size] at actual
  have dimension := (source_dimensions formula).1
  apply actual.trans
  unfold sourceImageBudget AtomImage.stepBudget
  gcongr

end SaturationMonoid.ComplexityProjection.SATSource.AffineContextScale

import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ContextScale

/-!
The first strong-feedback phase executes the original residual rows, multiplicity-
sensitive permutation test, first-answer scan and Gaussian insertion. Its ledger
counts these source operations and copies, not the unlowered later phases or TM time.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineFeedbackCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open CapacityMatching.RowCost (rowCells rowsCells)
abbrev Counted := CapacityMatching.SourceCost.Counted

def erase (a : Nat) : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | b::rest =>
      if b==a then ⟨rest,2*rest.length+2⟩
      else let next := erase a rest
           ⟨b::next.value,next.cells+2*next.value.length+4⟩

theorem erase_value (a : Nat) (values : List Nat) : (erase a values).value=values.erase a := by
  induction values with
  | nil => rfl
  | cons b rest ih => simp only [erase,List.erase_cons,ih]; split <;> rfl

theorem erase_length (a : Nat) (values : List Nat) : (erase a values).value.length ≤ values.length := by
  rw [erase_value]
  exact List.length_erase_le

def eraseBudget (length : Nat) : Nat := length*(2*length+4)+1

theorem erase_cells (a : Nat) (values : List Nat) : (erase a values).cells ≤ eraseBudget values.length := by
  induction values with
  | nil => simp [erase,eraseBudget]
  | cons b rest ih =>
      have size := erase_length a rest
      simp only [erase,List.length_cons]
      split <;> unfold eraseBudget at * <;> nlinarith

private theorem member_contains (a : Nat) (values : List Nat) :
    (AffineClauseProduct.Cost.member a values).value=values.contains a := by
  apply Bool.eq_iff_iff.mpr
  simp [AffineClauseProduct.Cost.member_value]

def perm : List Nat → List Nat → Counted Bool
  | [],right => ⟨right.isEmpty,1⟩
  | a::rest,right =>
      let found := AffineClauseProduct.Cost.member a right
      if found.value then
        let removed := erase a right
        let next := perm rest removed.value
        ⟨next.value,found.visits+removed.cells+next.cells+2*removed.value.length+5⟩
      else ⟨false,found.visits+2⟩

theorem perm_value (left right : List Nat) : (perm left right).value=left.isPerm right := by
  induction left generalizing right with
  | nil => rfl
  | cons a rest ih =>
      simp only [perm,List.isPerm,member_contains,ih,erase_value]
      split <;> simp_all

def permUnit (right : Nat) : Nat := eraseBudget right+4*right+8

theorem perm_cells (left right : List Nat) :
    (perm left right).cells ≤ left.length*permUnit right.length+1 := by
  induction left generalizing right with
  | nil => simp [perm]
  | cons a rest ih =>
      have lookup := AffineClauseProduct.Cost.member_visits a right
      have erased := erase_cells a right
      have length := erase_length a right
      have later := ih (erase a right).value
      have unit : permUnit (erase a right).value.length ≤ permUnit right.length := by
        unfold permUnit eraseBudget
        gcongr
      have tail := later.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ unit) 1)
      simp only [perm,List.length_cons]
      split <;> unfold permUnit at * <;> nlinarith

def permBudget (n : Nat) : Nat := n*permUnit n+1

theorem perm_cells_bounded (n : Nat) (left right : List Nat) (a : left.length ≤ n) (b : right.length ≤ n) :
    (perm left right).cells ≤ permBudget n := by
  apply (perm_cells left right).trans
  unfold permBudget permUnit eraseBudget
  gcongr

namespace Propagation
open Affine.Propagation (Reading)

def residualRow {n : Nat} (basis : List Row) (literal : CNFLiteral n) : Counted Row :=
  let reduced := EliminateCost.reduce basis (Affine.Propagation.badLiteral literal)
  let normalized := CapacityMatching.RowCost.normalize reduced.row
  ⟨normalized.value,reduced.cells+normalized.cells+
    2*rowCells reduced.row+2*rowCells normalized.value+5⟩

theorem residualRow_value {n : Nat} (basis : List Row) (literal : CNFLiteral n) :
    (residualRow basis literal).value=Affine.Propagation.residualRow basis literal := by
  simp only [residualRow,EliminateCost.reduce_row,CapacityMatching.RowCost.normalize,Affine.Propagation.residualRow]

theorem residualRow_valid {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (literal : CNFLiteral n) :
    Table.RowValid n (residualRow basis literal).value := by
  rw [residualRow_value]
  exact ⟨Row.normalize_nodup _,Affine.Propagation.residualRow_within basis inside literal⟩

def residualBudget (n : Nat) : Nat := n*EliminateCost.reduceCellBudget n+n*(2*n+5)+10*n+28

theorem residualRow_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (literal : CNFLiteral n) : (residualRow basis literal).cells ≤ residualBudget n := by
  have unit : Table.RowValid n (Affine.Propagation.badLiteral literal) :=
    ⟨by simp [Affine.Propagation.badLiteral],Affine.Propagation.badLiteral_within literal⟩
  have reduced := EliminateCost.reduce_cells n basis (fun row member => ⟨valid.1.1 row member,valid.2 row member⟩) _ unit
  have rank := basis_length_le n basis valid.1 valid.2
  have inside := reduceWith_within n basis valid.2 _ unit.2
  have nodup := reduceWith_nodup basis valid.1.1 _ unit.1
  have length := Table.row_length_le n _ ⟨nodup,inside⟩
  have normalized := CapacityMatching.RowCost.normalize_cells n _ inside
  have output := CapacityMatching.RowCost.normalize_storage n _ inside
  simp only [residualRow,EliminateCost.reduce_row]
  unfold residualBudget rowCells
  change (EliminateCost.reduce basis (Affine.Propagation.badLiteral literal)).cells+_+
    2*((reduceWith basis (Affine.Propagation.badLiteral literal)).vars.length+2)+
    2*rowCells (CapacityMatching.RowCost.normalize (reduceWith basis (Affine.Propagation.badLiteral literal))).value+5 ≤ _
  nlinarith [Nat.mul_le_mul_right (EliminateCost.reduceCellBudget n) rank]

def residuals {n : Nat} (basis : List Row) (clause : CNFClause n) : Counted (List Row) :=
  CapacityMatching.RowCost.gather (fun literal =>
    let generated := residualRow basis literal
    ⟨[generated.value],generated.cells+rowCells generated.value+2⟩) clause

theorem residuals_value {n : Nat} (basis : List Row) (clause : CNFClause n) :
    (residuals basis clause).value=clause.map (Affine.Propagation.residualRow basis) := by
  rw [residuals,CapacityMatching.RowCost.gather_value]
  simp only [residualRow_value]
  induction clause <;> simp_all

theorem residuals_valid {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (clause : CNFClause n) :
    ∀ row ∈ (residuals basis clause).value,Table.RowValid n row := by
  rw [residuals_value]
  intro row member
  obtain ⟨literal,_,rfl⟩ := List.mem_map.mp member
  simpa only [residualRow_value] using residualRow_valid basis inside literal

theorem residuals_length {n : Nat} (basis : List Row) (clause : CNFClause n) :
    (residuals basis clause).value.length=clause.length := by rw [residuals_value,List.length_map]

def residualsBudget (n count : Nat) : Nat := count*(residualBudget n+n+4+(count+1)*(n+2)+5)+1

theorem residuals_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (clause : CNFClause n) : (residuals basis clause).cells ≤ residualsBudget n clause.length := by
  apply CapacityMatching.RowCost.gather_cells _ clause (residualBudget n+n+4) (n+2)
  · intro literal _
    have cost := residualRow_cells basis valid literal
    have size := Table.row_length_le n _ (residualRow_valid basis valid.2 literal)
    dsimp
    unfold rowCells
    omega
  · intro literal _
    have size := Table.row_length_le n _ (residualRow_valid basis valid.2 literal)
    simp only [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil]
    unfold rowCells
    omega

def readingSize : Reading → Nat
  | .forced row => rowCells row+1
  | _ => 1

def pivotSize : Option Row → Nat
  | none => 1
  | some row => rowCells row+1

def done (reading : Reading) : Counted Reading := ⟨reading,2*readingSize reading+1⟩

def scan (pivot : Option Row) : List Row → Counted Reading
  | [] => done (match pivot with | none => .contradiction | some row => .forced (Affine.Propagation.flip row))
  | row::rest =>
      let answer :=
        if row.vars=[] then
          if row.rhs then done .satisfied else scan pivot rest
        else match pivot with
          | none => scan (some row) rest
          | some first =>
              let compared := perm row.vars first.vars
              let next := if compared.value then
                if row.rhs=first.rhs then scan pivot rest else done .satisfied
                else done .unresolved
              ⟨next.value,next.cells+compared.cells⟩
      ⟨answer.value,answer.cells+2*rowCells row+2*pivotSize pivot+2*readingSize answer.value+5⟩

theorem scan_value (pivot : Option Row) (rows : List Row) :
    (scan pivot rows).value=Affine.Propagation.scan pivot rows := by
  induction rows generalizing pivot with
  | nil => cases pivot <;> rfl
  | cons row rest ih =>
      by_cases empty : row.vars=[]
      · cases rhs : row.rhs <;> simp [scan,Affine.Propagation.scan,empty,rhs,done,ih]
      · cases pivot with
        | none => simp [scan,Affine.Propagation.scan,empty,ih]
        | some first =>
            by_cases agrees : row.vars.isPerm first.vars=true
            · by_cases rhs : row.rhs=first.rhs <;>
                simp [scan,Affine.Propagation.scan,empty,perm_value,agrees,rhs,done,ih]
            · simp [scan,Affine.Propagation.scan,empty,perm_value,agrees,done]

theorem readingSize_scan (n : Nat) (pivot : Option Row) (rows : List Row)
    (bounded : ∀ row ∈ pivot.toList++rows,row.vars.length ≤ n) :
    readingSize (scan pivot rows).value ≤ n+3 := by
  rw [scan_value]
  cases result : Affine.Propagation.scan pivot rows with
  | satisfied => simp [readingSize]
  | contradiction => simp [readingSize]
  | unresolved => simp [readingSize]
  | forced row =>
      have size := Affine.Propagation.scan_forced_property rows pivot (fun row => row.vars.length ≤ n)
        (fun value member => bounded value member) row result
      simp only [readingSize,rowCells]
      omega

theorem pivotSize_bound (n : Nat) (pivot : Option Row) (bounded : ∀ row ∈ pivot.toList,row.vars.length ≤ n) :
    pivotSize pivot ≤ n+3 := by
  cases pivot with
  | none => simp [pivotSize]
  | some row =>
      have size := bounded row (by simp)
      simp only [pivotSize,rowCells]
      omega

def scanUnit (n : Nat) : Nat := permBudget n+6*n+24
def scanBudget (n count : Nat) : Nat := count*scanUnit n+2*n+7

theorem scan_cells (n : Nat) (pivot : Option Row) (rows : List Row)
    (bounded : ∀ row ∈ pivot.toList++rows,row.vars.length ≤ n) :
    (scan pivot rows).cells ≤ scanBudget n rows.length := by
  induction rows generalizing pivot with
  | nil =>
      have size := pivotSize_bound n pivot (by simpa using bounded)
      have value : (scan pivot []).cells=2*pivotSize pivot+1 := by cases pivot <;> rfl
      rw [value]
      simp only [scanBudget,List.length_nil,Nat.zero_mul,Nat.zero_add]
      omega
  | cons row rest ih =>
      simp only [List.length_cons]
      have first := bounded row (by simp)
      have output := readingSize_scan n pivot (row::rest) bounded
      have pivotBound := pivotSize_bound n pivot (fun value member => bounded value (by simp [member]))
      have same := ih pivot (fun value member => bounded value (by
        rcases List.mem_append.mp member with old | tail
        · exact List.mem_append_left _ old
        · simp [tail]))
      have changed := ih (some row) (by
        intro value member
        simp only [Option.toList_some,List.singleton_append,List.mem_cons] at member
        rcases member with rfl | tail
        · exact first
        · exact bounded value (by simp [tail]))
      by_cases empty : row.vars=[]
      · cases rhs : row.rhs <;>
          simp only [scan,if_pos empty,rhs,Bool.false_eq_true,if_false,if_true,done] at output ⊢
        all_goals unfold scanBudget scanUnit rowCells at *; nlinarith
      · cases pivot with
        | none =>
            simp only [scan,if_neg empty,pivotSize] at output ⊢
            unfold scanBudget scanUnit rowCells at *
            nlinarith
        | some old =>
            have oldBound := bounded old (by simp)
            have compared := perm_cells_bounded n row.vars old.vars first oldBound
            by_cases agrees : (perm row.vars old.vars).value=true
            · by_cases rhs : row.rhs=old.rhs <;>
                simp [scan,empty,agrees,rhs,done] at output ⊢
              all_goals unfold scanBudget scanUnit rowCells at *; nlinarith
            · simp only [scan,if_neg empty,if_neg agrees,done] at output ⊢
              unfold scanBudget scanUnit rowCells at *
              nlinarith

def inspect {n : Nat} (basis : List Row) (clause : CNFClause n) : Counted Reading :=
  let rows := residuals basis clause
  let scanned := scan none rows.value
  ⟨scanned.value,rows.cells+scanned.cells+2*rowsCells rows.value+2*readingSize scanned.value+3⟩

theorem inspect_value {n : Nat} (basis : List Row) (clause : CNFClause n) :
    (inspect basis clause).value=Affine.Propagation.inspect basis clause := by
  simp only [inspect,scan_value,residuals_value,Affine.Propagation.inspect]

theorem inspect_readingSize {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (clause : CNFClause n) :
    readingSize (inspect basis clause).value ≤ n+3 := by
  apply readingSize_scan n none (residuals basis clause).value
  intro row member
  exact Table.row_length_le n row (residuals_valid basis inside clause row (by simpa using member))

def inspectBudget (n count : Nat) : Nat :=
  residualsBudget n count+scanBudget n count+2*count*(n+2)+2*(n+3)+3

theorem inspect_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (clause : CNFClause n) :
    (inspect basis clause).cells ≤ inspectBudget n clause.length := by
  have source := residuals_cells basis valid clause
  have typed := residuals_valid basis valid.2 clause
  have scanned := scan_cells n none (residuals basis clause).value (by
    intro row member
    exact Table.row_length_le n row (typed row (by simpa using member)))
  have storage := StrongFeedbackScale.rows_storage n (residuals basis clause).value typed
  rw [residuals_length] at scanned storage
  have output := inspect_readingSize basis valid.2 clause
  change readingSize (scan none (residuals basis clause).value).value ≤ n+3 at output
  unfold inspect inspectBudget
  nlinarith

theorem inspectBudget_mono (n small large : Nat) (size : small ≤ large) :
    inspectBudget n small ≤ inspectBudget n large := by
  unfold inspectBudget residualsBudget scanBudget
  gcongr

def find {n : Nat} (basis : List Row) : CNFFormula n → Counted Reading
  | [] => done .unresolved
  | clause::rest =>
      let first := inspect basis clause
      let next := match first.value with
        | .forced row => done (.forced row)
        | .contradiction => done .contradiction
        | _ => find basis rest
      ⟨next.value,first.cells+next.cells+2*readingSize first.value+2*readingSize next.value+5⟩

theorem find_value {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (find basis formula).value=Affine.Propagation.find basis formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases found : Affine.Propagation.inspect basis clause <;>
        simp only [find,Affine.Propagation.find,inspect_value,found,done,ih]

theorem find_readingSize {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    readingSize (find basis formula).value ≤ n+3 := by
  rw [find_value]
  cases found : Affine.Propagation.find basis formula with
  | satisfied => simp [readingSize]
  | contradiction => simp [readingSize]
  | unresolved => simp [readingSize]
  | forced row =>
      obtain ⟨clause,_,hit⟩ := Affine.Propagation.find_forced_origin basis formula row found
      have size := inspect_readingSize basis inside clause
      simpa only [inspect_value,hit] using size

def findBudget (n clauses literals : Nat) : Nat := clauses*(inspectBudget n literals+6*(n+3)+6)+3

theorem find_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) (literals : Nat) (count : Extract.literalCount formula ≤ literals) :
    (find basis formula).cells ≤ findBudget n formula.length literals := by
  induction formula with
  | nil => simp [find,done,readingSize,findBudget]
  | cons clause rest ih =>
      have counts : clause.length+Extract.literalCount rest ≤ literals := count
      have first := (inspect_cells basis valid clause).trans (inspectBudget_mono n clause.length literals (by omega))
      have firstSize := inspect_readingSize basis valid.2 clause
      have tail := ih (by omega)
      have tailSize := find_readingSize basis valid.2 rest
      cases answer : (inspect basis clause).value <;>
        simp only [find,answer,done] at *
      all_goals unfold findBudget at *; simp only [List.length_cons] at *; nlinarith

def update {n : Nat} (formula : CNFFormula n) : Result → Counted Result
  | .contradiction => ⟨.contradiction,1⟩
  | .basis basis =>
      let found := find basis formula
      let applied : Counted Result := match found.value with
        | .forced row =>
            let inserted := EliminateCost.insert (.basis basis) row
            ⟨inserted.result,inserted.cells⟩
        | .contradiction => ⟨.contradiction,1⟩
        | _ => ⟨.basis basis,1⟩
      ⟨applied.value,found.cells+applied.cells+2*AffineCarrier.cellSize basis+
        2*AffineCarrier.resultSize applied.value+2*readingSize found.value+5⟩

theorem update_value {n : Nat} (formula : CNFFormula n) (result : Result) :
    (update formula result).value=Affine.Propagation.update formula result := by
  cases result with
  | contradiction => rfl
  | basis basis =>
      cases answer : Affine.Propagation.find basis formula <;>
        simp only [update,Affine.Propagation.update,find_value,answer,EliminateCost.insert_result]

def updateBudget (n clauses literals : Nat) : Nat :=
  findBudget n clauses literals+n*(2*n+5)+EliminateCost.insertCellBudget n+1+
    4*(AffineCarrier.Cost.cellBound n+1)+2*(n+3)+5

theorem update_cells {n : Nat} (formula : CNFFormula n) (result : Result)
    (valid : result.triangular ∧ result.within n) :
    (update formula result).cells ≤ updateBudget n formula.length (Extract.literalCount formula) := by
  cases result with
  | contradiction => simp only [update,updateBudget]; omega
  | basis basis =>
      have foundCost := find_cells basis valid formula _ (Nat.le_refl _)
      have size := find_readingSize basis valid.2 formula
      have inputSize := AffineCarrier.Cost.cell_size n basis valid.1 valid.2
      have outputSize := AffineCarrier.Cost.result_size n (Affine.Propagation.update formula (.basis basis))
        (Affine.Propagation.update_triangular formula _ valid.1) (Affine.Propagation.update_within formula _ valid.2)
      rw [← update_value] at outputSize
      cases answer : (find basis formula).value with
      | satisfied | unresolved | contradiction =>
          rw [answer] at size
          simp only [update,answer] at outputSize ⊢
          unfold updateBudget
          nlinarith
      | forced row =>
          have origin : Affine.Propagation.find basis formula=Reading.forced row := by simpa only [find_value] using answer
          obtain ⟨clause,_,hit⟩ := Affine.Propagation.find_forced_origin basis formula row origin
          have inside := Affine.Propagation.inspect_forced_within basis valid.2 clause row hit
          have inserted := EliminateCost.insert_cells n (.basis basis) valid.1 valid.2 row inside
          rw [answer] at size
          have length : row.vars.length ≤ n := by
            simp only [readingSize,rowCells] at size
            omega
          simp only [update,answer] at outputSize ⊢
          unfold updateBudget
          nlinarith [Nat.mul_le_mul_right (2*n+5) length]

end Propagation

/-- The other three row phases execute normally; this subtotal records only the
fully lowered first phase, without a charge for calling an unlowered phase. -/
structure Execution where
  value : Result
  propagationCells : Nat
  deriving Repr

def step {n : Nat} (formula : CNFFormula n) (result : Result) : Execution :=
  let propagated := Propagation.update formula result
  let atoms := Atoms.advance formula propagated.value
  let capacity := CapacityFeedback.advance formula atoms
  let tight := TightFeedback.advance formula capacity
  ⟨tight,propagated.cells⟩

theorem step_value {n : Nat} (formula : CNFFormula n) (result : Result) :
    (step formula result).value=TightFeedback.step formula result := by
  simp only [step,Propagation.update_value,TightFeedback.step,CapacityFeedback.step,JointFeedback.step]

theorem step_cells {n : Nat} (formula : CNFFormula n) (result : Result)
    (valid : result.triangular ∧ result.within n) :
    (step formula result).propagationCells ≤ Propagation.updateBudget n formula.length (Extract.literalCount formula) :=
  Propagation.update_cells formula result valid

def run {n : Nat} (formula : CNFFormula n) : Nat → Result → Execution
  | 0,result => ⟨result,0⟩
  | fuel+1,result =>
      let next := step formula result
      let tail := run formula fuel next.value
      ⟨tail.value,next.propagationCells+tail.propagationCells⟩

theorem run_value {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result) :
    (run formula fuel result).value=TightFeedback.iterate formula fuel result := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih => simp only [run,TightFeedback.iterate,ih,step_value]

theorem run_cells {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (valid : result.triangular ∧ result.within n) :
    (run formula fuel result).propagationCells ≤ fuel*Propagation.updateBudget n formula.length (Extract.literalCount formula) := by
  induction fuel generalizing result with
  | zero => simp [run]
  | succ fuel ih =>
      have first := step_cells formula result valid
      have nextValid := TightFeedback.step_invariants formula result valid.2 valid.1
      rw [← step_value] at nextValid
      have tail := ih (step formula result).value nextValid.symm
      simp only [run]
      nlinarith

structure Query where
  value : Result
  initializationCells : Nat
  propagationCells : Nat
  deriving Repr

def query {n : Nat} (formula : CNFFormula n) (context : List Row) (probe : CNFClause n) : Query :=
  let initialized := AffineContextScale.querySetup context probe
  let executed := run formula (n+1) initialized.result
  ⟨executed.value,initialized.cells,executed.propagationCells⟩

theorem query_value {n : Nat} (formula : CNFFormula n) (context : List Row) (probe : CNFClause n) :
    (query formula context probe).value=TightFeedback.generate formula (context++probe.map Affine.Propagation.badLiteral) := by
  simp only [query,run_value,AffineContextScale.querySetup_result,TightFeedback.generate]

theorem query_reject_value {n : Nat} (formula : CNFFormula n) (context : List Row) (probe : CNFClause n) :
    (match (query formula context probe).value with | .contradiction => true | .basis _ => false)=
      AffineBinaryContext.reject formula context probe := by
  rw [query_value]
  rfl

theorem query_cells {n : Nat} (formula : CNFFormula n) (context : List Row) (inside : RowsWithin n context)
    (probe : CNFClause n) (binary : probe.length=2) :
    (query formula context probe).initializationCells+(query formula context probe).propagationCells ≤
      AffineContextScale.queryBudget n (rowsCells context)+
        (n+1)*Propagation.updateBudget n formula.length (Extract.literalCount formula) := by
  have initial := AffineContextScale.querySetup_cells context inside probe binary
  have joined := AffineContextScale.probe_inside context inside probe
  have valid : (AffineContextScale.querySetup context probe).result.triangular ∧
      (AffineContextScale.querySetup context probe).result.within n := by
    rw [AffineContextScale.querySetup_result]
    exact ⟨eliminate_triangular _,eliminate_within n _ joined⟩
  exact Nat.add_le_add initial (run_cells formula (n+1) _ valid)

theorem query_holds {n : Nat} (formula : CNFFormula n) (context : List Row) (probe : CNFClause n)
    (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (query formula context probe).value.holds assignment)=
      (CNFFormula.eval formula assignment && holds (context++probe.map Affine.Propagation.badLiteral) assignment) := by
  rw [query_value,TightFeedback.generate_holds]

end SaturationMonoid.ComplexityProjection.SATSource.AffineFeedbackCost

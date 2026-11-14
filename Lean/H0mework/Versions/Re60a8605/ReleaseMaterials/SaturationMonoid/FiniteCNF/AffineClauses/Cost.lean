import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Core

/-!
Budgets for the actual affine-clause executor and a paired original-CNF compiler.
Input row occurrences are charged before normalization, including repeated addresses.
The counters are source-cell ledgers; counter evaluation and bit-level machine steps
remain separate from these bounds.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.Cost

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open AffineCarrier (Cells Valid read storage resultSize pack append)
open AffineCarrier.Cost (cellBound storage_bound result_size pack_length pack_visits)

@[simp] theorem rowTerms_nil : Gates.rowTerms [] = 0 := rfl
@[simp] theorem rowTerms_cons (row : Row) (rest : List Row) :
    Gates.rowTerms (row::rest) = row.vars.length+Gates.rowTerms rest := rfl

def rowCount (formula : Formula) : Nat := (formula.map List.length).sum

def termCount (formula : Formula) : Nat := (formula.map Gates.rowTerms).sum

@[simp] theorem rowCount_nil : rowCount [] = 0 := rfl
@[simp] theorem rowCount_cons (clause : Clause) (rest : Formula) :
    rowCount (clause::rest) = clause.length+rowCount rest := rfl
@[simp] theorem termCount_nil : termCount [] = 0 := rfl
@[simp] theorem termCount_cons (clause : Clause) (rest : Formula) :
    termCount (clause::rest) = Gates.rowTerms clause+termCount rest := rfl

@[simp] theorem formulaSize_nil : formulaSize [] = 1 := rfl

theorem formulaSize_cons (clause : Clause) (rest : Formula) :
    formulaSize (clause::rest) = CapacityMatching.RowCost.rowsCells clause+formulaSize rest+1 := by
  simp only [formulaSize,List.map_cons,List.sum_cons,List.length_cons]
  omega

theorem formula_size (formula : Formula) :
    formulaSize formula = termCount formula+2*rowCount formula+formula.length+1 := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      rw [formulaSize_cons,AffineCollect.Cost.rows_size,ih]
      simp only [termCount_cons,rowCount_cons,List.length_cons]
      ring

theorem flipped_inside (n : Nat) (clause : Clause) (inside : RowsWithin n clause) :
    RowsWithin n (clause.map Propagation.flip) := by
  intro row member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  exact inside original present

theorem flipped_terms (clause : Clause) :
    Gates.rowTerms (clause.map Propagation.flip) = Gates.rowTerms clause := by
  induction clause with
  | nil => rfl
  | cons row rest ih => simp only [List.map_cons,rowTerms_cons,Propagation.flip,ih]

theorem branches_length (clause : Clause) (result : Result) :
    (branches clause result).value.length ≤ clause.length := by
  induction clause generalizing result with
  | nil => rfl
  | cons row rest ih =>
      have first := pack_length (EliminateCost.insert result row).result
      have tail := ih (EliminateCost.insert result (Propagation.flip row)).result
      simp only [branches,append,List.length_append,List.length_cons]
      omega

theorem branches_inserts (clause : Clause) (result : Result) :
    (branches clause result).inserts = 2*clause.length := by
  induction clause generalizing result with
  | nil => rfl
  | cons row rest ih => simp only [branches,append,pack,ih,List.length_cons]; omega

theorem branches_xors (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (branches clause result).xors ≤ 2*clause.length*n := by
  induction clause generalizing result with
  | nil => simp [branches]
  | cons row rest ih =>
      have yes := EliminateCost.insert_xors n result triangular inside row
      have no := EliminateCost.insert_xors n result triangular inside (Propagation.flip row)
      have valid := AffineCarrier.insert_valid n result triangular inside (Propagation.flip row) (rowInside row (by simp))
      have tail := ih (fun other member => rowInside other (by simp [member])) _ valid.1 valid.2
      simp only [branches,append,pack,List.length_cons]
      nlinarith

def branchesBudget (n length terms : Nat) : Nat :=
  2*terms*(2*n+5)+length*(2*EliminateCost.insertCellBudget n+(2*length+12)*cellBound n+40)+1

theorem branches_visits (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (branches clause result).visits ≤ branchesBudget n clause.length (Gates.rowTerms clause) := by
  induction clause generalizing result with
  | nil => simp [branches,branchesBudget]
  | cons row rest ih =>
      let yes := (EliminateCost.insert result row).result
      let no := (EliminateCost.insert result (Propagation.flip row)).result
      have headInside := rowInside row (by simp)
      have tailInside : RowsWithin n rest := fun other member => rowInside other (by simp [member])
      have yesValid := AffineCarrier.insert_valid n result triangular inside row headInside
      have noValid := AffineCarrier.insert_valid n result triangular inside (Propagation.flip row) headInside
      have yesCost := EliminateCost.insert_cells n result triangular inside row headInside
      have noCost := EliminateCost.insert_cells n result triangular inside (Propagation.flip row) headInside
      change (EliminateCost.insert result (Propagation.flip row)).cells ≤
        row.vars.length*(2*n+5)+EliminateCost.insertCellBudget n at noCost
      have packed := pack_visits n yes yesValid.1 yesValid.2
      have tail := ih tailInside no noValid.1 noValid.2
      have yesStorage : storage (pack yes).value ≤ cellBound n := by
        have bound := storage_bound n _ (AffineCarrier.pack_valid n yes yesValid.1 yesValid.2)
        exact bound.trans (by simpa using Nat.mul_le_mul_right (cellBound n) (pack_length yes))
      have noStorage : storage (branches rest no).value ≤ rest.length*cellBound n :=
        (storage_bound n _ (branches_valid n rest tailInside no noValid.1 noValid.2)).trans
          (Nat.mul_le_mul_right _ (branches_length rest no))
      have initialSize := result_size n result triangular inside
      have yesSize := result_size n yes yesValid.1 yesValid.2
      have noSize := result_size n no noValid.1 noValid.2
      change (pack yes).visits+(branches rest no).visits+2*storage (pack yes).value+
        2*storage (branches rest no).value+5+
        (EliminateCost.insert result row).cells+(EliminateCost.insert result (Propagation.flip row)).cells+
        2*(resultSize result+resultSize yes+resultSize no)+16 ≤ _
      simp only [branchesBudget,List.length_cons,rowTerms_cons] at tail ⊢
      nlinarith

theorem checked_valid (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (EliminateCost.runFrom result (clause.map Propagation.flip)).result.triangular ∧
      (EliminateCost.runFrom result (clause.map Propagation.flip)).result.within n := by
  rw [EliminateCost.runFrom_result]
  exact ⟨eliminateFrom_triangular result triangular _,
    eliminateFrom_within n result inside _ (flipped_inside n clause rowInside)⟩

def checkedBudget (n length terms : Nat) : Nat :=
  terms*(2*n+5)+length*(EliminateCost.insertCellBudget n+1)+1

theorem checked_visits (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (EliminateCost.runFrom result (clause.map Propagation.flip)).cells ≤
      checkedBudget n clause.length (Gates.rowTerms clause) := by
  simpa only [flipped_terms,List.length_map,checkedBudget] using
    EliminateCost.runFrom_cells n result triangular inside _ (flipped_inside n clause rowInside)

theorem cut_length (clause : Clause) (result : Result) :
    (cut clause result).value.length ≤ clause.length+1 := by
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.flip)).result with
  | contradiction => simpa only [cut,checked] using (pack_length result).trans (Nat.le_add_left 1 clause.length)
  | basis basis => simpa only [cut,checked] using (branches_length clause result).trans (Nat.le_succ _)

theorem cut_inserts (clause : Clause) (result : Result) : (cut clause result).inserts ≤ 3*clause.length := by
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.flip)).result <;>
    simp only [cut,checked,pack,branches_inserts] <;> omega

theorem cut_xors (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause) (result : Result)
    (triangular : result.triangular) (inside : result.within n) : (cut clause result).xors ≤ 3*clause.length*n := by
  have test := EliminateCost.runFrom_xors n result triangular inside _ (flipped_inside n clause rowInside)
  simp only [List.length_map] at test
  have splitCost := branches_xors n clause rowInside result triangular inside
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.flip)).result <;>
    simp only [cut,checked,pack] <;> nlinarith

def cutBudget (n length terms : Nat) : Nat :=
  branchesBudget n length terms+terms*(2*n+9)+length*(EliminateCost.insertCellBudget n+9)+6*cellBound n+15

theorem cut_visits (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (cut clause result).visits ≤ cutBudget n clause.length (Gates.rowTerms clause) := by
  have test := checked_visits n clause rowInside result triangular inside
  have valid := checked_valid n clause rowInside result triangular inside
  have beforeSize := result_size n result triangular inside
  have afterSize := result_size n _ valid.1 valid.2
  have packed := pack_visits n result triangular inside
  have divided := branches_visits n clause rowInside result triangular inside
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.flip)).result <;>
    simp only [cut,checked,cutBudget,AffineCollect.Cost.rows_size] <;>
    simp only [checked,checkedBudget] at afterSize test <;> nlinarith

theorem action_length (clause : Clause) (cells : Cells) :
    (clauseAction clause cells).value.length ≤ cells.length*(clause.length+1) := by
  induction cells with
  | nil => simp [clauseAction]
  | cons basis rest ih =>
      have first := cut_length clause (.basis basis)
      simp only [clauseAction,append,List.length_append,List.length_cons]
      nlinarith

def actionBudget (n count length terms : Nat) : Nat :=
  count*(cutBudget n length terms+(count+1)*(length+1)*cellBound n+5)+1

theorem action_visits (n : Nat) (clause : Clause) (rowInside : RowsWithin n clause)
    (cells : Cells) (valid : Valid n cells) :
    (clauseAction clause cells).visits ≤ actionBudget n cells.length clause.length (Gates.rowTerms clause) := by
  induction cells with
  | nil => simp [clauseAction,actionBudget]
  | cons basis rest ih =>
      have headValid := valid basis (by simp)
      have tailValid : Valid n rest := fun other member => valid other (by simp [member])
      have first := cut_visits n clause rowInside (.basis basis) headValid.1 headValid.2
      have tail := ih tailValid
      have firstSize : storage (cut clause (.basis basis)).value ≤ (clause.length+1)*cellBound n :=
        (storage_bound n _ (cut_valid n clause rowInside (.basis basis) headValid.1 headValid.2)).trans
          (Nat.mul_le_mul_right _ (cut_length clause (.basis basis)))
      have tailSize : storage (clauseAction clause rest).value ≤ rest.length*(clause.length+1)*cellBound n :=
        (storage_bound n _ (clauseAction_valid n clause rowInside rest tailValid)).trans
          (Nat.mul_le_mul_right _ (action_length clause rest))
      simp only [clauseAction,append,actionBudget,List.length_cons] at tail ⊢
      nlinarith

theorem clean_size (formula : Formula) : formulaSize (clean formula) ≤ formulaSize formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases truth : tautology clause <;>
        simp [clean,truth,formulaSize_cons] at ih ⊢ <;> omega

def cleanBudget (n length rows terms : Nat) : Nat :=
  terms*(2*n+9)+rows*(EliminateCost.insertCellBudget n+9)+
    length*(2*cellBound n+2*(terms+2*rows+length+1)+11)+1

theorem cleanRun_ceiling (n : Nat) (formula : Formula) (inside : Within n formula)
    (ceiling : Nat) (size : formulaSize formula ≤ ceiling) :
    (cleanRun formula).visits ≤ termCount formula*(2*n+9)+rowCount formula*(EliminateCost.insertCellBudget n+9)+
      formula.length*(2*cellBound n+2*ceiling+11)+1 := by
  induction formula with
  | nil => simp [cleanRun]
  | cons clause rest ih =>
      have firstInside := inside clause (by simp)
      have tailInside : Within n rest := fun other member => inside other (by simp [member])
      have restSize : formulaSize rest ≤ ceiling := by rw [formulaSize_cons] at size; omega
      have tail := ih tailInside restSize
      have test := checked_visits n clause firstInside (.basis []) triangular_nil (by simp [Result.within,RowsWithin])
      have valid := checked_valid n clause firstInside (.basis []) triangular_nil (by simp [Result.within,RowsWithin])
      have outputSize : formulaSize (cleanRun (clause::rest)).value ≤ ceiling := by
        rw [cleanRun_value]
        exact (clean_size _).trans size
      have resultSizeBound := result_size n _ valid.1 valid.2
      change (EliminateCost.run (clause.map Propagation.flip)).cells ≤ _ at test
      change resultSize (EliminateCost.run (clause.map Propagation.flip)).result ≤ _ at resultSizeBound
      cases checked : (EliminateCost.run (clause.map Propagation.flip)).result <;>
        simp only [cleanRun,checked] at outputSize ⊢ <;>
        simp only [checked,checkedBudget,termCount_cons,rowCount_cons,List.length_cons,AffineCollect.Cost.rows_size]
          at resultSizeBound test ⊢ <;> nlinarith

theorem cleanRun_visits (n : Nat) (formula : Formula) (inside : Within n formula) :
    (cleanRun formula).visits ≤ cleanBudget n formula.length (rowCount formula) (termCount formula) := by
  simpa only [cleanBudget,formula_size] using cleanRun_ceiling n formula inside (formulaSize formula) (Nat.le_refl _)

def growth (formula : Formula) : Nat := (formula.map (fun clause => clause.length+1)).prod

theorem run_length (n : Nat) (formula : Formula) (inside : Within n formula)
    (cells : Cells) (valid : Valid n cells) :
    (run n formula cells).value.length ≤ cells.length*growth formula := by
  induction formula generalizing cells with
  | nil => simp [run,growth]
  | cons clause rest ih =>
      have firstInside := inside clause (by simp)
      have cutValid := clauseAction_valid n clause firstInside cells valid
      have first := action_length clause cells
      have shared := AffineCollect.collect_length n _ cutValid
      have next := ih (fun other member => inside other (by simp [member])) _
        (AffineCollect.collect_valid n _ cutValid)
      simp only [run,growth,List.map_cons,List.prod_cons]
      exact next.trans (by
        change _ ≤ cells.length*((clause.length+1)*growth rest)
        have bound := shared.trans first
        nlinarith)

def runBudget (n : Nat) : Formula → Nat → Nat
  | [],count => 2*count*cellBound n+1
  | clause::rest,count =>
      actionBudget n count clause.length (Gates.rowTerms clause)+
        AffineCollect.Cost.collectBudget n (count*(clause.length+1))+
        runBudget n rest (count*(clause.length+1))+3

theorem runBudget_mono (n : Nat) (formula : Formula) (small large : Nat) (bound : small ≤ large) :
    runBudget n formula small ≤ runBudget n formula large := by
  induction formula generalizing small large with
  | nil => simp only [runBudget]; gcongr
  | cons clause rest ih =>
      have next := ih (small*(clause.length+1)) (large*(clause.length+1)) (by gcongr)
      have shared := AffineCollect.Cost.collectBudget_mono n (small*(clause.length+1)) (large*(clause.length+1)) (by gcongr)
      simp only [runBudget,actionBudget]
      gcongr

theorem run_visits (n : Nat) (formula : Formula) (inside : Within n formula)
    (cells : Cells) (valid : Valid n cells) :
    (run n formula cells).visits ≤ runBudget n formula cells.length := by
  induction formula generalizing cells with
  | nil =>
      have stored := storage_bound n cells valid
      simp only [run,runBudget]
      nlinarith
  | cons clause rest ih =>
      have firstInside := inside clause (by simp)
      have cutValid := clauseAction_valid n clause firstInside cells valid
      have cutCost := action_visits n clause firstInside cells valid
      have cutSize := action_length clause cells
      have sharedCost := AffineCollect.Cost.collect_visits n _ cutValid
      have sharedBound := AffineCollect.Cost.collectBudget_mono n _ _ cutSize
      have sharedValid := AffineCollect.collect_valid n _ cutValid
      have sharedSize := (AffineCollect.collect_length n _ cutValid).trans cutSize
      have tail := ih (fun other member => inside other (by simp [member])) _ sharedValid
      have tailBound := runBudget_mono n rest _ _ sharedSize
      simp only [run,runBudget]
      omega

theorem runBudget_clean (n : Nat) (formula : Formula) (count : Nat) :
    runBudget n (clean formula) count ≤ runBudget n formula count := by
  induction formula generalizing count with
  | nil => rfl
  | cons clause rest ih =>
      cases truth : tautology clause with
      | false =>
          have shape : clean (clause::rest) = clause::clean rest := by simp [clean,truth]
          rw [shape,runBudget,runBudget]
          have tail := ih (count*(clause.length+1))
          omega
      | true =>
          have shape : clean (clause::rest) = clean rest := by simp [clean,truth]
          rw [shape,runBudget]
          have tail := ih count
          have bound := runBudget_mono n rest count (count*(clause.length+1)) (by nlinarith)
          omega

theorem generate_visits (n : Nat) (formula : Formula) (inside : Within n formula) :
    (generate n formula).visits ≤
      cleanBudget n formula.length (rowCount formula) (termCount formula)+runBudget n formula 1+2 := by
  have cleaned := cleanRun_visits n formula inside
  have final := run_visits n (clean formula) (clean_within n formula inside) [[]] (by
    intro basis member
    have same : basis=[] := List.mem_singleton.mp member
    subst basis
    exact ⟨triangular_nil,by simp [RowsWithin]⟩)
  have bounded := runBudget_clean n formula 1
  simp only [generate,cleanRun_value]
  simp only [List.length_singleton] at final
  omega

open CapacityMatching.RowCost (rowCells rowsCells)
open CapacityMatching.SourceCost (Counted)

/-- A shared row-list is traversed, with the original out-of-range zero default. -/
def lookup : List Row → Nat → Counted Row
  | [],_ => ⟨Gates.zeroRow,3⟩
  | row::_,0 => ⟨row,2*rowCells row+3⟩
  | row::rest,i+1 =>
      let next := lookup rest i
      ⟨next.value,next.cells+2*rowCells row+3⟩

theorem lookup_value (rows : List Row) (i : Nat) : (lookup rows i).value = rows.getD i Gates.zeroRow := by
  induction rows generalizing i with
  | nil => simp [lookup]
  | cons row rest ih => cases i <;> simp [lookup,ih]

theorem lookup_cells (rows : List Row) (i : Nat) :
    (lookup rows i).cells ≤ 2*rowsCells rows+3*rows.length+3 := by
  induction rows generalizing i with
  | nil => simp [lookup]
  | cons row rest ih =>
      cases i with
      | zero => simp [lookup]; omega
      | succ i =>
          have tail := ih i
          simp only [lookup,CapacityMatching.RowCost.rowsCells_cons,List.length_cons]
          omega

theorem lookup_valid (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (i : Nat) : Table.RowValid width (lookup rows i).value := by
  induction rows generalizing i with
  | nil => exact Table.zero_valid width
  | cons row rest ih =>
      cases i with
      | zero => exact valid row (by simp)
      | succ i => exact ih (fun other member => valid other (by simp [member])) i

def literal {n : Nat} (rows : List Row) (source : CNFLiteral n) : Counted Row :=
  let found := lookup rows source.var.val
  let value : Row := ⟨found.value.vars,found.value.rhs ^^ source.positive⟩
  ⟨value,found.cells+2*rowCells value+5⟩

theorem literal_value {n : Nat} (table : Array Row) (source : CNFLiteral n) :
    (literal table.toList source).value = literalRow table source := by
  simp only [literal,lookup_value,literalRow]

theorem literal_valid {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (source : CNFLiteral n) :
    Table.RowValid width (literal rows source).value := lookup_valid width rows valid source.var.val

theorem source_storage (width : Nat) (rows : List Row) (valid : ∀ row ∈ rows, Table.RowValid width row) :
    rowsCells rows ≤ rows.length*(width+2) := by
  simpa using CapacityMatching.RowCost.table_storage width rows.toArray valid

def literalBudget (width size : Nat) : Nat := 2*size*(width+2)+3*size+2*width+12

theorem literal_cells {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (source : CNFLiteral n) :
    (literal rows source).cells ≤ literalBudget width rows.length := by
  have lookupBound := lookup_cells rows source.var.val
  have stored := source_storage width rows valid
  have output := Table.row_length_le width _ (literal_valid width rows valid source)
  change (lookup rows source.var.val).value.vars.length ≤ width at output
  simp only [literal,literalBudget,rowCells]
  nlinarith

def compileClause {n : Nat} (rows : List Row) : CNFClause n → Counted Clause
  | [] => ⟨[],1⟩
  | source::rest =>
      let first := literal rows source
      let tail := compileClause rows rest
      let value := first.value::tail.value
      ⟨value,first.cells+tail.cells+2*rowsCells value+4⟩

theorem compileClause_value {n : Nat} (table : Array Row) (clause : CNFClause n) :
    (compileClause table.toList clause).value = clause.map (literalRow table) := by
  induction clause with
  | nil => rfl
  | cons source rest ih => simp only [compileClause,literal_value,ih,List.map_cons]

theorem compileClause_length {n : Nat} (rows : List Row) (clause : CNFClause n) :
    (compileClause rows clause).value.length = clause.length := by
  induction clause with
  | nil => rfl
  | cons source rest ih => simp only [compileClause,List.length_cons,ih]

theorem compileClause_storage {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (clause : CNFClause n) :
    rowsCells (compileClause rows clause).value ≤ clause.length*(width+2) := by
  induction clause with
  | nil => simp [compileClause]
  | cons source rest ih =>
      have first := Table.row_length_le width _ (literal_valid width rows valid source)
      simp only [compileClause,CapacityMatching.RowCost.rowsCells_cons,rowCells,List.length_cons]
      nlinarith

theorem compileClause_terms {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (clause : CNFClause n) :
    Gates.rowTerms (compileClause rows clause).value ≤ clause.length*width := by
  have storage := compileClause_storage width rows valid clause
  rw [AffineCollect.Cost.rows_size,compileClause_length] at storage
  nlinarith

def clauseBudget (width size length : Nat) : Nat :=
  length*(literalBudget width size+2*length*(width+2)+4)+1

theorem compileClause_cells {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (clause : CNFClause n) :
    (compileClause rows clause).cells ≤ clauseBudget width rows.length clause.length := by
  induction clause with
  | nil => simp [compileClause,clauseBudget]
  | cons source rest ih =>
      have first := literal_cells width rows valid source
      have output := compileClause_storage width rows valid (source::rest)
      simp only [compileClause] at output ⊢
      simp only [clauseBudget,List.length_cons] at ih output ⊢
      nlinarith

def compileFormula {n : Nat} (rows : List Row) : CNFFormula n → Counted Formula
  | [] => ⟨[],1⟩
  | clause::rest =>
      let first := compileClause rows clause
      let tail := compileFormula rows rest
      let value := first.value::tail.value
      ⟨value,first.cells+tail.cells+2*formulaSize value+5⟩

theorem compileFormula_value {n : Nat} (table : Array Row) (formula : CNFFormula n) :
    (compileFormula table.toList formula).value = AffineClauses.compile table formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [compileFormula,compileClause_value,ih,AffineClauses.compile,List.map_cons]

theorem compileFormula_length {n : Nat} (rows : List Row) (formula : CNFFormula n) :
    (compileFormula rows formula).value.length = formula.length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp only [compileFormula,List.length_cons,ih]

theorem compileFormula_rows {n : Nat} (rows : List Row) (formula : CNFFormula n) :
    rowCount (compileFormula rows formula).value = Extract.literalCount formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      simp only [compileFormula,rowCount_cons,compileClause_length,ih,Extract.literalCount,List.map_cons,List.sum_cons]

theorem compileFormula_terms {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (formula : CNFFormula n) :
    termCount (compileFormula rows formula).value ≤ Extract.literalCount formula*width := by
  induction formula with
  | nil => simp [compileFormula,Extract.literalCount]
  | cons clause rest ih =>
      have first := compileClause_terms width rows valid clause
      simp only [compileFormula,termCount_cons,Extract.literalCount,List.map_cons,List.sum_cons] at ih ⊢
      nlinarith

theorem compileFormula_storage {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (formula : CNFFormula n) :
    formulaSize (compileFormula rows formula).value ≤ Extract.literalCount formula*(width+2)+formula.length+1 := by
  have terms := compileFormula_terms width rows valid formula
  rw [formula_size,compileFormula_rows,compileFormula_length]
  nlinarith

def formulaBudget (width size length literals : Nat) : Nat :=
  literals*(literalBudget width size+2*literals*(width+2)+4)+
    length*(2*(literals*(width+2)+length+1)+6)+1

theorem compileFormula_ceiling {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (formula : CNFFormula n)
    (length literals : Nat) (number : formula.length ≤ length) (terms : Extract.literalCount formula ≤ literals) :
    (compileFormula rows formula).cells ≤
      Extract.literalCount formula*(literalBudget width rows.length+2*literals*(width+2)+4)+
        formula.length*(2*(literals*(width+2)+length+1)+6)+1 := by
  induction formula with
  | nil => simp [compileFormula,Extract.literalCount]
  | cons clause rest ih =>
      have countShape : Extract.literalCount (clause::rest) = clause.length+Extract.literalCount rest := rfl
      have tail := ih (by simpa using Nat.le_trans (Nat.le_succ rest.length) number)
        (by rw [countShape] at terms; omega)
      have first := compileClause_cells width rows valid clause
      have short : clause.length ≤ literals := by rw [countShape] at terms; omega
      have firstBound : (compileClause rows clause).cells ≤
          clause.length*(literalBudget width rows.length+2*literals*(width+2)+4)+1 := by
        refine first.trans ?_
        unfold clauseBudget
        gcongr
      have stored := compileFormula_storage width rows valid (clause::rest)
      have output : formulaSize (compileFormula rows (clause::rest)).value ≤ literals*(width+2)+length+1 := by
        refine stored.trans ?_
        gcongr
      simp only [compileFormula] at output ⊢
      rw [countShape]
      simp only [List.length_cons]
      nlinarith

theorem compileFormula_cells {n : Nat} (width : Nat) (rows : List Row)
    (valid : ∀ row ∈ rows, Table.RowValid width row) (formula : CNFFormula n) :
    (compileFormula rows formula).cells ≤ formulaBudget width rows.length formula.length (Extract.literalCount formula) :=
  compileFormula_ceiling width rows valid formula _ _ (Nat.le_refl _) (Nat.le_refl _)

/-- The table-to-list copy occurs once, before compiling any original literal. -/
def compile {n : Nat} (table : Array Row) (formula : CNFFormula n) : Counted Formula :=
  let shared := table.toList
  let output := compileFormula shared formula
  ⟨output.value,2*rowsCells shared+2*table.size+3+output.cells⟩

theorem compile_value {n : Nat} (table : Array Row) (formula : CNFFormula n) :
    (compile table formula).value = AffineClauses.compile table formula := compileFormula_value table formula

def compileBudget (width size length literals : Nat) : Nat :=
  2*size*(width+2)+2*size+3+formulaBudget width size length literals

theorem compile_cells {n : Nat} (width : Nat) (table : Array Row) (valid : Table.Valid width table)
    (formula : CNFFormula n) :
    (compile table formula).cells ≤ compileBudget width table.size formula.length (Extract.literalCount formula) := by
  have source := CapacityMatching.RowCost.table_storage width table valid
  have output := compileFormula_cells width table.toList valid formula
  simp only [Array.length_toList] at output
  simp only [compile,compileBudget]
  nlinarith

theorem growth_clean (formula : Formula) : growth (clean formula) ≤ growth formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases truth : tautology clause with
      | false =>
          have shape : clean (clause::rest) = clause::clean rest := by simp [clean,truth]
          rw [shape]
          simp only [growth,List.map_cons,List.prod_cons] at ih ⊢
          gcongr
      | true =>
          have shape : clean (clause::rest) = clean rest := by simp [clean,truth]
          rw [shape]
          simp only [growth,List.map_cons,List.prod_cons] at ih ⊢
          refine ih.trans ?_
          rw [Nat.add_mul,Nat.one_mul]
          omega

theorem generate_length (n : Nat) (formula : Formula) (inside : Within n formula) :
    (generate n formula).value.length ≤ growth formula := by
  have length := run_length n (clean formula) (clean_within n formula inside) [[]] (by
    intro basis member
    have same : basis=[] := List.mem_singleton.mp member
    subst basis
    exact ⟨triangular_nil,by simp [RowsWithin]⟩)
  simp only [List.length_singleton,Nat.one_mul] at length
  change (run n (cleanRun formula).value [[]]).value.length ≤ _
  rw [cleanRun_value]
  exact length.trans (growth_clean formula)

theorem generate_storage (n : Nat) (formula : Formula) (inside : Within n formula) :
    storage (generate n formula).value ≤ growth formula*cellBound n :=
  (storage_bound n _ (generate_valid n formula inside)).trans
    (Nat.mul_le_mul_right _ (generate_length n formula inside))

theorem coordinates_valid_n (n : Nat) (basis : List Row) : Table.Valid n (Table.coordinates n basis) := by
  intro row member
  have good := Table.coordinates_valid n basis row member
  exact ⟨good.1,fun i present => (good.2 i present).trans_le (Table.freeWidth_le n basis)⟩

/-- One generated coordinate table is shared by all original literals. -/
def coordinateCompile {n : Nat} (basis : List Row) (formula : CNFFormula n) : Counted Formula :=
  let table := Table.coordinates n basis
  let compiled := compile table formula
  ⟨compiled.value,AffineCollect.coordinateWork n basis+compiled.cells+
    2*AffineCollect.tableSize table+2*formulaSize compiled.value+5⟩

theorem coordinateCompile_value {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (coordinateCompile basis formula).value = AffineClauses.compile (Table.coordinates n basis) formula :=
  compile_value _ formula

theorem coordinateCompile_length {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (coordinateCompile basis formula).value.length = formula.length := compileFormula_length _ formula

theorem coordinateCompile_rows {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    rowCount (coordinateCompile basis formula).value = Extract.literalCount formula := compileFormula_rows _ formula

theorem coordinateCompile_terms {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    termCount (coordinateCompile basis formula).value ≤ Extract.literalCount formula*n :=
  compileFormula_terms n _ (coordinates_valid_n n basis) formula

theorem coordinateCompile_storage {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    formulaSize (coordinateCompile basis formula).value ≤ Extract.literalCount formula*(n+2)+formula.length+1 :=
  compileFormula_storage n _ (coordinates_valid_n n basis) formula

theorem coordinateCompile_within {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    Within (freeIndices n basis).length (coordinateCompile basis formula).value := by
  rw [coordinateCompile_value]
  exact AffineClauses.compile_within _ _ (Table.coordinates_valid n basis) formula

def coordinateCompileBudget (n length literals : Nat) : Nat :=
  AffineCollect.Cost.coordinateBudget n+compileBudget n n length literals+
    2*cellBound n+2*(literals*(n+2)+length+1)+5

theorem coordinateCompile_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) :
    (coordinateCompile basis formula).cells ≤ coordinateCompileBudget n formula.length (Extract.literalCount formula) := by
  have source := AffineCollect.Cost.coordinate_visits n basis valid
  have compiled := compile_cells n (Table.coordinates n basis) (coordinates_valid_n n basis) formula
  rw [Table.coordinates_size] at compiled
  have stored := AffineCollect.Cost.coordinate_size n basis
  have output := coordinateCompile_storage basis formula
  change formulaSize (compile (Table.coordinates n basis) formula).value ≤ _ at output
  simp only [coordinateCompile,coordinateCompileBudget]
  omega

/-- Compilation and exact universal-clause cleanup consume the same generated table. -/
def prepare {n : Nat} (basis : List Row) (formula : CNFFormula n) : Counted Formula :=
  let compiled := coordinateCompile basis formula
  let cleaned := cleanRun compiled.value
  ⟨cleaned.value,compiled.cells+cleaned.visits+2*formulaSize compiled.value+2*formulaSize cleaned.value+5⟩

theorem prepare_value {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (prepare basis formula).value = clean (AffineClauses.compile (Table.coordinates n basis) formula) := by
  simp only [prepare,cleanRun_value,coordinateCompile_value]

theorem prepare_within {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    Within (freeIndices n basis).length (prepare basis formula).value := by
  rw [prepare_value]
  exact clean_within _ _ (AffineClauses.compile_within _ _ (Table.coordinates_valid n basis) formula)

theorem prepare_storage {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    formulaSize (prepare basis formula).value ≤ Extract.literalCount formula*(n+2)+formula.length+1 := by
  change formulaSize (cleanRun (coordinateCompile basis formula).value).value ≤ _
  rw [cleanRun_value]
  exact (clean_size _).trans (coordinateCompile_storage basis formula)

theorem cleanBudget_mono_terms (n length rows small large : Nat) (bound : small ≤ large) :
    cleanBudget n length rows small ≤ cleanBudget n length rows large := by
  unfold cleanBudget
  gcongr

def prepareBudget (n length literals : Nat) : Nat :=
  coordinateCompileBudget n length literals+cleanBudget n length literals (literals*n)+
    4*(literals*(n+2)+length+1)+5

theorem prepare_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) :
    (prepare basis formula).cells ≤ prepareBudget n formula.length (Extract.literalCount formula) := by
  have compiled := coordinateCompile_cells basis valid formula
  have withinN : Within n (coordinateCompile basis formula).value := by
    rw [coordinateCompile_value]
    exact AffineClauses.compile_within _ _ (coordinates_valid_n n basis) formula
  have cleaned := cleanRun_visits n (coordinateCompile basis formula).value withinN
  rw [coordinateCompile_length,coordinateCompile_rows] at cleaned
  have cleanedBound := cleanBudget_mono_terms n formula.length (Extract.literalCount formula) _ _
    (coordinateCompile_terms basis formula)
  have inputSize := coordinateCompile_storage basis formula
  have outputSize := prepare_storage basis formula
  change formulaSize (cleanRun (coordinateCompile basis formula).value).value ≤ _ at outputSize
  simp only [prepare,prepareBudget]
  omega

theorem prepare_read {n : Nat} (basis : List Row) (formula : CNFFormula n) (assignment : Nat → Bool) :
    formulaRead (prepare basis formula).value assignment =
      CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) assignment) := by
  rw [prepare_value,clean_read,AffineClauses.compile_read]

theorem prepare_parameter_read {n : Nat} (basis : List Row) (inside : RowsWithin n basis)
    (formula : CNFFormula n) (parameters : Assignment (freeIndices n basis).length) :
    formulaRead (prepare basis formula).value (extendAssignment parameters) =
      CNFFormula.eval formula (extendAssignment (parameterLift n basis parameters)) := by
  rw [prepare_value,clean_read]
  have bounded := AffineClauses.compile_within _ _ (Table.coordinates_valid n basis) formula
  exact (AffineClauses.generate_read _ _ bounded _).symm.trans
    (AffineClauses.coordinate_read formula basis inside parameters)

end SaturationMonoid.ComplexityProjection.SATSource.AffineClauses.Cost

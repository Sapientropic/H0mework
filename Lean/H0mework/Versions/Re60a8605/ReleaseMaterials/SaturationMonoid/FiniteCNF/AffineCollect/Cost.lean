import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCollect.Core

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineCollect.Cost

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineCarrier (Cells Valid Separated read storage cellSize)
open InterferenceProgram

theorem rows_size (rows : List Row) : CapacityMatching.RowCost.rowsCells rows = Gates.rowTerms rows+2*rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowCells,
        Gates.rowTerms,List.map_cons,List.sum_cons,List.length_cons] at *
      omega

theorem table_size (table : Array Row) : tableSize table = Gates.rowTerms table.toList+2*table.size+1 := by
  simp only [tableSize,rows_size,Array.length_toList]

theorem coordinate_size (n : Nat) (basis : List Row) : tableSize (Table.coordinates n basis) ≤ AffineCarrier.Cost.cellBound n := by
  have bound := Table.coordinates_storage_quadratic n basis
  rw [table_size,Table.coordinates_size]
  unfold AffineCarrier.Cost.cellBound
  nlinarith

def coordinateBudget (n : Nat) : Nat :=
  10*(n+1)^4+8*(n+n+AffineCarrier.Cost.cellBound n+1)*(AffineCarrier.Cost.cellBound n+1)+
    2*AffineCarrier.Cost.cellBound n+3

theorem coordinate_visits (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    coordinateWork n basis ≤ coordinateBudget n := by
  have source := Table.coordinatesVisits_polynomial n basis valid.1 valid.2
  have rank := basis_length_le n basis valid.1 valid.2
  have stored := AffineCarrier.Cost.cell_size n basis valid.1 valid.2
  have measured := (AffineCarrier.Cost.row_measures basis).2
  have terms : Gates.rowTerms basis ≤ AffineCarrier.Cost.cellBound n := by
    unfold cellSize at stored
    omega
  unfold coordinateWork coordinateBudget
  gcongr

def sourceSize (n : Nat) : Nat := n*(2*n+3)+1

theorem source_size (n : Nat) (left right : List Row) : tableSize (BranchImage.source n left right) ≤ sourceSize n := by
  have bound := BranchImage.source_storage n left right
  rw [table_size,BranchImage.source_size]
  unfold sourceSize
  nlinarith

def imageBudget (n : Nat) : Nat :=
  (n*(2*n+1)+n)*(2*((2*n+1)+n)+5)+n*((2*n+1)*AtomImage.stepBudget (2*n+1) n+n+11)+2

def kernelBudget (n : Nat) : Nat := n*n*(2*n+5)+n*(EliminateCost.insertCellBudget n+1)+1

theorem kernel_visits (n : Nat) (left right : List Row) :
    (EliminateCost.run (BranchImage.common n left right)).cells ≤ kernelBudget n := by
  let kernel := BranchImage.common n left right
  have inside := BranchImage.common_within n left right
  have count := BranchImage.common_length n left right
  have generated := AtomImage.generate_valid (2*n+1) (BranchImage.source n left right) (BranchImage.source_within n left right)
  have valid : Table.Valid n kernel.toArray := by
    intro row member
    have typed := generated.2 row member
    simpa only [BranchImage.source_size] using typed
  have terms := Table.rowTerms_bound n kernel.toArray valid
  simp only [List.size_toArray] at terms
  have bound := EliminateCost.run_cells n kernel inside
  change kernel.length ≤ n at count
  have termBound : Gates.rowTerms kernel ≤ n*n := terms.trans (by gcongr)
  apply bound.trans
  unfold kernelBudget
  gcongr

def checkerBudget (n : Nat) : Nat := n*(n*(Union.pairBudget n+2)+3)+1

def mergeBudget (n : Nat) : Nat :=
  2*coordinateBudget n+
    (n+1)*(8*(AffineCarrier.Cost.cellBound n+AffineCarrier.Cost.cellBound n+sourceSize n)+8)+
    (imageBudget n+1)*(8*imageWorkspace n+8)+
    (kernelBudget n+checkerBudget n+2)*(8*AffineCarrier.Cost.cellBound n+8)+
    2*(3*AffineCarrier.Cost.cellBound n+1)+12

theorem merge_visits (n : Nat) (left right : List Row)
    (leftValid : Triangular left ∧ RowsWithin n left) (rightValid : Triangular right ∧ RowsWithin n right) :
    (merge n left right).visits ≤ mergeBudget n := by
  have leftCost := coordinate_visits n left leftValid
  have rightCost := coordinate_visits n right rightValid
  have leftTable := coordinate_size n left
  have rightTable := coordinate_size n right
  have source := source_size n left right
  have imageCost := BranchImage.common_visits n left right
  change AtomImage.generateVisits (BranchImage.source n left right) ≤ imageBudget n at imageCost
  have gaussian := kernel_visits n left right
  have checked := Union.merge_checkCells n left right leftValid.2 leftValid.1 rightValid.2 rightValid.1
  change (Union.check (eliminate (BranchImage.common n left right)) left right).cells ≤ checkerBudget n at checked
  have leftSize := AffineCarrier.Cost.cell_size n left leftValid.1 leftValid.2
  have rightSize := AffineCarrier.Cost.cell_size n right rightValid.1 rightValid.2
  have invariants := BranchImage.join_invariants n (.basis left) (.basis right)
    leftValid.2 leftValid.1 rightValid.2 rightValid.1
  have resultSize := AffineCarrier.Cost.result_size n _ invariants.2 invariants.1
  change AffineCarrier.resultSize (eliminate (BranchImage.common n left right)) ≤ AffineCarrier.Cost.cellBound n+1 at resultSize
  simp only [merge,EliminateCost.run_result]
  change coordinateWork n left+coordinateWork n right+
    (n+1)*(8*(tableSize (Table.coordinates n left)+tableSize (Table.coordinates n right)+
      tableSize (BranchImage.source n left right))+8)+
    (AtomImage.generateVisits (BranchImage.source n left right)+1)*(8*imageWorkspace n+8)+
    ((EliminateCost.run (BranchImage.common n left right)).cells+
      (Union.check (eliminate (BranchImage.common n left right)) left right).cells+2)*(8*AffineCarrier.Cost.cellBound n+8)+
    2*(cellSize left+cellSize right+AffineCarrier.resultSize (eliminate (BranchImage.common n left right)))+12 ≤ _
  unfold mergeBudget
  have sizes : cellSize left+cellSize right+AffineCarrier.resultSize (eliminate (BranchImage.common n left right)) ≤
      3*AffineCarrier.Cost.cellBound n+1 := by omega
  calc
    _ ≤ coordinateBudget n+coordinateBudget n+
        (n+1)*(8*(AffineCarrier.Cost.cellBound n+AffineCarrier.Cost.cellBound n+sourceSize n)+8)+
        (imageBudget n+1)*(8*imageWorkspace n+8)+
        (kernelBudget n+checkerBudget n+2)*(8*AffineCarrier.Cost.cellBound n+8)+
        2*(3*AffineCarrier.Cost.cellBound n+1)+12 := by gcongr
    _ = _ := by ring

theorem merge_checks_bound (n : Nat) (left right : List Row)
    (leftValid : Triangular left ∧ RowsWithin n left) (rightValid : Triangular right ∧ RowsWithin n right) :
    (merge n left right).checks ≤ n*n := by
  rw [merge_checks]
  exact Union.merge_calls n left right leftValid.2 leftValid.1 rightValid.2 rightValid.1

theorem tryLeft_attempts (n : Nat) (left : List Row) (rest : Cells) : (tryLeft n left rest).attempts ≤ rest.length := by
  induction rest with
  | nil => rfl
  | cons right rest ih =>
      cases tested : (merge n left right).value <;> simp only [tryLeft,tested,List.length_cons] <;> omega

theorem scan_attempts (n : Nat) (cells : Cells) : (scan n cells).attempts ≤ cells.length*cells.length := by
  induction cells with
  | nil => simp [scan]
  | cons left rest ih =>
      have first := tryLeft_attempts n left rest
      cases found : (tryLeft n left rest).answer <;> simp only [scan,found,List.length_cons] <;> nlinarith

theorem tryLeft_answerSize (n : Nat) (left : List Row) (rest : Cells)
    (leftValid : Triangular left ∧ RowsWithin n left) (restValid : Valid n rest) :
    answerSize (tryLeft n left rest).answer ≤ rest.length*AffineCarrier.Cost.cellBound n+1 := by
  cases found : (tryLeft n left rest).answer with
  | none => simp [answerSize]
  | some output =>
      have spec := tryLeft_spec n left rest output leftValid restValid found
      have bound := AffineCarrier.Cost.storage_bound n output spec.1
      simp only [answerSize]
      rw [spec.2.1] at bound
      omega

theorem scan_answerSize (n : Nat) (cells : Cells) (valid : Valid n cells) :
    answerSize (scan n cells).answer ≤ cells.length*AffineCarrier.Cost.cellBound n+1 := by
  cases found : (scan n cells).answer with
  | none => simp [answerSize]
  | some output =>
      have spec := scan_spec n cells output valid found
      have bound := AffineCarrier.Cost.storage_bound n output spec.1
      have size : output.length ≤ cells.length := by omega
      have total := bound.trans (Nat.mul_le_mul_right _ size)
      simp only [answerSize]
      omega

def leftBudget (n count : Nat) : Nat := count*(mergeBudget n+2*(count+1)*AffineCarrier.Cost.cellBound n+9)+1

theorem tryLeft_visits (n : Nat) (left : List Row) (rest : Cells)
    (leftValid : Triangular left ∧ RowsWithin n left) (restValid : Valid n rest) :
    (tryLeft n left rest).visits ≤ leftBudget n rest.length := by
  induction rest with
  | nil => simp [tryLeft,leftBudget]
  | cons right rest ih =>
      have rightValid := restValid right (by simp)
      have tailValid : Valid n rest := fun other member => restValid other (by simp [member])
      have proposal := merge_visits n left right leftValid rightValid
      have original := AffineCarrier.Cost.cell_size n right rightValid.1 rightValid.2
      have restSize := AffineCarrier.Cost.storage_bound n rest tailValid
      have tail := ih tailValid
      have tailSize := tryLeft_answerSize n left rest leftValid tailValid
      cases tested : (merge n left right).value with
      | none =>
          simp only [tryLeft,tested,leftBudget,List.length_cons] at tail ⊢
          nlinarith
      | some current =>
          have valid := merge_valid n left right current leftValid rightValid tested
          have size := AffineCarrier.Cost.cell_size n current valid.1 valid.2
          simp only [tryLeft,tested,leftBudget,List.length_cons]
          nlinarith

def scanBudget (n count : Nat) : Nat :=
  count*(leftBudget n count+2*(count+1)*AffineCarrier.Cost.cellBound n+9)+1

theorem scan_visits (n : Nat) (cells : Cells) (valid : Valid n cells) : (scan n cells).visits ≤ scanBudget n cells.length := by
  induction cells with
  | nil => simp [scan,scanBudget]
  | cons left rest ih =>
      have leftValid := valid left (by simp)
      have restValid : Valid n rest := fun other member => valid other (by simp [member])
      have first := tryLeft_visits n left rest leftValid restValid
      have firstBound : (tryLeft n left rest).visits ≤ leftBudget n (rest.length+1) := by
        apply first.trans
        unfold leftBudget
        gcongr <;> omega
      have tail := ih restValid
      have leftSize := AffineCarrier.Cost.cell_size n left leftValid.1 leftValid.2
      have tailSize := scan_answerSize n rest restValid
      cases found : (tryLeft n left rest).answer with
      | none =>
          have monotone : scanBudget n rest.length ≤ rest.length*(leftBudget n (rest.length+1)+
              2*(rest.length+2)*AffineCarrier.Cost.cellBound n+9)+1 := by
            unfold scanBudget leftBudget
            gcongr <;> omega
          simp only [scan,found,scanBudget,List.length_cons]
          nlinarith
      | some output =>
          have spec := tryLeft_spec n left rest output leftValid restValid found
          have outputSize := AffineCarrier.Cost.storage_bound n output spec.1
          rw [spec.2.1] at outputSize
          simp only [scan,found,scanBudget,List.length_cons]
          nlinarith

theorem scanBudget_mono (n small large : Nat) (bound : small ≤ large) : scanBudget n small ≤ scanBudget n large := by
  unfold scanBudget leftBudget
  gcongr

theorem iterate_merges (n fuel : Nat) (cells : Cells) (valid : Valid n cells) :
    (iterate n fuel cells).value.length+(iterate n fuel cells).merges = cells.length := by
  induction fuel generalizing cells with
  | zero => simp [iterate]
  | succ fuel ih =>
      cases first : (scan n cells).answer with
      | none => simp [iterate,first]
      | some next =>
          have spec := scan_spec n cells next valid first
          have tail := ih next spec.1
          simp only [iterate,first]
          omega

theorem iterate_attempts (n fuel ceiling : Nat) (cells : Cells) (valid : Valid n cells) (size : cells.length ≤ ceiling) :
    (iterate n fuel cells).attempts ≤ fuel*ceiling*ceiling := by
  induction fuel generalizing cells with
  | zero => simp [iterate]
  | succ fuel ih =>
      have first := scan_attempts n cells
      have bounded : (scan n cells).attempts ≤ ceiling*ceiling := first.trans (by gcongr)
      cases found : (scan n cells).answer with
      | none => simp only [iterate,found]; nlinarith
      | some next =>
          have spec := scan_spec n cells next valid found
          have tail := ih next spec.1 (by omega)
          simp only [iterate,found]
          nlinarith

theorem iterate_visits (n fuel ceiling : Nat) (cells : Cells) (valid : Valid n cells) (size : cells.length ≤ ceiling) :
    (iterate n fuel cells).visits ≤ fuel*(scanBudget n ceiling+2*ceiling*AffineCarrier.Cost.cellBound n+5)+
      2*ceiling*AffineCarrier.Cost.cellBound n+3 := by
  induction fuel generalizing cells with
  | zero =>
      have stored := (AffineCarrier.Cost.storage_bound n cells valid).trans (Nat.mul_le_mul_right _ size)
      simp only [iterate]
      nlinarith
  | succ fuel ih =>
      have first := (scan_visits n cells valid).trans (scanBudget_mono n _ ceiling size)
      cases found : (scan n cells).answer with
      | none =>
          have stored := (AffineCarrier.Cost.storage_bound n cells valid).trans (Nat.mul_le_mul_right _ size)
          simp only [iterate,found]
          nlinarith
      | some next =>
          have spec := scan_spec n cells next valid found
          have tail := ih next spec.1 (by omega)
          simp only [iterate,found]
          nlinarith

def collectBudget (n count : Nat) : Nat :=
  count*(scanBudget n count+2*count*AffineCarrier.Cost.cellBound n+5)+2*count*AffineCarrier.Cost.cellBound n+3

theorem collect_merges (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (collect n cells).value.length+(collect n cells).merges = cells.length := iterate_merges n cells.length cells valid

theorem collect_attempts (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (collect n cells).attempts ≤ cells.length^3 := by
  have bound := iterate_attempts n cells.length cells.length cells valid (Nat.le_refl _)
  simpa only [collect,pow_succ,pow_zero,Nat.one_mul] using bound

theorem collect_visits (n : Nat) (cells : Cells) (valid : Valid n cells) :
    (collect n cells).visits ≤ collectBudget n cells.length := iterate_visits n cells.length cells.length cells valid (Nat.le_refl _)

theorem collectBudget_mono (n small large : Nat) (bound : small ≤ large) : collectBudget n small ≤ collectBudget n large := by
  unfold collectBudget scanBudget leftBudget
  gcongr

theorem run_length {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells) :
    (run formula cells).value.length ≤ cells.length*AffineCarrier.Cost.growth formula := by
  induction formula generalizing cells with
  | nil => simp [run,AffineCarrier.Cost.growth]
  | cons clause rest ih =>
      have cutValid := AffineCarrier.clauseAction_valid clause cells valid
      have first := AffineCarrier.Cost.action_length clause cells
      have shared := collect_length n _ cutValid
      have next := ih _ (collect_valid n _ cutValid)
      simp only [run,AffineCarrier.Cost.growth,List.map_cons,List.prod_cons]
      exact next.trans (by
        change _ ≤ cells.length*((clause.length+1)*AffineCarrier.Cost.growth rest)
        have bound := shared.trans first
        nlinarith)

def runBudget (n : Nat) {width : Nat} : CNFFormula width → Nat → Nat
  | [],count => 2*count*AffineCarrier.Cost.cellBound n+1
  | clause::rest,count =>
      AffineCarrier.Cost.actionBudget n count clause.length+collectBudget n (count*(clause.length+1))+
        runBudget n rest (count*(clause.length+1))+3

theorem runBudget_mono (n : Nat) {width : Nat} (formula : CNFFormula width) (small large : Nat) (bound : small ≤ large) :
    runBudget n formula small ≤ runBudget n formula large := by
  induction formula generalizing small large with
  | nil => simp only [runBudget]; gcongr
  | cons clause rest ih =>
      have next := ih (small*(clause.length+1)) (large*(clause.length+1)) (by gcongr)
      have shared := collectBudget_mono n (small*(clause.length+1)) (large*(clause.length+1)) (by gcongr)
      simp only [runBudget,AffineCarrier.Cost.actionBudget]
      gcongr

theorem run_visits {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells) :
    (run formula cells).visits ≤ runBudget n formula cells.length := by
  induction formula generalizing cells with
  | nil =>
      have stored := AffineCarrier.Cost.storage_bound n cells valid
      simp only [run,runBudget]
      nlinarith
  | cons clause rest ih =>
      have cutValid := AffineCarrier.clauseAction_valid clause cells valid
      have cutCost := AffineCarrier.Cost.action_visits clause cells valid
      have cutSize := AffineCarrier.Cost.action_length clause cells
      have sharedCost := collect_visits n _ cutValid
      have sharedBound := collectBudget_mono n _ _ cutSize
      have sharedValid := collect_valid n _ cutValid
      have sharedSize := (collect_length n _ cutValid).trans cutSize
      have tail := ih _ sharedValid
      have tailBound := runBudget_mono n rest _ _ sharedSize
      simp only [run,runBudget]
      omega

theorem generate_length {n : Nat} (formula : CNFFormula n) :
    (generate formula).value.length ≤ AffineCarrier.Cost.growth formula := by
  have bound := run_length formula (AffineCarrier.seed formula).value (AffineCarrier.seed_valid formula)
  exact bound.trans (by simpa using Nat.mul_le_mul_right (AffineCarrier.Cost.growth formula) (AffineCarrier.Cost.seed_length formula))

theorem generate_storage {n : Nat} (formula : CNFFormula n) :
    storage (generate formula).value ≤ AffineCarrier.Cost.growth formula*AffineCarrier.Cost.cellBound n :=
  (AffineCarrier.Cost.storage_bound n _ (generate_valid formula)).trans (Nat.mul_le_mul_right _ (generate_length formula))

theorem generate_visits {n : Nat} (formula : CNFFormula n) :
    (generate formula).visits ≤ AffineCarrier.Cost.seedBudget n formula.length (Extract.literalCount formula)+runBudget n formula 1+2 := by
  have initial := AffineCarrier.Cost.seed_visits formula
  have final := run_visits formula (AffineCarrier.seed formula).value (AffineCarrier.seed_valid formula)
  have bound := runBudget_mono n formula _ 1 (AffineCarrier.Cost.seed_length formula)
  change (AffineCarrier.seed formula).visits+(run formula (AffineCarrier.seed formula).value).visits+2 ≤ _
  omega

end SaturationMonoid.ComplexityProjection.SATSource.AffineCollect.Cost

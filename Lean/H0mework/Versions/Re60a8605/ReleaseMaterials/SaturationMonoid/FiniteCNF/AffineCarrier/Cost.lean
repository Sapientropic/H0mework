import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineCarrier.Core

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineCarrier.Cost

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram

def cellBound (n : Nat) : Nat := n*(n+2)+1

theorem cell_size (n : Nat) (basis : List Row) (triangular : Triangular basis) (inside : RowsWithin n basis) :
    cellSize basis ≤ cellBound n := by
  have rank := basis_length_le n basis triangular inside
  have each : ∀ rows : List Row, (∀ row ∈ rows, Table.RowValid n row) →
      CapacityMatching.RowCost.rowsCells rows ≤ rows.length*(n+2) := by
    intro rows valid
    induction rows with
    | nil => simp
    | cons row rest ih =>
        have first := Table.row_length_le n row (valid row (by simp))
        have tail := ih (fun other member => valid other (by simp [member]))
        simp only [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowCells,List.length_cons]
        nlinarith
  have total := each basis (fun row member => ⟨triangular.1 row member,inside row member⟩)
  unfold cellSize cellBound
  nlinarith

theorem storage_bound (n : Nat) (cells : Cells) (valid : Valid n cells) : storage cells ≤ cells.length*cellBound n := by
  induction cells with
  | nil => simp [storage]
  | cons basis rest ih =>
      have first := cell_size n basis (valid basis (by simp)).1 (valid basis (by simp)).2
      have tail := ih (fun other member => valid other (by simp [member]))
      simp only [storage,List.map_cons,List.sum_cons,List.length_cons] at *
      nlinarith

theorem result_size (n : Nat) (result : Result) (triangular : result.triangular) (inside : result.within n) :
    resultSize result ≤ cellBound n+1 := by
  cases result with
  | contradiction => simp [resultSize]
  | basis basis => exact Nat.add_le_add_right (cell_size n basis triangular inside) 1

theorem pack_length (result : Result) : (pack result).value.length ≤ 1 := by cases result <;> simp [pack]

theorem pack_visits (n : Nat) (result : Result) (triangular : result.triangular) (inside : result.within n) :
    (pack result).visits ≤ 2*cellBound n+5 := by
  have bound := result_size n result triangular inside
  simp only [pack]
  omega

def unitInsert (n : Nat) : Nat := 2*n+5+EliminateCost.insertCellBudget n

theorem unit_visits {n : Nat} (literal : CNFLiteral n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (EliminateCost.insert result (trueRow literal)).cells ≤ unitInsert n ∧
    (EliminateCost.insert result (Propagation.badLiteral literal)).cells ≤ unitInsert n := by
  constructor
  · simpa only [trueRow,List.length_cons,List.length_nil,Nat.zero_add,Nat.one_mul,unitInsert] using
      EliminateCost.insert_cells n result triangular inside (trueRow literal) (trueRow_within literal)
  · simpa only [Propagation.badLiteral,List.length_cons,List.length_nil,Nat.zero_add,Nat.one_mul,unitInsert] using
      EliminateCost.insert_cells n result triangular inside (Propagation.badLiteral literal) (Propagation.badLiteral_within literal)

theorem branches_length {n : Nat} (clause : CNFClause n) (result : Result) :
    (branches clause result).value.length ≤ clause.length := by
  induction clause generalizing result with
  | nil => rfl
  | cons literal rest ih =>
      have first := pack_length (EliminateCost.insert result (trueRow literal)).result
      have tail := ih (EliminateCost.insert result (Propagation.badLiteral literal)).result
      simp only [branches,append,List.length_append,List.length_cons]
      omega

theorem branches_inserts {n : Nat} (clause : CNFClause n) (result : Result) :
    (branches clause result).inserts = 2*clause.length := by
  induction clause generalizing result with
  | nil => rfl
  | cons literal rest ih => simp only [branches,append,pack,ih,List.length_cons]; omega

theorem branches_xors {n : Nat} (clause : CNFClause n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (branches clause result).xors ≤ 2*clause.length*n := by
  induction clause generalizing result with
  | nil => simp [branches]
  | cons literal rest ih =>
      have yes := EliminateCost.insert_xors n result triangular inside (trueRow literal)
      have no := EliminateCost.insert_xors n result triangular inside (Propagation.badLiteral literal)
      have valid := insert_valid n result triangular inside (Propagation.badLiteral literal) (Propagation.badLiteral_within literal)
      have tail := ih _ valid.1 valid.2
      simp only [branches,append,pack,List.length_cons]
      nlinarith

def branchesBudget (n length : Nat) : Nat :=
  length*(2*unitInsert n+(2*length+12)*cellBound n+40)+1

theorem branches_visits {n : Nat} (clause : CNFClause n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (branches clause result).visits ≤ branchesBudget n clause.length := by
  induction clause generalizing result with
  | nil => simp [branches,branchesBudget]
  | cons literal rest ih =>
      let yes := (EliminateCost.insert result (trueRow literal)).result
      let no := (EliminateCost.insert result (Propagation.badLiteral literal)).result
      have yesValid := insert_valid n result triangular inside (trueRow literal) (trueRow_within literal)
      have noValid := insert_valid n result triangular inside (Propagation.badLiteral literal) (Propagation.badLiteral_within literal)
      obtain ⟨yesCost,noCost⟩ := unit_visits literal result triangular inside
      have packed := pack_visits n yes yesValid.1 yesValid.2
      have tail := ih no noValid.1 noValid.2
      have yesStorage : storage (pack yes).value ≤ cellBound n := by
        have bound := storage_bound n _ (pack_valid n yes yesValid.1 yesValid.2)
        exact bound.trans (by simpa using Nat.mul_le_mul_right (cellBound n) (pack_length yes))
      have noStorage : storage (branches rest no).value ≤ rest.length*cellBound n :=
        (storage_bound n _ (branches_valid rest no noValid.1 noValid.2)).trans
          (Nat.mul_le_mul_right _ (branches_length rest no))
      have initialSize := result_size n result triangular inside
      have yesSize := result_size n yes yesValid.1 yesValid.2
      have noSize := result_size n no noValid.1 noValid.2
      change (pack yes).visits+(branches rest no).visits+2*storage (pack yes).value+
        2*storage (branches rest no).value+5+
        (EliminateCost.insert result (trueRow literal)).cells+(EliminateCost.insert result (Propagation.badLiteral literal)).cells+
        2*(resultSize result+resultSize yes+resultSize no)+16 ≤ _
      simp only [branchesBudget,List.length_cons] at tail ⊢
      nlinarith

theorem bad_inside {n : Nat} (clause : CNFClause n) : RowsWithin n (clause.map Propagation.badLiteral) := by
  intro row member
  obtain ⟨literal,_,rfl⟩ := List.mem_map.mp member
  exact Propagation.badLiteral_within literal

theorem bad_terms {n : Nat} (clause : CNFClause n) : Gates.rowTerms (clause.map Propagation.badLiteral) = clause.length := by
  simp [Gates.rowTerms,Propagation.badLiteral,List.map_map,Function.comp_def]

theorem checked_valid {n : Nat} (clause : CNFClause n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result.triangular ∧
      (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result.within n := by
  rw [EliminateCost.runFrom_result]
  exact ⟨eliminateFrom_triangular result triangular _,eliminateFrom_within n result inside _ (bad_inside clause)⟩

theorem checked_visits {n : Nat} (clause : CNFClause n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) :
    (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).cells ≤ clause.length*(unitInsert n+1)+1 := by
  have bound := EliminateCost.runFrom_cells n result triangular inside _ (bad_inside clause)
  rw [bad_terms,List.length_map] at bound
  convert bound using 1
  unfold unitInsert
  ring

theorem cut_length {n : Nat} (clause : CNFClause n) (result : Result) :
    (cut clause result).value.length ≤ clause.length+1 := by
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result with
  | contradiction => simpa only [cut,checked] using (pack_length result).trans (Nat.le_add_left 1 clause.length)
  | basis basis => simpa only [cut,checked] using (branches_length clause result).trans (Nat.le_succ _)

theorem cut_inserts {n : Nat} (clause : CNFClause n) (result : Result) : (cut clause result).inserts ≤ 3*clause.length := by
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result <;>
    simp only [cut,checked,pack,branches_inserts] <;> omega

theorem cut_xors {n : Nat} (clause : CNFClause n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) : (cut clause result).xors ≤ 3*clause.length*n := by
  have test := EliminateCost.runFrom_xors n result triangular inside _ (bad_inside clause)
  simp only [List.length_map] at test
  have splitCost := branches_xors clause result triangular inside
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result <;>
    simp only [cut,checked,pack] <;> nlinarith

def cutBudget (n length : Nat) : Nat :=
  branchesBudget n length+length*(unitInsert n+5)+6*cellBound n+15

theorem cut_visits {n : Nat} (clause : CNFClause n) (result : Result)
    (triangular : result.triangular) (inside : result.within n) : (cut clause result).visits ≤ cutBudget n clause.length := by
  have test := checked_visits clause result triangular inside
  have valid := checked_valid clause result triangular inside
  have beforeSize := result_size n result triangular inside
  have afterSize := result_size n _ valid.1 valid.2
  have packed := pack_visits n result triangular inside
  have divided := branches_visits clause result triangular inside
  cases checked : (EliminateCost.runFrom result (clause.map Propagation.badLiteral)).result <;>
    simp only [cut,checked,cutBudget] <;> simp only [checked] at afterSize <;> nlinarith

theorem action_length {n : Nat} (clause : CNFClause n) (cells : Cells) :
    (clauseAction clause cells).value.length ≤ cells.length*(clause.length+1) := by
  induction cells with
  | nil => simp [clauseAction]
  | cons basis rest ih =>
      have first := cut_length clause (.basis basis)
      simp only [clauseAction,append,List.length_append,List.length_cons]
      nlinarith

def actionBudget (n count length : Nat) : Nat :=
  count*(cutBudget n length+(count+1)*(length+1)*cellBound n+5)+1

theorem action_visits {n : Nat} (clause : CNFClause n) (cells : Cells) (valid : Valid n cells) :
    (clauseAction clause cells).visits ≤ actionBudget n cells.length clause.length := by
  induction cells with
  | nil => simp [clauseAction,actionBudget]
  | cons basis rest ih =>
      have headValid := valid basis (by simp)
      have tailValid : Valid n rest := fun other member => valid other (by simp [member])
      have first := cut_visits clause (.basis basis) headValid.1 headValid.2
      have tail := ih tailValid
      have firstSize : storage (cut clause (.basis basis)).value ≤ (clause.length+1)*cellBound n :=
        (storage_bound n _ (cut_valid clause (.basis basis) headValid.1 headValid.2)).trans
          (Nat.mul_le_mul_right _ (cut_length clause (.basis basis)))
      have tailSize : storage (clauseAction clause rest).value ≤ rest.length*(clause.length+1)*cellBound n :=
        (storage_bound n _ (clauseAction_valid clause rest tailValid)).trans (Nat.mul_le_mul_right _ (action_length clause rest))
      simp only [clauseAction,append,actionBudget,List.length_cons] at tail ⊢
      nlinarith

def growth {n : Nat} (formula : CNFFormula n) : Nat := (formula.map (fun clause => clause.length+1)).prod

theorem run_length {n : Nat} (formula : CNFFormula n) (cells : Cells) :
    (run formula cells).value.length ≤ cells.length*growth formula := by
  induction formula generalizing cells with
  | nil => simp [run,growth]
  | cons clause rest ih =>
      have next := ih (clauseAction clause cells).value
      have width := action_length clause cells
      simp only [run,growth,List.map_cons,List.prod_cons]
      exact next.trans (by change _ ≤ cells.length*((clause.length+1)*growth rest); nlinarith)

def runBudget (n : Nat) {width : Nat} : CNFFormula width → Nat → Nat
  | [], count => 2*count*cellBound n+1
  | clause::rest, count => actionBudget n count clause.length+runBudget n rest (count*(clause.length+1))+2

theorem runBudget_mono (n : Nat) {width : Nat} (formula : CNFFormula width) (small large : Nat) (bound : small ≤ large) :
    runBudget n formula small ≤ runBudget n formula large := by
  induction formula generalizing small large with
  | nil => simp only [runBudget]; gcongr
  | cons clause rest ih =>
      have next := ih (small*(clause.length+1)) (large*(clause.length+1)) (by gcongr)
      simp only [runBudget,actionBudget]
      gcongr

theorem run_visits {n : Nat} (formula : CNFFormula n) (cells : Cells) (valid : Valid n cells) :
    (run formula cells).visits ≤ runBudget n formula cells.length := by
  induction formula generalizing cells with
  | nil =>
      have bound := storage_bound n cells valid
      simp only [run,runBudget]
      nlinarith
  | cons clause rest ih =>
      have first := action_visits clause cells valid
      have tail := ih _ (clauseAction_valid clause cells valid)
      have grow := runBudget_mono n rest _ _ (action_length clause cells)
      simp only [run,runBudget]
      omega

theorem row_measures (rows : List Row) :
    rows.length ≤ CapacityMatching.RowCost.rowsCells rows ∧ Gates.rowTerms rows ≤ CapacityMatching.RowCost.rowsCells rows := by
  induction rows with
  | nil => simp [Gates.rowTerms]
  | cons row rest ih =>
      simp only [List.length_cons,CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowCells,
        Gates.rowTerms,List.map_cons,List.sum_cons] at *
      omega

def extractBudget (n clauses literals : Nat) : Nat :=
  clauses*(56*literals+40*clauses+42)+1+40*(clauses+1)*(n+1)^3

def seedBudget (n clauses literals : Nat) : Nat :=
  extractBudget n clauses literals+CapacityMatching.RowCost.prepareBudget n clauses literals+
    CapacityMatching.RowCost.prepareStorage n clauses literals*(unitInsert n+1)+6*cellBound n+18

theorem seed_length {n : Nat} (formula : CNFFormula n) : (seed formula).value.length ≤ 1 := by
  rw [seed_result]
  exact pack_length _

theorem seed_visits {n : Nat} (formula : CNFFormula n) :
    (seed formula).visits ≤ seedBudget n formula.length (Extract.literalCount formula) := by
  let first := EliminateCost.run (Extract.run formula).rows
  let extra := CapacityMatching.RowCost.prepare formula
  let last := EliminateCost.runFrom first.result extra.value
  have firstTriangular : first.result.triangular := by
    dsimp only [first]
    rw [EliminateCost.run_result]
    exact eliminate_triangular _
  have firstWithin : first.result.within n := by
    dsimp only [first]
    rw [EliminateCost.run_result]
    exact eliminate_within n _ (extract_rowsWithin formula)
  have extraWithin : RowsWithin n extra.value := by
    dsimp only [extra]
    rw [CapacityMatching.RowCost.prepare_value]
    exact CapacityMatching.SourceTight.prepare_within formula
  have lastTriangular : last.result.triangular := by
    dsimp only [last]
    rw [EliminateCost.runFrom_result]
    exact eliminateFrom_triangular _ firstTriangular _
  have lastWithin : last.result.within n := by
    dsimp only [last]
    rw [EliminateCost.runFrom_result]
    exact eliminateFrom_within n _ firstWithin _ extraWithin
  have firstCost := EliminateCost.fromFormula_cells formula
  change (Extract.run formula).visits+first.cells ≤ extractBudget n formula.length (Extract.literalCount formula) at firstCost
  have extraCost := CapacityMatching.RowCost.prepare_cells formula
  change extra.cells ≤ _ at extraCost
  have extraSize := CapacityMatching.RowCost.prepare_storage formula
  change CapacityMatching.RowCost.rowsCells extra.value ≤ _ at extraSize
  have extraLength := (row_measures extra.value).1.trans extraSize
  have extraTerms := (row_measures extra.value).2.trans extraSize
  have lastCost := EliminateCost.runFrom_cells n first.result firstTriangular firstWithin extra.value extraWithin
  have lastBound : last.cells ≤
      CapacityMatching.RowCost.prepareStorage n formula.length (Extract.literalCount formula)*(unitInsert n+1)+1 := by
    calc
      last.cells ≤ Gates.rowTerms extra.value*(2*n+5)+extra.value.length*(EliminateCost.insertCellBudget n+1)+1 := lastCost
      _ ≤ CapacityMatching.RowCost.prepareStorage n formula.length (Extract.literalCount formula)*(2*n+5)+
          CapacityMatching.RowCost.prepareStorage n formula.length (Extract.literalCount formula)*(EliminateCost.insertCellBudget n+1)+1 := by gcongr
      _ = _ := by unfold unitInsert; ring
  have firstSize := result_size n first.result firstTriangular firstWithin
  have lastSize := result_size n last.result lastTriangular lastWithin
  have packed := pack_visits n last.result lastTriangular lastWithin
  change (Extract.run formula).visits+first.cells+extra.cells+last.cells+(pack last.result).visits+
    2*(resultSize first.result+resultSize last.result)+8 ≤ _
  unfold seedBudget
  omega

theorem generate_length {n : Nat} (formula : CNFFormula n) : (generate formula).value.length ≤ growth formula := by
  have bound := run_length formula (seed formula).value
  exact bound.trans (by simpa using Nat.mul_le_mul_right (growth formula) (seed_length formula))

theorem generate_storage {n : Nat} (formula : CNFFormula n) : storage (generate formula).value ≤ growth formula*cellBound n :=
  (storage_bound n _ (generate_valid formula)).trans (Nat.mul_le_mul_right _ (generate_length formula))

/-- This is the bound for this actual carrier execution, with its clause-dependent growth explicit. -/
theorem generate_visits {n : Nat} (formula : CNFFormula n) :
    (generate formula).visits ≤ seedBudget n formula.length (Extract.literalCount formula)+runBudget n formula 1+2 := by
  have initial := seed_visits formula
  have final := run_visits formula (seed formula).value (seed_valid formula)
  have bound := runBudget_mono n formula _ 1 (seed_length formula)
  change (seed formula).visits+(run formula (seed formula).value).visits+2 ≤ _
  omega

end SaturationMonoid.ComplexityProjection.SATSource.AffineCarrier.Cost

import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.FeedbackCost
import Mathlib.Data.List.Sort

/-! Paired residual generation and a paid insertion-sort realization of the
    original canonical rows. Ledgers count source-record scans and payload
    copies; Nat bit operations and evaluating the counters have separate costs. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineAtomFeedbackCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowCells rowsCells)
open InterferenceProgram
abbrev Counted := CapacityMatching.SourceCost.Counted
abbrev Data := List (List Row)

def dataSize (source : Data) : Nat := rowsCells source.flatten+source.length+1

theorem dataSize_cons (rows : List Row) (rest : Data) :
    dataSize (rows::rest)=rowsCells rows+dataSize rest+1 := by
  simp only [dataSize,List.flatten_cons,CapacityMatching.RowCost.rowsCells_append,List.length_cons]
  omega

def orderedInsert (i : Nat) : List Nat → Counted (List Nat)
  | [] => ⟨[i],3⟩
  | j::rest =>
      if i ≤ j then ⟨i::j::rest,2*rest.length+7⟩
      else let tail := orderedInsert i rest
           ⟨j::tail.value,tail.cells+2*tail.value.length+4⟩

theorem orderedInsert_value (i : Nat) (vars : List Nat) :
    (orderedInsert i vars).value=List.orderedInsert (· ≤ ·) i vars := by
  induction vars with
  | nil => rfl
  | cons j rest ih => simp only [orderedInsert,List.orderedInsert]; split <;> simp_all

theorem orderedInsert_length (i : Nat) (vars : List Nat) :
    (orderedInsert i vars).value.length=vars.length+1 := by
  rw [orderedInsert_value]
  exact List.orderedInsert_length _ _ _

def insertionBudget (length : Nat) : Nat := (length+1)*(2*length+7)

theorem orderedInsert_cells (i : Nat) (vars : List Nat) :
    (orderedInsert i vars).cells ≤ insertionBudget vars.length := by
  induction vars with
  | nil => simp [orderedInsert,insertionBudget]
  | cons j rest ih =>
      simp only [orderedInsert,List.length_cons,orderedInsert_length]
      split <;> unfold insertionBudget at * <;> nlinarith

def sort : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | i::rest =>
      let tail := sort rest
      let added := orderedInsert i tail.value
      ⟨added.value,tail.cells+added.cells+2*(tail.value.length+added.value.length)+5⟩

theorem sort_value (vars : List Nat) : (sort vars).value=vars.mergeSort := by
  rw [List.mergeSort_eq_insertionSort (· ≤ ·)]
  induction vars with
  | nil => rfl
  | cons i rest ih => simp only [sort,orderedInsert_value,ih,List.insertionSort_cons]

theorem sort_length (vars : List Nat) : (sort vars).value.length=vars.length := by
  rw [sort_value]
  exact (List.mergeSort_perm vars _).length_eq

def sortBudget (length : Nat) : Nat := length*(insertionBudget length+4*length+7)+1

theorem sort_cells (vars : List Nat) : (sort vars).cells ≤ sortBudget vars.length := by
  induction vars with
  | nil => simp [sort,sortBudget]
  | cons i rest ih =>
      have inserted := orderedInsert_cells i (sort rest).value
      rw [sort_length] at inserted
      simp only [sort,sort_length,orderedInsert_length,List.length_cons]
      unfold sortBudget insertionBudget at *
      nlinarith

def canonical (row : Row) : Counted Row :=
  let sorted := sort row.vars
  ⟨⟨sorted.value,row.rhs⟩,sorted.cells+2*(rowCells row+sorted.value.length+2)+5⟩

theorem canonical_value (row : Row) : (canonical row).value=Atoms.canonical row := by
  simp only [canonical,sort_value,Atoms.canonical]

theorem canonical_length (row : Row) : (canonical row).value.vars.length=row.vars.length := sort_length _

def canonicalBudget (n : Nat) : Nat := sortBudget n+4*n+13

theorem canonical_cells (n : Nat) (row : Row) (bounded : row.vars.length ≤ n) :
    (canonical row).cells ≤ canonicalBudget n := by
  have sorted := sort_cells row.vars
  have upper : sortBudget row.vars.length ≤ sortBudget n := by
    unfold sortBudget insertionBudget
    gcongr
  simp only [canonical,sort_length,rowCells,canonicalBudget]
  omega

def canonicalRows (rows : List Row) : Counted (List Row) :=
  CapacityMatching.RowCost.gather (fun row =>
    let generated := canonical row
    ⟨[generated.value],generated.cells+rowCells generated.value+2⟩) rows

theorem canonicalRows_value (rows : List Row) :
    (canonicalRows rows).value=rows.map Atoms.canonical := by
  rw [canonicalRows,CapacityMatching.RowCost.gather_value]
  simp only [canonical_value]
  induction rows <;> simp_all

theorem canonicalRows_length (rows : List Row) : (canonicalRows rows).value.length=rows.length := by
  simp [canonicalRows_value]

theorem canonicalRows_storage (rows : List Row) : rowsCells (canonicalRows rows).value=rowsCells rows := by
  rw [canonicalRows_value]
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.map_cons,CapacityMatching.RowCost.rowsCells_cons,ih,rowCells,Atoms.canonical]
      rw [(List.mergeSort_perm row.vars _).length_eq]

def canonicalRowsBudget (n count : Nat) : Nat := count*(canonicalBudget n+n+4+(count+1)*(n+2)+5)+1

theorem canonicalRows_cells (n : Nat) (rows : List Row) (bounded : ∀ row ∈ rows, row.vars.length ≤ n) :
    (canonicalRows rows).cells ≤ canonicalRowsBudget n rows.length := by
  apply CapacityMatching.RowCost.gather_cells _ rows (canonicalBudget n+n+4) (n+2)
  · intro row member
    have first := canonical_cells n row (bounded row member)
    have length := canonical_length row
    have size := bounded row member
    dsimp
    unfold rowCells
    omega
  · intro row member
    have size := bounded row member
    simp only [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,Nat.add_zero,rowCells,canonical_length]
    omega

def dataClause {n : Nat} (basis : List Row) (clause : CNFClause n) : Counted (List Row) :=
  let residual := AffineFeedbackCost.Propagation.residuals basis clause
  let sorted := canonicalRows residual.value
  ⟨sorted.value,residual.cells+sorted.cells+2*(rowsCells residual.value+rowsCells sorted.value)+6*clause.length+3⟩

theorem dataClause_value {n : Nat} (basis : List Row) (clause : CNFClause n) :
    (dataClause basis clause).value=clause.map (fun literal => Atoms.canonical (Propagation.residualRow basis literal)) := by
  simp only [dataClause,canonicalRows_value,AffineFeedbackCost.Propagation.residuals_value,List.map_map,Function.comp_def]

theorem dataClause_length {n : Nat} (basis : List Row) (clause : CNFClause n) :
    (dataClause basis clause).value.length=clause.length := by simp [dataClause_value]

theorem dataClause_storage {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (clause : CNFClause n) :
    rowsCells (dataClause basis clause).value ≤ clause.length*(n+2) := by
  rw [dataClause,canonicalRows_storage]
  have typed := AffineFeedbackCost.Propagation.residuals_valid basis inside clause
  simpa only [AffineFeedbackCost.Propagation.residuals_length] using StrongFeedbackScale.rows_storage n _ typed

def dataClauseBudget (n count : Nat) : Nat :=
  AffineFeedbackCost.Propagation.residualsBudget n count+canonicalRowsBudget n count+4*count*(n+2)+6*count+3

theorem dataClause_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (clause : CNFClause n) : (dataClause basis clause).cells ≤ dataClauseBudget n clause.length := by
  have residual := AffineFeedbackCost.Propagation.residuals_cells basis valid clause
  have typed := AffineFeedbackCost.Propagation.residuals_valid basis valid.2 clause
  have sorted := canonicalRows_cells n (AffineFeedbackCost.Propagation.residuals basis clause).value
    (fun row member => Table.row_length_le n row (typed row member))
  have stored := StrongFeedbackScale.rows_storage n _ typed
  rw [AffineFeedbackCost.Propagation.residuals_length] at sorted stored
  simp only [dataClause,canonicalRows_storage,dataClauseBudget]
  nlinarith

def data {n : Nat} (basis : List Row) : CNFFormula n → Counted Data
  | [] => ⟨[],1⟩
  | clause::rest =>
      let first := dataClause basis clause
      let tail := data basis rest
      ⟨first.value::tail.value,first.cells+tail.cells+2*(rowsCells first.value+dataSize tail.value)+5⟩

theorem data_value {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (data basis formula).value=Atoms.data basis formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp only [data,Atoms.data,List.map_cons,dataClause_value,ih]

theorem data_length {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (data basis formula).value.length=formula.length := by rw [data_value,Atoms.data_length]

theorem data_storage {n : Nat} (basis : List Row) (inside : RowsWithin n basis) (formula : CNFFormula n) :
    dataSize (data basis formula).value ≤ Extract.literalCount formula*(n+2)+formula.length+1 := by
  have stored := StrongFeedbackScale.data_storage basis inside formula
  simp only [data_value,dataSize,Atoms.data_length]
  omega

def dataBudget (n clauses literals : Nat) : Nat :=
  clauses*(dataClauseBudget n literals+2*(literals*(n+2)+clauses+1)+5)+1

theorem data_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) (literals : Nat) (count : Extract.literalCount formula ≤ literals) :
    (data basis formula).cells ≤ dataBudget n formula.length literals := by
  induction formula with
  | nil => simp [data,dataBudget]
  | cons clause rest ih =>
      have counts : clause.length+Extract.literalCount rest ≤ literals := count
      have first := dataClause_cells basis valid clause
      have firstCost : (dataClause basis clause).cells ≤ dataClauseBudget n literals := by
        apply first.trans
        unfold dataClauseBudget AffineFeedbackCost.Propagation.residualsBudget canonicalRowsBudget
        gcongr <;> omega
      have firstStored := dataClause_storage basis valid.2 clause
      have tailStored := data_storage basis valid.2 rest
      have tail := ih (by omega)
      simp only [data,List.length_cons]
      unfold dataBudget at *
      nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.AffineAtomFeedbackCost

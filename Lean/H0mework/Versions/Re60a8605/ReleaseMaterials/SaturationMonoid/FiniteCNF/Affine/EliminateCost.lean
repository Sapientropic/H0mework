import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.Table

/-!
The paired execution follows the original Gaussian source operations. `cells` counts
their source-cell visits; computing the counters themselves and implementing address,
integer and allocation operations at bit level have separate costs.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.Affine.EliminateCost

open InterferenceProgram

structure Reduction where
  row : Row
  xors : Nat
  cells : Nat
  deriving Repr

/-- The counter follows the same heads, membership branches and row XORs as `reduceWith`. -/
def reduce : List Row → Row → Reduction
  | [], row => ⟨row, 0, 1⟩
  | pivot :: rest, row =>
      match pivot.vars with
      | [] =>
          let next := reduce rest row
          ⟨next.row, next.xors, next.cells + 2⟩
      | p :: _ =>
          if p ∈ row.vars then
            let next := reduce rest (row.xor pivot)
            ⟨next.row, next.xors + 1,
              next.cells + pivotMemberVisits p row.vars + Table.mergeVisits row.vars pivot.vars + 3⟩
          else
            let next := reduce rest row
            ⟨next.row, next.xors, next.cells + pivotMemberVisits p row.vars + 2⟩

theorem reduce_row (basis : List Row) (row : Row) : (reduce basis row).row = reduceWith basis row := by
  induction basis generalizing row with
  | nil => rfl
  | cons pivot rest ih =>
      cases shape : pivot.vars with
      | nil => simpa [reduce, reduceWith, shape] using ih row
      | cons p vars =>
          by_cases present : p ∈ row.vars <;> simp [reduce, reduceWith, shape, present, ih]

theorem reduce_xors (basis : List Row) (row : Row) : (reduce basis row).xors ≤ basis.length := by
  induction basis generalizing row with
  | nil => simp [reduce]
  | cons pivot rest ih =>
      cases shape : pivot.vars with
      | nil => simpa [reduce, shape] using (ih row).trans (Nat.le_succ _)
      | cons p vars =>
          by_cases present : p ∈ row.vars
          · simpa [reduce, shape, present] using Nat.add_le_add_right (ih (row.xor pivot)) 1
          · simpa [reduce, shape, present] using (ih row).trans (Nat.le_succ _)

def reduceCellBudget (n : Nat) : Nat := n * (2 * n + 5) + n + 5

theorem reduce_cells (n : Nat) (basis : List Row)
    (basisValid : ∀ row ∈ basis, Table.RowValid n row) (row : Row) (rowValid : Table.RowValid n row) :
    (reduce basis row).cells ≤ basis.length * reduceCellBudget n + 1 := by
  induction basis generalizing row with
  | nil => simp [reduce]
  | cons pivot rest ih =>
      have pivotValid := basisValid pivot (by simp)
      have tailValid : ∀ value ∈ rest, Table.RowValid n value :=
        fun value member => basisValid value (by simp [member])
      have currentLength := Table.row_length_le n row rowValid
      cases shape : pivot.vars with
      | nil =>
          have tail := ih tailValid row rowValid
          simp only [reduce, shape, List.length_cons]
          simp only [reduceCellBudget] at *
          nlinarith
      | cons p vars =>
          have membership := pivotMemberVisits_bound p row.vars
          by_cases present : p ∈ row.vars
          · have merging := Table.mergeVisits_bound n row.vars pivot.vars rowValid.2 pivotValid.1 pivotValid.2
            rw [shape] at merging
            have nextValid := Table.xor_valid n row pivot rowValid pivotValid
            have tail := ih tailValid (row.xor pivot) nextValid
            simp only [reduce, shape, if_pos present, List.length_cons]
            simp only [reduceCellBudget] at *
            nlinarith
          · have tail := ih tailValid row rowValid
            simp only [reduce, shape, if_neg present, List.length_cons]
            simp only [reduceCellBudget] at *
            nlinarith

structure Outcome where
  result : Result
  xors : Nat
  cells : Nat
  deriving Repr

def insert (result : Result) (row : Row) : Outcome :=
  match result with
  | .contradiction => ⟨.contradiction, 0, 1⟩
  | .basis stored =>
      let reduced := reduce stored row.normalize
      let used := Table.mergeVisits row.vars [] + reduced.cells
      match reduced.row.vars with
      | [] => ⟨if reduced.row.rhs then .contradiction else .basis stored, reduced.xors, used + 3⟩
      | _ :: _ => ⟨.basis (stored ++ [reduced.row]), reduced.xors, used + stored.length + 4⟩

theorem insert_result (result : Result) (row : Row) : (insert result row).result = result.insert row := by
  cases result with
  | contradiction => rfl
  | basis stored =>
      simp only [insert, reduce_row, Result.insert]
      cases (reduceWith stored row.normalize).vars <;> rfl

theorem insert_xors (n : Nat) (result : Result) (triangular : result.triangular)
    (inside : result.within n) (row : Row) : (insert result row).xors ≤ n := by
  cases result with
  | contradiction => simp [insert]
  | basis stored =>
      have calls := reduce_xors stored row.normalize
      have rank := basis_length_le n stored triangular inside
      simp only [insert]
      split <;> simp only <;> omega

def insertCellBudget (n : Nat) : Nat := n * reduceCellBudget n + n + 6

theorem insert_cells (n : Nat) (result : Result) (triangular : result.triangular)
    (inside : result.within n) (row : Row) (rowInside : Parity.Within n row.vars) :
    (insert result row).cells ≤ row.vars.length * (2 * n + 5) + insertCellBudget n := by
  cases result with
  | contradiction => simp only [insert, insertCellBudget]; omega
  | basis stored =>
      have normalization := Table.mergeVisits_bound n row.vars [] rowInside (by simp) (by simp [Parity.Within])
      have normalized : Table.RowValid n row.normalize :=
        ⟨row.normalize_nodup, Row.normalize_within n row rowInside⟩
      have reduction := reduce_cells n stored (fun value member =>
        ⟨triangular.1 value member, inside value member⟩) row.normalize normalized
      have rank := basis_length_le n stored triangular inside
      have reductionBound : (reduce stored row.normalize).cells ≤ n * reduceCellBudget n + 1 :=
        reduction.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ rank) 1)
      simp only [insert]
      split <;> simp only
      all_goals
        simp only [insertCellBudget]
        omega

def runFrom : Result → List Row → Outcome
  | result, [] => ⟨result, 0, 1⟩
  | result, row :: rest =>
      let first := insert result row
      let next := runFrom first.result rest
      ⟨next.result, first.xors + next.xors, first.cells + next.cells + 1⟩

def run (rows : List Row) : Outcome := runFrom (.basis []) rows

theorem runFrom_result (result : Result) (rows : List Row) :
    (runFrom result rows).result = eliminateFrom result rows := by
  induction rows generalizing result with
  | nil => rfl
  | cons row rest ih =>
      simp only [runFrom, ih, insert_result, eliminateFrom, List.foldl_cons]

theorem run_result (rows : List Row) : (run rows).result = eliminate rows := runFrom_result (.basis []) rows

theorem runFrom_xors (n : Nat) (result : Result) (triangular : result.triangular)
    (inside : result.within n) (rows : List Row) (rowsInside : RowsWithin n rows) :
    (runFrom result rows).xors ≤ rows.length * n := by
  induction rows generalizing result with
  | nil => simp [runFrom]
  | cons row rest ih =>
      have rowInside := rowsInside row (by simp)
      have first := insert_xors n result triangular inside row
      have nextTriangular : (insert result row).result.triangular := by
        rw [insert_result]
        exact Result.insert_triangular result triangular row
      have nextInside : (insert result row).result.within n := by
        rw [insert_result]
        exact Result.insert_within n result inside row rowInside
      have tail := ih (insert result row).result nextTriangular nextInside
        (fun other member => rowsInside other (by simp [member]))
      simp only [runFrom, List.length_cons]
      nlinarith

theorem run_xors (n : Nat) (rows : List Row) (inside : RowsWithin n rows) :
    (run rows).xors ≤ rows.length * n :=
  runFrom_xors n (.basis []) triangular_nil (by simp [Result.within, RowsWithin]) rows inside

theorem runFrom_cells (n : Nat) (result : Result) (triangular : result.triangular)
    (inside : result.within n) (rows : List Row) (rowsInside : RowsWithin n rows) :
    (runFrom result rows).cells ≤
      Gates.rowTerms rows * (2 * n + 5) + rows.length * (insertCellBudget n + 1) + 1 := by
  induction rows generalizing result with
  | nil => simp [runFrom, Gates.rowTerms]
  | cons row rest ih =>
      have rowInside := rowsInside row (by simp)
      have first := insert_cells n result triangular inside row rowInside
      have nextTriangular : (insert result row).result.triangular := by
        rw [insert_result]
        exact Result.insert_triangular result triangular row
      have nextInside : (insert result row).result.within n := by
        rw [insert_result]
        exact Result.insert_within n result inside row rowInside
      have tail := ih (insert result row).result nextTriangular nextInside
        (fun other member => rowsInside other (by simp [member]))
      simp only [runFrom, Gates.rowTerms, List.map_cons, List.sum_cons, List.length_cons]
      simp only [Gates.rowTerms] at tail
      nlinarith

/-- The counters measure source cells and actual `Row.xor` calls; bit-level machine steps remain separate. -/
theorem run_cells (n : Nat) (rows : List Row) (inside : RowsWithin n rows) :
    (run rows).cells ≤
      Gates.rowTerms rows * (2 * n + 5) + rows.length * (insertCellBudget n + 1) + 1 :=
  runFrom_cells n (.basis []) triangular_nil (by simp [Result.within, RowsWithin]) rows inside

theorem extract_rowTerms {n : Nat} (formula : CNFFormula n) :
    Gates.rowTerms (Extract.extract formula) ≤ 3 * formula.length := by
  have lengthBound := Extract.extract_length formula
  suffices ∀ rows : List Row, (∀ row ∈ rows, row.vars.length ≤ 3) →
      Gates.rowTerms rows ≤ 3 * rows.length by
    exact (this _ (fun row member => (Extract.extract_wellFormed formula row member).2.1)).trans
      (Nat.mul_le_mul_left 3 lengthBound)
  intro rows short
  induction rows with
  | nil => simp [Gates.rowTerms]
  | cons row rest ih =>
      have first := short row (by simp)
      have next := ih (fun other member => short other (by simp [member]))
      simp only [Gates.rowTerms, List.map_cons, List.sum_cons, List.length_cons]
      simp only [Gates.rowTerms] at next
      omega

def fromFormula {n : Nat} (formula : CNFFormula n) : Outcome :=
  let extracted := Extract.run formula
  let reduced := run extracted.rows
  ⟨reduced.result, reduced.xors, extracted.visits + reduced.cells⟩

theorem fromFormula_result {n : Nat} (formula : CNFFormula n) :
    (fromFormula formula).result = eliminate (Extract.extract formula) := run_result _

theorem fromFormula_xors {n : Nat} (formula : CNFFormula n) :
    (fromFormula formula).xors ≤ formula.length * n := by
  exact (run_xors n _ (extract_rowsWithin formula)).trans
    (Nat.mul_le_mul_right n (Extract.extract_length formula))

theorem extracted_cells {n : Nat} (formula : CNFFormula n) :
    (run (Extract.extract formula)).cells ≤ 40 * (formula.length + 1) * (n + 1) ^ 3 := by
  have counted := run_cells n (Extract.extract formula) (extract_rowsWithin formula)
  have terms := extract_rowTerms formula
  have rows := Extract.extract_length formula
  have bounded : (run (Extract.extract formula)).cells ≤
      3 * formula.length * (2 * n + 5) + formula.length * (insertCellBudget n + 1) + 1 := by
    refine counted.trans ?_
    gcongr
  have perRow : 3 * (2 * n + 5) + insertCellBudget n + 1 ≤ 40 * (n + 1) ^ 3 := by
    simp only [insertCellBudget, reduceCellBudget]
    ring_nf
    omega
  have factored : (run (Extract.extract formula)).cells ≤
      formula.length * (3 * (2 * n + 5) + insertCellBudget n + 1) + 1 := by
    convert bounded using 1
    ring
  have positive : 0 < 40 * (n + 1) ^ 3 := by positivity
  calc
    (run (Extract.extract formula)).cells ≤ formula.length * (40 * (n + 1) ^ 3) + 1 :=
      factored.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ perRow) 1)
    _ ≤ formula.length * (40 * (n + 1) ^ 3) + 40 * (n + 1) ^ 3 := by omega
    _ = 40 * (formula.length + 1) * (n + 1) ^ 3 := by ring

theorem fromFormula_cells {n : Nat} (formula : CNFFormula n) :
    (fromFormula formula).cells ≤
      formula.length * (56 * Extract.literalCount formula + 40 * formula.length + 42) + 1 +
      40 * (formula.length + 1) * (n + 1) ^ 3 := by
  exact Nat.add_le_add (Extract.run_visits formula) (extracted_cells formula)

end SaturationMonoid.ComplexityProjection.SATSource.Affine.EliminateCost

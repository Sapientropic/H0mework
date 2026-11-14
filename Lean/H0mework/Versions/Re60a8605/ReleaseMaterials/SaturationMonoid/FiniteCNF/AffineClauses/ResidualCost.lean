import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.AffineClauses.Residual

/-!
Bounds for the existing paired arbitrary-row compiler, including source term
occurrences before cancellation. Only generated table rows use the width bound.
The same rewrite/generate ledgers account for decoder calls and full output copies;
these source-record units do not include counter evaluation or classical bit steps.
-/

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.AffineResidual.Cost

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open AffineClauses (Clause Formula formulaSize Within)
open AffineClauses.Cost (rowCount termCount)
open CapacityMatching.RowCost (rowsCells rowCells decodeRows)
open InterferenceProgram

theorem decoded_valid (n : Nat) (table : Array Row) (valid : Table.Valid n table) (clause : Clause) :
    ∀ row ∈ (decodeRows table clause).value, Table.RowValid n row := by
  rw [CapacityMatching.RowCost.decodeRows_value]
  intro row member
  obtain ⟨source,present,rfl⟩ := List.mem_map.mp member
  exact Table.combine_valid n table valid source.vars ⟨[],source.rhs⟩ (by simp [Table.RowValid,Parity.Within])

theorem decoded_length (table : Array Row) (clause : Clause) :
    (decodeRows table clause).value.length=clause.length := by simp [CapacityMatching.RowCost.decodeRows_value]

theorem decoded_storage (n : Nat) (table : Array Row) (valid : Table.Valid n table) (clause : Clause) :
    rowsCells (decodeRows table clause).value ≤ clause.length*(n+2) := by
  have generated := CapacityMatching.RowCost.table_storage n (decodeRows table clause).value.toArray
    (decoded_valid n table valid clause)
  simpa only [List.size_toArray,List.toList_toArray,decoded_length] using generated

theorem rewrite_rows (table : Array Row) (formula : Formula) :
    rowCount (rewrite table formula).value=rowCount formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp only [rewrite,AffineClauses.Cost.rowCount_cons,decoded_length,ih]

theorem rewrite_valid (n : Nat) (table : Array Row) (valid : Table.Valid n table) (formula : Formula) :
    ∀ clause ∈ (rewrite table formula).value, ∀ row ∈ clause, Table.RowValid n row := by
  induction formula with
  | nil => simp [rewrite]
  | cons clause rest ih =>
      intro source member
      rcases List.mem_cons.mp member with rfl | tail
      · exact decoded_valid n table valid clause
      · exact ih source tail

theorem formula_terms (n : Nat) (formula : Formula)
    (valid : ∀ clause ∈ formula, ∀ row ∈ clause, Table.RowValid n row) :
    termCount formula ≤ rowCount formula*n := by
  induction formula with
  | nil => simp [termCount,rowCount]
  | cons clause rest ih =>
      have first := Table.rowTerms_bound n clause.toArray (valid clause (by simp))
      have tail := ih (fun c member => valid c (by simp [member]))
      simp only [List.size_toArray] at first
      simp only [AffineClauses.Cost.termCount_cons,AffineClauses.Cost.rowCount_cons]
      nlinarith

theorem rewrite_terms (n : Nat) (table : Array Row) (valid : Table.Valid n table) (formula : Formula) :
    termCount (rewrite table formula).value ≤ rowCount formula*n := by
  simpa only [rewrite_rows] using formula_terms n _ (rewrite_valid n table valid formula)

theorem rewrite_size (n : Nat) (table : Array Row) (valid : Table.Valid n table) (formula : Formula) :
    formulaSize (rewrite table formula).value ≤ rowCount formula*(n+2)+formula.length+1 := by
  have terms := rewrite_terms n table valid formula
  rw [AffineClauses.Cost.formula_size,rewrite_rows,rewrite_length]
  nlinarith

theorem rewrite_size_ceiling (n : Nat) (table : Array Row) (valid : Table.Valid n table) (formula : Formula) :
    formulaSize (rewrite table formula).value ≤ (n+3)*formulaSize formula := by
  have bound := rewrite_size n table valid formula
  have measures := AffineClauses.Cost.formula_size formula
  nlinarith

theorem formulaSize_drop (formula : Formula) (count : Nat) : formulaSize (formula.drop count) ≤ formulaSize formula := by
  induction count generalizing formula with
  | zero => rfl
  | succ count ih =>
      cases formula with
      | nil => rfl
      | cons clause rest =>
          simpa only [List.drop_succ_cons] using
            (ih rest).trans (by rw [AffineClauses.Cost.formulaSize_cons]; omega)

theorem combine_prefix_storage (n : Nat) (table : Array Row) (valid : Table.Valid n table) (row : Row) (stage : Nat) :
    rowCells (Table.combine table (row.vars.take stage) ⟨[],row.rhs⟩) ≤ n+2 := by
  have generated := Table.combine_valid n table valid (row.vars.take stage) ⟨[],row.rhs⟩ (by simp [Table.RowValid,Parity.Within])
  exact Nat.add_le_add_right (Table.row_length_le n _ generated) 2

def workspaceBudget (n tableSize sourceSize : Nat) : Nat := (tableSize+2*sourceSize+1)*(n+3)

theorem rewrite_workspace (n : Nat) (table : Array Row) (valid : Table.Valid n table)
    (formula : Formula) (clause : Clause) (present : clause ∈ formula) (row : Row) (suffix stage : Nat) :
    AffineCollect.tableSize table+formulaSize formula+formulaSize (rewrite table (formula.drop suffix)).value+
      rowsCells (decodeRows table clause).value+rowCells (Table.combine table (row.vars.take stage) ⟨[],row.rhs⟩) ≤
        workspaceBudget n table.size (formulaSize formula) := by
  have tableBound := CapacityMatching.RowCost.table_storage n table valid
  have tail := (rewrite_size_ceiling n table valid (formula.drop suffix)).trans
    (Nat.mul_le_mul_left (n+3) (formulaSize_drop formula suffix))
  have clauseSize := AffineClauses.Seed.clause_storage formula clause present
  have clauseBound := (CapacityMatching.RowCost.decodeRows_storage n table valid clause).trans
    (Nat.mul_le_mul_right (n+2) clauseSize)
  have partialRow := combine_prefix_storage n table valid row stage
  unfold AffineCollect.tableSize workspaceBudget
  nlinarith

theorem decodeBudget_mono (n count small large : Nat) (bound : small ≤ large) :
    CapacityMatching.RowCost.decodeBudget n count small ≤ CapacityMatching.RowCost.decodeBudget n count large := by
  unfold CapacityMatching.RowCost.decodeBudget
  gcongr

def rewriteRound (n tableSize sourceSize : Nat) : Nat :=
  CapacityMatching.RowCost.decodeBudget n tableSize sourceSize+2*((n+2)*sourceSize+(n+3)*sourceSize)+5

def rewriteBudget (n tableSize sourceSize : Nat) : Nat := sourceSize*rewriteRound n tableSize sourceSize+1

theorem rewrite_cells_bound (n size : Nat) (table : Array Row) (valid : Table.Valid n table)
    (formula : Formula) (records : formulaSize formula ≤ size) :
    (rewrite table formula).cells ≤ formula.length*rewriteRound n table.size size+1 := by
  induction formula with
  | nil => simp [rewrite]
  | cons clause rest ih =>
      have input : rowsCells clause ≤ size ∧ formulaSize rest ≤ size := by
        rw [AffineClauses.Cost.formulaSize_cons] at records
        omega
      have first := (CapacityMatching.RowCost.decodeRows_cells n table valid clause).trans
        (decodeBudget_mono n table.size _ size input.1)
      have firstSize := (CapacityMatching.RowCost.decodeRows_storage n table valid clause).trans
        (Nat.mul_le_mul_right (n+2) input.1)
      have tailSize := (rewrite_size_ceiling n table valid rest).trans (Nat.mul_le_mul_left (n+3) input.2)
      have tail := ih input.2
      simp only [rewrite,List.length_cons,rewriteRound] at *
      nlinarith

theorem rewrite_cells (n : Nat) (table : Array Row) (valid : Table.Valid n table) (formula : Formula) :
    (rewrite table formula).cells ≤ rewriteBudget n table.size (formulaSize formula) := by
  have bound := rewrite_cells_bound n (formulaSize formula) table valid formula (Nat.le_refl _)
  have length : formula.length ≤ formulaSize formula := by rw [AffineClauses.Cost.formula_size]; omega
  exact bound.trans (by unfold rewriteBudget; gcongr)

theorem clean_valid (n : Nat) (formula : Formula)
    (valid : ∀ clause ∈ formula, ∀ row ∈ clause, Table.RowValid n row) :
    ∀ clause ∈ AffineClauses.clean formula, ∀ row ∈ clause, Table.RowValid n row :=
  fun clause member => valid clause (List.mem_filter.mp member).1

theorem clean_rows (formula : Formula) : rowCount (AffineClauses.clean formula) ≤ rowCount formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases truth : AffineClauses.tautology clause <;>
        simp [AffineClauses.clean,truth,AffineClauses.Cost.rowCount_cons] at ih ⊢ <;> omega

theorem generate_rows (n : Nat) (basis : List Row) (formula : Formula) :
    rowCount (generate n basis formula).value ≤ rowCount formula := by
  rw [generate_value]
  exact (clean_rows _).trans_eq (rewrite_rows _ _)

theorem generate_terms (n : Nat) (basis : List Row) (formula : Formula) :
    termCount (generate n basis formula).value ≤ rowCount formula*(freeIndices n basis).length := by
  have valid := clean_valid _ _ (rewrite_valid _ _ (Table.coordinates_valid n basis) formula)
  have bound := formula_terms _ _ valid
  rw [← generate_value] at bound
  exact bound.trans (Nat.mul_le_mul_right _ (generate_rows n basis formula))

theorem generate_size (n : Nat) (basis : List Row) (formula : Formula) :
    formulaSize (generate n basis formula).value ≤ rowCount formula*((freeIndices n basis).length+2)+formula.length+1 := by
  have terms := generate_terms n basis formula
  have rows := generate_rows n basis formula
  have length := AffineResidual.generate_length n basis formula
  rw [AffineClauses.Cost.formula_size]
  nlinarith

theorem coordinates_valid (n : Nat) (basis : List Row) : Table.Valid n (Table.coordinates n basis) := by
  intro row member
  have original := Table.coordinates_valid n basis row member
  exact ⟨original.1,fun i hit => (original.2 i hit).trans_le (Table.freeWidth_le n basis)⟩

theorem generate_size_ceiling (n : Nat) (basis : List Row) (formula : Formula) :
    formulaSize (generate n basis formula).value ≤ (n+3)*formulaSize formula := by
  rw [generate_value]
  exact (AffineClauses.Cost.clean_size _).trans (rewrite_size_ceiling n _ (coordinates_valid n basis) formula)

def cleanBudget (n size : Nat) : Nat :=
  size*n*(2*n+9)+size*(EliminateCost.insertCellBudget n+9)+size*(2*AffineCarrier.Cost.cellBound n+2*((n+3)*size)+11)+1

theorem rewritten_clean_cells (n : Nat) (table : Array Row) (valid : Table.Valid n table) (formula : Formula) :
    (AffineClauses.cleanRun (rewrite table formula).value).visits ≤ cleanBudget n (formulaSize formula) := by
  have inside := rewrite_within n table valid formula
  have generated := AffineClauses.Cost.cleanRun_ceiling n (rewrite table formula).value inside
    ((n+3)*formulaSize formula) (rewrite_size_ceiling n table valid formula)
  have terms := rewrite_terms n table valid formula
  have measures : formula.length ≤ formulaSize formula ∧ rowCount formula ≤ formulaSize formula := by
    rw [AffineClauses.Cost.formula_size]
    omega
  rw [rewrite_length,rewrite_rows] at generated
  have termBound := terms.trans (Nat.mul_le_mul_right n measures.2)
  apply generated.trans
  unfold cleanBudget
  gcongr <;> omega

def generateBudget (n size : Nat) : Nat :=
  AffineCollect.Cost.coordinateBudget n+rewriteBudget n n size+cleanBudget n size+
    2*(AffineCarrier.Cost.cellBound n+2*(n+3)*size)+9

theorem generate_cells (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (formula : Formula) :
    (generate n basis formula).cells ≤ generateBudget n (formulaSize formula) := by
  have coordinates := AffineCollect.Cost.coordinate_visits n basis valid
  have sourceTable := AffineCollect.Cost.coordinate_size n basis
  have tableValid := coordinates_valid n basis
  have compiled := rewrite_cells n _ tableValid formula
  rw [Table.coordinates_size] at compiled
  have cleaned := rewritten_clean_cells n _ tableValid formula
  have written := rewrite_size_ceiling n _ tableValid formula
  have output := generate_size_ceiling n basis formula
  change AffineCollect.coordinateWork n basis+(rewrite (Table.coordinates n basis) formula).cells+
    (AffineClauses.cleanRun (rewrite (Table.coordinates n basis) formula).value).visits+
    2*(AffineCollect.tableSize (Table.coordinates n basis)+formulaSize (rewrite (Table.coordinates n basis) formula).value+
      formulaSize (generate n basis formula).value)+9 ≤ _
  unfold generateBudget
  nlinarith

theorem generateBudget_mono (n small large : Nat) (bound : small ≤ large) : generateBudget n small ≤ generateBudget n large := by
  unfold generateBudget rewriteBudget rewriteRound cleanBudget CapacityMatching.RowCost.decodeBudget
  gcongr

theorem branch_cells (n : Nat) (clause : Clause) (remaining : Formula) (inside : Within n (clause::remaining))
    (basis : List Row) (produced : basis ∈ (AffineClauses.clauseAction clause [[]]).value) :
    (generate n basis remaining).cells ≤ generateBudget n (formulaSize (clause::remaining)) := by
  have valid := AffineClauses.clauseAction_valid n clause (inside clause (by simp)) [[]] (by
    intro b member
    have empty : b=[] := List.mem_singleton.mp member
    subst b
    exact ⟨triangular_nil,by simp [RowsWithin]⟩)
  exact (generate_cells n basis (valid basis produced) remaining).trans
    (generateBudget_mono n _ _ (by rw [AffineClauses.Cost.formulaSize_cons]; omega))

theorem generated_workspace (n : Nat) (basis : List Row) (formula : Formula)
    (clause : Clause) (present : clause ∈ formula) (row : Row) (suffix stage : Nat) :
    AffineCollect.tableSize (generate n basis formula).table+formulaSize formula+
      formulaSize (rewrite (generate n basis formula).table (formula.drop suffix)).value+
      rowsCells (decodeRows (generate n basis formula).table clause).value+
      rowCells (Table.combine (generate n basis formula).table (row.vars.take stage) ⟨[],row.rhs⟩) ≤
        workspaceBudget n n (formulaSize formula) := by
  simpa only [generate,Table.coordinates_size] using
    rewrite_workspace n (Table.coordinates n basis) (coordinates_valid n basis) formula clause present row suffix stage

end SaturationMonoid.ComplexityProjection.SATSource.AffineResidual.Cost

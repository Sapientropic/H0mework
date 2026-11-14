import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ConditionalCandidateCostFunctional

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ConditionalCandidateCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowCells rowsCells)
open InterferenceProgram
open FunctionalSubstitution (Instruction)
open FunctionalSchedule.Cost (instructionSize inputSize)
abbrev Counted := CapacityMatching.SourceCost.Counted

def split {n : Nat} (formula : CNFFormula n) (basis : List Row) (i : Fin n) :
    Counted (Option (List Row × List Row)) :=
  let left := AffineRelationExtractionCost.branch formula (.basis basis) i false
  let right := AffineRelationExtractionCost.branch formula (.basis basis) i true
  let value := match left.value,right.value with
    | .basis a,.basis b => some (a,b)
    | _,_ => none
  ⟨value,left.cells+right.cells+
    2*(AffineCarrier.cellSize basis+AffineCarrier.resultSize left.value+AffineCarrier.resultSize right.value)+8⟩

theorem split_value {n : Nat} (formula : CNFFormula n) (basis : List Row) (i : Fin n) :
    (split formula basis i).value=ConditionalPivot.split formula basis i := by
  simp only [split,AffineRelationExtractionCost.branch_value,ConditionalPivot.split]
  rfl

def splitBudget (n clauses literals basisSize : Nat) : Nat :=
  2*AffineRelationExtractionCost.branchBudget n clauses literals+
    2*(basisSize+2*(AffineCarrier.Cost.cellBound n+1))+8

theorem split_cells {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (i : Fin n) :
    (split formula basis i).cells ≤
      splitBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  have left := AffineRelationExtractionCost.branch_cells formula (.basis basis) valid i false
  have right := AffineRelationExtractionCost.branch_cells formula (.basis basis) valid i true
  have leftValid := BranchImage.branch_invariants formula (.basis basis) i false valid.2 valid.1
  have rightValid := BranchImage.branch_invariants formula (.basis basis) i true valid.2 valid.1
  have leftSize := AffineCarrier.Cost.result_size n _ leftValid.2 leftValid.1
  have rightSize := AffineCarrier.Cost.result_size n _ rightValid.2 rightValid.1
  simp only [split,splitBudget,AffineRelationExtractionCost.branch_value]
  omega

def coordinates (n : Nat) (basis : List Row) : Counted (Array Row) :=
  ⟨Table.coordinates n basis,AffineCollect.coordinateWork n basis⟩

theorem coordinates_value (n : Nat) (basis : List Row) : (coordinates n basis).value=Table.coordinates n basis := rfl

theorem coordinates_cells (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (coordinates n basis).cells ≤ AffineCollect.Cost.coordinateBudget n :=
  AffineCollect.Cost.coordinate_visits n basis valid

def width (n : Nat) (basis : List Row) : Counted Nat :=
  let free := freeIndices n basis
  ⟨free.length,freeIndexVisits n basis+3*free.length+2*n+2*AffineCarrier.cellSize basis+9⟩

theorem width_value (n : Nat) (basis : List Row) : (width n basis).value=(freeIndices n basis).length := rfl

def widthBudget (n basisSize : Nat) : Nat := (n+1)*(n+2)+5*n+2*basisSize+9

theorem width_cells (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (width n basis).cells ≤ widthBudget n (AffineCarrier.cellSize basis) := by
  have source := bounded_freeIndexVisits n basis valid.1 valid.2
  have count := Table.freeWidth_le n basis
  simp only [width,widthBudget]
  omega

theorem table_valid (n : Nat) (basis : List Row) : Table.Valid n (Table.coordinates n basis) := by
  intro row member
  have source := Table.coordinates_valid n basis row member
  exact ⟨source.1,fun i present => (source.2 i present).trans_le (Table.freeWidth_le n basis)⟩

theorem split_valid {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (i : Fin n) (left right : List Row)
    (found : (split formula basis i).value=some (left,right)) :
    (Triangular left ∧ RowsWithin n left) ∧ (Triangular right ∧ RowsWithin n right) := by
  have ends := ConditionalPivot.split_branches formula basis i left right ((split_value formula basis i).symm.trans found)
  have a := BranchImage.branch_invariants formula (.basis basis) i false valid.2 valid.1
  have b := BranchImage.branch_invariants formula (.basis basis) i true valid.2 valid.1
  rw [ends.1] at a
  rw [ends.2] at b
  exact ⟨a.symm,b.symm⟩

def project (table : Array Row) (rows : List Row) : Counted (List Row) := CapacityMatching.RowCost.decodeRows table rows

theorem project_value (table : Array Row) (rows : List Row) :
    (project table rows).value=ConditionalPivot.project table rows := CapacityMatching.RowCost.decodeRows_value table rows

def instructionBound (size : Nat) : Nat := 20+8*size
def instructionBudget (size : Nat) : Nat := Code.conditionalBudget size+20*(size+3)

def instruction (table : Array Row) (i j : Nat) (left right : List Row) : Counted Instruction :=
  let body := Code.conditionalBody table i j left right
  ⟨⟨j,body.value⟩,body.cells+2*body.value.code.size+16⟩

theorem instruction_value (table : Array Row) (i j : Nat) (left right : List Row) :
    (instruction table i j left right).value=⟨j,ConditionalPivot.body table i j left right⟩ := by
  simp only [instruction,Code.conditionalBody_value]

theorem instruction_size (table : Array Row) (i j : Nat) (left right : List Row) (size : Nat)
    (tableBound : AffineCollect.tableSize table ≤ size) (leftBound : rowsCells left ≤ size) (rightBound : rowsCells right ≤ size) :
    instructionSize (instruction table i j left right).value ≤ instructionBound size := by
  have source := Code.conditionalBody_size table i j left right size tableBound leftBound rightBound
  simp only [instruction,instructionSize,instructionBound]
  omega

theorem instruction_cells (table : Array Row) (i j : Nat) (left right : List Row) (size : Nat)
    (tableBound : AffineCollect.tableSize table ≤ size) (leftBound : rowsCells left ≤ size) (rightBound : rowsCells right ≤ size) :
    (instruction table i j left right).cells ≤ instructionBudget size := by
  have source := Code.conditionalBody_cells table i j left right size tableBound leftBound rightBound
  have stored := Code.conditionalBody_size table i j left right size tableBound leftBound rightBound
  simp only [instruction,instructionBudget]
  omega

def makeCalls {k : Nat} (table : Array Row) (i : Nat) (left right : List Row) : List (Fin k) → Counted (List Instruction)
  | [] => ⟨[],1⟩
  | j::rest =>
      let first := instruction table i j.val left right
      let tail := makeCalls table i left right rest
      ⟨first.value::tail.value,first.cells+tail.cells+2*(instructionSize first.value+inputSize tail.value)+8⟩

theorem makeCalls_value {k : Nat} (table : Array Row) (i : Nat) (left right : List Row) (indices : List (Fin k)) :
    (makeCalls table i left right indices).value=indices.map (fun j => ⟨j.val,ConditionalPivot.body table i j.val left right⟩) := by
  induction indices <;> simp_all [makeCalls,instruction_value]

theorem makeCalls_length {k : Nat} (table : Array Row) (i : Nat) (left right : List Row) (indices : List (Fin k)) :
    (makeCalls table i left right indices).value.length=indices.length := by simp only [makeCalls_value,List.length_map]

theorem makeCalls_storage {k : Nat} (table : Array Row) (i : Nat) (left right : List Row) (indices : List (Fin k)) (size : Nat)
    (tableBound : AffineCollect.tableSize table ≤ size) (leftBound : rowsCells left ≤ size) (rightBound : rowsCells right ≤ size) :
    inputSize (makeCalls table i left right indices).value ≤ indices.length*instructionBound size+1 := by
  induction indices with
  | nil => simp [makeCalls]
  | cons j rest ih =>
      have first := instruction_size table i j.val left right size tableBound leftBound rightBound
      simp only [makeCalls,FunctionalSchedule.Cost.inputSize_cons,List.length_cons]
      nlinarith

def makeCallsBudget (count size : Nat) : Nat := count*(instructionBudget size+4*(count+1)*instructionBound size+10)+1

theorem makeCalls_cells_aux {k : Nat} (table : Array Row) (i : Nat) (left right : List Row) (indices : List (Fin k)) (count size : Nat)
    (tableBound : AffineCollect.tableSize table ≤ size) (leftBound : rowsCells left ≤ size) (rightBound : rowsCells right ≤ size)
    (length : indices.length ≤ count) :
    (makeCalls table i left right indices).cells ≤ indices.length*(instructionBudget size+4*(count+1)*instructionBound size+10)+1 := by
  induction indices with
  | nil => simp [makeCalls]
  | cons j rest ih =>
      have tail := ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) length)
      have first := instruction_cells table i j.val left right size tableBound leftBound rightBound
      have stored := instruction_size table i j.val left right size tableBound leftBound rightBound
      have remaining := makeCalls_storage table i left right rest size tableBound leftBound rightBound
      simp only [makeCalls,List.length_cons] at *
      nlinarith

theorem makeCalls_cells {k : Nat} (table : Array Row) (i : Nat) (left right : List Row) (indices : List (Fin k)) (count size : Nat)
    (tableBound : AffineCollect.tableSize table ≤ size) (leftBound : rowsCells left ≤ size) (rightBound : rowsCells right ≤ size)
    (length : indices.length ≤ count) : (makeCalls table i left right indices).cells ≤ makeCallsBudget count size := by
  apply (makeCalls_cells_aux table i left right indices count size tableBound leftBound rightBound length).trans
  unfold makeCallsBudget
  gcongr

def branchCandidates {n : Nat} (formula : CNFFormula n) (basis : List Row) (table : Array Row) (free : Nat) (i : Fin n) :
    Counted (List Instruction) :=
  let ends := split formula basis i
  match ends.value with
  | none => ⟨[],ends.cells+5⟩
  | some (a,b) =>
      let left := project table a
      let right := project table b
      let output := makeCalls table i.val left.value right.value (List.finRange free)
      ⟨output.value,ends.cells+left.cells+right.cells+output.cells+
        2*(rowsCells a+rowsCells b+rowsCells left.value+rowsCells right.value+inputSize output.value)+3*free+12⟩

theorem branchCandidates_value {n : Nat} (formula : CNFFormula n) (basis : List Row) (table : Array Row) (i : Fin n) :
    (branchCandidates formula basis table (freeIndices n basis).length i).value=
      ConditionalPivot.branchCandidates formula basis table i := by
  simp only [branchCandidates,split_value,ConditionalPivot.branchCandidates]
  cases ends : ConditionalPivot.split formula basis i with
  | none => rfl
  | some pair =>
      rcases pair with ⟨a,b⟩
      simp only [makeCalls_value,project_value]
      rfl

def bodyScale (n : Nat) : Nat := AffineCarrier.Cost.cellBound n*(n+2)+AffineCarrier.Cost.cellBound n+1
def branchStorage (n : Nat) : Nat := n*instructionBound (bodyScale n)+1

theorem decodeBudget_mono (n count small large : Nat) (bounded : small ≤ large) :
    CapacityMatching.RowCost.decodeBudget n count small ≤ CapacityMatching.RowCost.decodeBudget n count large := by
  unfold CapacityMatching.RowCost.decodeBudget
  gcongr

theorem split_sizes {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (i : Fin n) (a b : List Row) (found : (split formula basis i).value=some (a,b)) :
    rowsCells a ≤ AffineCarrier.Cost.cellBound n ∧ rowsCells b ≤ AffineCarrier.Cost.cellBound n := by
  have source := split_valid formula basis valid i a b found
  have left := AffineCarrier.Cost.cell_size n a source.1.1 source.1.2
  have right := AffineCarrier.Cost.cell_size n b source.2.1 source.2.2
  unfold AffineCarrier.cellSize at left right
  omega

theorem project_bound (n : Nat) (basis rows : List Row) (bounded : rowsCells rows ≤ AffineCarrier.Cost.cellBound n) :
    rowsCells (project (Table.coordinates n basis) rows).value ≤ AffineCarrier.Cost.cellBound n*(n+2) :=
  (CapacityMatching.RowCost.decodeRows_storage n _ (table_valid n basis) rows).trans (Nat.mul_le_mul_right (n+2) bounded)

theorem bodyScale_bounds (n : Nat) (basis rows : List Row) (bounded : rowsCells rows ≤ AffineCarrier.Cost.cellBound n) :
    AffineCollect.tableSize (Table.coordinates n basis) ≤ bodyScale n ∧
      rowsCells (project (Table.coordinates n basis) rows).value ≤ bodyScale n := by
  have table := AffineCollect.Cost.coordinate_size n basis
  have source := project_bound n basis rows bounded
  unfold bodyScale
  omega

theorem branchCandidates_storage {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (i : Fin n) :
    inputSize (branchCandidates formula basis (Table.coordinates n basis) (freeIndices n basis).length i).value ≤ branchStorage n := by
  simp only [branchCandidates]
  cases ends : (split formula basis i).value with
  | none => simp [branchStorage]
  | some pair =>
      rcases pair with ⟨a,b⟩
      have stored := split_sizes formula basis valid i a b ends
      have left := bodyScale_bounds n basis a stored.1
      have right := bodyScale_bounds n basis b stored.2
      have output := makeCalls_storage (Table.coordinates n basis) i.val
        (project (Table.coordinates n basis) a).value (project (Table.coordinates n basis) b).value
        (List.finRange (freeIndices n basis).length) (bodyScale n) left.1 left.2 right.2
      have count := Table.freeWidth_le n basis
      simp only [List.length_finRange] at output
      simp only [branchStorage]
      nlinarith

def branchBudget (n clauses literals basisSize : Nat) : Nat :=
  splitBudget n clauses literals basisSize+2*CapacityMatching.RowCost.decodeBudget n n (AffineCarrier.Cost.cellBound n)+
    makeCallsBudget n (bodyScale n)+
    2*(2*AffineCarrier.Cost.cellBound n+2*AffineCarrier.Cost.cellBound n*(n+2)+branchStorage n)+3*n+12

theorem branchCandidates_cells {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (i : Fin n) :
    (branchCandidates formula basis (Table.coordinates n basis) (freeIndices n basis).length i).cells ≤
      branchBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  have splitWork := split_cells formula basis valid i
  simp only [branchCandidates]
  cases ends : (split formula basis i).value with
  | none => simp only; unfold branchBudget; omega
  | some pair =>
      rcases pair with ⟨a,b⟩
      have stored := split_sizes formula basis valid i a b ends
      have left := bodyScale_bounds n basis a stored.1
      have right := bodyScale_bounds n basis b stored.2
      have decodedLeft := project_bound n basis a stored.1
      have decodedRight := project_bound n basis b stored.2
      have aWork := (CapacityMatching.RowCost.decodeRows_cells n (Table.coordinates n basis) (table_valid n basis) a).trans
        (decodeBudget_mono n _ _ _ stored.1)
      have bWork := (CapacityMatching.RowCost.decodeRows_cells n (Table.coordinates n basis) (table_valid n basis) b).trans
        (decodeBudget_mono n _ _ _ stored.2)
      rw [Table.coordinates_size] at aWork bWork
      have count := Table.freeWidth_le n basis
      have output := makeCalls_cells (Table.coordinates n basis) i.val
        (project (Table.coordinates n basis) a).value (project (Table.coordinates n basis) b).value
        (List.finRange (freeIndices n basis).length) n (bodyScale n) left.1 left.2 right.2 (by simpa)
      have outputSize := branchCandidates_storage formula basis valid i
      simp only [branchCandidates,ends] at outputSize
      change (project (Table.coordinates n basis) a).cells ≤ _ at aWork
      change (project (Table.coordinates n basis) b).cells ≤ _ at bWork
      simp only [branchBudget]
      nlinarith

def branches {n : Nat} (formula : CNFFormula n) (basis : List Row) (table : Array Row) (free : Nat) : List (Fin n) → Counted (List Instruction)
  | [] => ⟨[],1⟩
  | i::rest =>
      let first := branchCandidates formula basis table free i
      let tail := branches formula basis table free rest
      let output := first.value++tail.value
      ⟨output,first.cells+tail.cells+2*(inputSize first.value+inputSize tail.value+inputSize output)+8⟩

theorem branches_value {n : Nat} (formula : CNFFormula n) (basis : List Row) (table : Array Row) (indices : List (Fin n)) :
    (branches formula basis table (freeIndices n basis).length indices).value=
      indices.flatMap (ConditionalPivot.branchCandidates formula basis table) := by
  induction indices <;> simp_all [branches,branchCandidates_value]

theorem branches_storage {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (indices : List (Fin n)) :
    inputSize (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length indices).value ≤
      indices.length*branchStorage n+1 := by
  induction indices with
  | nil => simp [branches]
  | cons i rest ih =>
      have first := branchCandidates_storage formula basis valid i
      have joined : inputSize (branchCandidates formula basis (Table.coordinates n basis) (freeIndices n basis).length i).value+
          inputSize (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length rest).value ≤
          (rest.length+1)*branchStorage n+2 := by nlinarith
      simp only [branches,Functional.inputSize_append,List.length_cons]
      omega

def branchesBudget (n clauses literals basisSize : Nat) : Nat :=
  n*(branchBudget n clauses literals basisSize+8*(n+1)*branchStorage n+16)+1

theorem branches_cells_aux {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (indices : List (Fin n)) (length : indices.length ≤ n) :
    (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length indices).cells ≤
      indices.length*(branchBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis)+8*(n+1)*branchStorage n+16)+1 := by
  induction indices with
  | nil => simp [branches]
  | cons i rest ih =>
      have tail := ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) length)
      have first := branchCandidates_cells formula basis valid i
      have firstSize := branchCandidates_storage formula basis valid i
      have tailSize := branches_storage formula basis valid rest
      have outputSize := branches_storage formula basis valid (i::rest)
      simp only [branches,List.length_cons] at outputSize ⊢
      simp only [List.length_cons] at length
      nlinarith

theorem branches_cells {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length (List.finRange n)).cells ≤
      branchesBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  simpa only [branchesBudget,List.length_finRange] using
    branches_cells_aux formula basis valid (List.finRange n) (by simp)

def candidates {n : Nat} (formula : CNFFormula n) (basis : List Row) : Counted (List Instruction) :=
  let table := coordinates n basis
  let free := width n basis
  let prior := Functional.candidates table.value formula
  let conditional := branches formula basis table.value free.value (List.finRange n)
  let output := prior.value++conditional.value
  ⟨output,table.cells+free.cells+prior.cells+conditional.cells+
    2*(AffineCarrier.cellSize basis+AffineCollect.tableSize table.value+
      inputSize prior.value+inputSize conditional.value+inputSize output)+2*n+16⟩

theorem candidates_value {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (candidates formula basis).value=ConditionalPivot.candidates formula basis := by
  simp only [candidates,coordinates_value,width_value,Functional.candidates_value,branches_value,ConditionalPivot.candidates]

def priorStorage (n clauses : Nat) : Nat := 3*clauses*Functional.callSize (AffineCarrier.Cost.cellBound n)+1
def conditionalStorage (n : Nat) : Nat := n*branchStorage n+1

def candidatesBudget (n clauses literals basisSize : Nat) : Nat :=
  AffineCollect.Cost.coordinateBudget n+widthBudget n basisSize+
    Functional.candidatesBudget clauses literals (AffineCarrier.Cost.cellBound n)+branchesBudget n clauses literals basisSize+
    2*(basisSize+AffineCarrier.Cost.cellBound n+2*(priorStorage n clauses+conditionalStorage n))+2*n+16

theorem candidates_cells {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (candidates formula basis).cells ≤ candidatesBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  have tableWork := coordinates_cells n basis valid
  have freeWork := width_cells n basis valid
  have tableSize := AffineCollect.Cost.coordinate_size n basis
  have priorWork := Functional.candidates_cells (Table.coordinates n basis) formula (AffineCarrier.Cost.cellBound n) tableSize
  have nextWork := branches_cells formula basis valid
  have priorSize := Functional.filter_storage (Table.coordinates n basis) (Functional.relations formula).value
    (AffineCarrier.Cost.cellBound n) tableSize
  have relationCount := Functional.relations_length formula
  have priorBound : inputSize (Functional.candidates (Table.coordinates n basis) formula).value ≤ priorStorage n formula.length := by
    simp only [Functional.candidates,priorStorage]
    nlinarith
  have nextSize := branches_storage formula basis valid (List.finRange n)
  simp only [List.length_finRange] at nextSize
  have outputSize := Functional.inputSize_append (Functional.candidates (Table.coordinates n basis) formula).value
    (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length (List.finRange n)).value
  simp only [candidates,coordinates_value,width_value,candidatesBudget,conditionalStorage]
  omega

end SaturationMonoid.ComplexityProjection.SATSource.ConditionalCandidateCost

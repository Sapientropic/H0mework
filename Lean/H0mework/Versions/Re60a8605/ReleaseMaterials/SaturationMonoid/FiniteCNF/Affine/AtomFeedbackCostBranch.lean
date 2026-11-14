import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.AtomFeedbackCostInventory

/-! The same BranchImage branch consumes the paired atom frontend and Gaussian
    return. `paidCells` records these lowered stages and Propagation. The actual
    Subsumption and equation extraction still execute between them; their own
    scan/normalization ledgers are not represented as a constant-time call.
    These source-record bills do not include the separate sparse-to-bit encoding,
    fixed RowXor-machine handoff, counter arithmetic or full TM execution. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineAtomFeedbackCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowCells rowsCells)
attribute [local irreducible] data front

def sourceBound (n clauses literals : Nat) : Nat := literals*(n+2)+clauses+1

theorem frontBudget_mono (small large : Nat) (bound : small ≤ large) : frontBudget small ≤ frontBudget large := by
  unfold frontBudget keysBudget tableBudget formulaBudget uniqueBudget addressBudget
  gcongr

theorem unitRows_storage {n : Nat} (formula : CNFFormula n) : rowsCells (Atoms.unitRows formula) ≤ 3*formula.length := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      cases clause with
      | nil => simp only [Atoms.unitRows,List.flatMap_cons,CapacityMatching.RowCost.rowsCells_append,
          CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells,List.length_cons,List.length_nil] at *; omega
      | cons literal tail =>
          cases tail with
          | nil => simp only [Atoms.unitRows,List.flatMap_cons,CapacityMatching.RowCost.rowsCells_append,
              CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells,List.length_cons,List.length_nil] at *; omega
          | cons other tail => simp only [Atoms.unitRows,List.flatMap_cons,List.nil_append,List.length_cons] at *; omega

theorem equations_storage {n : Nat} (formula : CNFFormula n) : rowsCells (Atoms.equations formula) ≤ 8*formula.length := by
  have units := unitRows_storage formula
  have count := Extract.extract_length formula
  have terms := EliminateCost.extract_rowTerms formula
  rw [AffineCollect.Cost.rows_size] at units
  rw [Atoms.equations,CapacityMatching.RowCost.rowsCells_append]
  simp only [AffineCollect.Cost.rows_size]
  omega

structure Learning where
  value : List Row
  paidCells : Nat
  deriving Repr

def learnFrom (source : Data) : Learning :=
  let prepared := front source
  let normalized := Subsumption.reduce prepared.formula
  let relations := Atoms.equations normalized
  let decoded := CapacityMatching.RowCost.decodeRows prepared.table relations
  ⟨decoded.value,prepared.cells+decoded.cells+
    2*(dataSize source+CapacityMatching.RowCost.formulaCells normalized+
      rowsCells relations+rowsCells decoded.value)+7⟩

theorem learnFrom_value (source : Data) :
    (learnFrom source).value=(Atoms.equations (Subsumption.reduce (Atoms.compile source))).map (Atoms.decode source) := by
  simp only [learnFrom,CapacityMatching.RowCost.decodeRows_value,front_table,front_formula]
  rfl

def learn {n : Nat} (basis : List Row) (formula : CNFFormula n) : Learning :=
  let source := data basis formula
  let returned := learnFrom source.value
  ⟨returned.value,source.cells+returned.paidCells⟩

theorem learn_value {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (learn basis formula).value=Atoms.learn basis formula := by
  simp only [learn]
  rw [data_value,learnFrom_value]
  rfl

theorem normalized_storage {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    CapacityMatching.RowCost.formulaCells (Atoms.ofFormula basis formula) ≤
      3*(Extract.literalCount formula+1)+2*(formula.length+1)+1 := by
  obtain ⟨clauses,literals⟩ := StrongFeedbackScale.atom_formula_size basis formula
  unfold CapacityMatching.RowCost.formulaCells
  omega

def returnRowsBound (n clauses : Nat) : Nat := 2*(clauses+1)*(n+2)

def learnBudget (n clauses literals : Nat) : Nat :=
  dataBudget n clauses literals+frontBudget (sourceBound n clauses literals)+
    CapacityMatching.RowCost.decodeBudget n (literals+1) (8*(clauses+1))+
    2*(sourceBound n clauses literals+3*(literals+1)+2*(clauses+1)+1+
      8*(clauses+1)+returnRowsBound n clauses)+7

private theorem learnFrom_paid {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) :
    (learnFrom (Atoms.data basis formula)).paidCells ≤
      frontBudget (sourceBound n formula.length (Extract.literalCount formula))+
      CapacityMatching.RowCost.decodeBudget n (Extract.literalCount formula+1) (8*(formula.length+1))+
      2*(sourceBound n formula.length (Extract.literalCount formula)+3*(Extract.literalCount formula+1)+
        2*(formula.length+1)+1+8*(formula.length+1)+returnRowsBound n formula.length)+7 := by
  have sourceSize := data_storage basis valid.2 formula
  rw [data_value] at sourceSize
  have frontCost := (front_cells (Atoms.data basis formula)).trans (frontBudget_mono _ _ sourceSize)
  have typed := Atoms.table_valid n _ (Atoms.data_valid basis valid.2 formula)
  have decoded := CapacityMatching.RowCost.decodeRows_cells n _ typed (Atoms.equations (Atoms.ofFormula basis formula))
  have equations := (equations_storage (Atoms.ofFormula basis formula)).trans
    (Nat.mul_le_mul_left 8 (StrongFeedbackScale.atom_formula_size basis formula).1)
  rw [StrongFeedbackScale.atom_table_size] at decoded
  have decodedCost := decoded.trans (StrongFeedbackScale.decodeBudget_mono n _ _ _ _
    (StrongFeedbackScale.atom_width basis formula) equations)
  have normalized := normalized_storage basis formula
  have output := StrongFeedbackScale.atoms_learn_storage basis valid.2 formula
  have sourceStored : dataSize (Atoms.data basis formula) ≤ sourceBound n formula.length (Extract.literalCount formula) := by
    exact sourceSize
  change (front (Atoms.data basis formula)).cells+
    (CapacityMatching.RowCost.decodeRows (front (Atoms.data basis formula)).table
      (Atoms.equations (Subsumption.reduce (front (Atoms.data basis formula)).formula))).cells+
    2*(dataSize (Atoms.data basis formula)+
      CapacityMatching.RowCost.formulaCells (Subsumption.reduce (front (Atoms.data basis formula)).formula)+
      rowsCells (Atoms.equations (Subsumption.reduce (front (Atoms.data basis formula)).formula))+
      rowsCells (learnFrom (Atoms.data basis formula)).value)+7 ≤ _
  have sameValue : (learnFrom (Atoms.data basis formula)).value=Atoms.learn basis formula := by rw [learnFrom_value]; rfl
  rw [sameValue,front_table,front_formula]
  change (front (Atoms.data basis formula)).cells+
    (CapacityMatching.RowCost.decodeRows (Atoms.table (Atoms.data basis formula)) (Atoms.equations (Atoms.ofFormula basis formula))).cells+
    2*(dataSize (Atoms.data basis formula)+CapacityMatching.RowCost.formulaCells (Atoms.ofFormula basis formula)+
      rowsCells (Atoms.equations (Atoms.ofFormula basis formula))+rowsCells (Atoms.learn basis formula))+7 ≤ _
  change rowsCells (Atoms.learn basis formula) ≤ returnRowsBound n formula.length at output
  change (front (Atoms.data basis formula)).cells ≤ frontBudget (sourceBound n formula.length (Extract.literalCount formula)) at frontCost
  omega

theorem learn_paid {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (formula : CNFFormula n) : (learn basis formula).paidCells ≤ learnBudget n formula.length (Extract.literalCount formula) := by
  have sourceCost := data_cells basis valid formula _ (Nat.le_refl _)
  have body := learnFrom_paid basis valid formula
  change (data basis formula).cells+(learnFrom (data basis formula).value).paidCells ≤ _
  rw [data_value]
  unfold learnBudget
  omega

structure Execution where
  value : Result
  paidCells : Nat
  deriving Repr

def advance {n : Nat} (formula : CNFFormula n) : Result → Execution
  | .contradiction => ⟨.contradiction,1⟩
  | .basis basis =>
      let generated := learn basis formula
      let returned := EliminateCost.runFrom (.basis basis) generated.value
      ⟨returned.result,generated.paidCells+returned.cells+
        2*(AffineCarrier.cellSize basis+rowsCells generated.value+AffineCarrier.resultSize returned.result)+5⟩

theorem advance_value {n : Nat} (formula : CNFFormula n) (result : Result) :
    (advance formula result).value=Atoms.advance formula result := by
  cases result <;> simp only [advance,learn_value,EliminateCost.runFrom_result,Atoms.advance]

def advanceBudget (n clauses literals : Nat) : Nat :=
  learnBudget n clauses literals+
    returnRowsBound n clauses*(2*n+EliminateCost.insertCellBudget n+8)+
    4*(AffineCarrier.Cost.cellBound n+1)+6

theorem advance_paid {n : Nat} (formula : CNFFormula n) (result : Result)
    (valid : result.triangular ∧ result.within n) :
    (advance formula result).paidCells ≤ advanceBudget n formula.length (Extract.literalCount formula) := by
  cases result with
  | contradiction => simp only [advance,advanceBudget]; omega
  | basis basis =>
      have generated := learn_paid basis valid formula
      have stored := StrongFeedbackScale.atoms_learn_storage basis valid.2 formula
      have measures := AffineCarrier.Cost.row_measures (Atoms.learn basis formula)
      have inside : RowsWithin n (Atoms.learn basis formula) :=
        fun row member => (Atoms.learn_valid basis valid.2 formula row member).2
      simp only [advance,learn_value]
      generalize learned : Atoms.learn basis formula = rows at *
      have returned := EliminateCost.runFrom_cells n (.basis basis) valid.1 valid.2 rows inside
      have resultValid : (eliminateFrom (.basis basis) rows).triangular ∧
          (eliminateFrom (.basis basis) rows).within n :=
        ⟨eliminateFrom_triangular _ valid.1 _,eliminateFrom_within n _ valid.2 _ inside⟩
      have inputSize := AffineCarrier.Cost.cell_size n basis valid.1 valid.2
      have outputSize := AffineCarrier.Cost.result_size n _ resultValid.1 resultValid.2
      have rowBound := measures.1.trans stored
      have termBound := measures.2.trans stored
      have gaussian : (EliminateCost.runFrom (.basis basis) rows).cells ≤
          returnRowsBound n formula.length*(2*n+EliminateCost.insertCellBudget n+6)+1 := by
        apply returned.trans
        unfold returnRowsBound
        nlinarith [Nat.mul_le_mul_right (2*n+5) termBound,
          Nat.mul_le_mul_right (EliminateCost.insertCellBudget n+1) rowBound]
      simp only [EliminateCost.runFrom_result]
      unfold advanceBudget returnRowsBound at *
      nlinarith

def joint {n : Nat} (formula : CNFFormula n) (result : Result) : Execution :=
  let propagated := AffineFeedbackCost.Propagation.update formula result
  let atoms := advance formula propagated.value
  ⟨atoms.value,propagated.cells+atoms.paidCells+2⟩

theorem joint_value {n : Nat} (formula : CNFFormula n) (result : Result) :
    (joint formula result).value=JointFeedback.step formula result := by
  simp only [joint,advance_value,AffineFeedbackCost.Propagation.update_value,JointFeedback.step]

def jointBudget (n clauses literals : Nat) : Nat :=
  AffineFeedbackCost.Propagation.updateBudget n clauses literals+advanceBudget n clauses literals+2

theorem joint_paid {n : Nat} (formula : CNFFormula n) (result : Result)
    (valid : result.triangular ∧ result.within n) :
    (joint formula result).paidCells ≤ jointBudget n formula.length (Extract.literalCount formula) := by
  have first := AffineFeedbackCost.Propagation.update_cells formula result valid
  have after : (AffineFeedbackCost.Propagation.update formula result).value.triangular ∧
      (AffineFeedbackCost.Propagation.update formula result).value.within n := by
    rw [AffineFeedbackCost.Propagation.update_value]
    exact ⟨Propagation.update_triangular formula result valid.1,Propagation.update_within formula result valid.2⟩
  have second := advance_paid formula _ after
  exact Nat.add_le_add_right (Nat.add_le_add first second) 2

def iterate {n : Nat} (formula : CNFFormula n) : Nat → Result → Execution
  | 0,result => ⟨result,1⟩
  | fuel+1,result =>
      let next := joint formula result
      let tail := iterate formula fuel next.value
      ⟨tail.value,next.paidCells+tail.paidCells+2⟩

theorem iterate_value {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result) :
    (iterate formula fuel result).value=JointFeedback.iterate formula fuel result := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih => simp only [iterate,ih,joint_value,JointFeedback.iterate]

theorem iterate_paid {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result)
    (valid : result.triangular ∧ result.within n) :
    (iterate formula fuel result).paidCells ≤ fuel*(jointBudget n formula.length (Extract.literalCount formula)+2)+1 := by
  induction fuel generalizing result with
  | zero => simp [iterate]
  | succ fuel ih =>
      have first := joint_paid formula result valid
      have nextValid := JointFeedback.step_invariants formula result valid.2 valid.1
      rw [← joint_value] at nextValid
      have tail := ih _ nextValid.symm
      simp only [iterate]
      nlinarith

def branch {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool) : Execution :=
  let inserted := EliminateCost.insert result ⟨[i.val],value⟩
  let generated := iterate formula (n+1) inserted.result
  ⟨generated.value,inserted.cells+generated.paidCells+
    2*(AffineCarrier.resultSize result+AffineCarrier.resultSize inserted.result+
      AffineCarrier.resultSize generated.value)+8⟩

theorem branch_value {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool) :
    (branch formula result i value).value=BranchImage.branch formula result i value := by
  simp only [branch,iterate_value,EliminateCost.insert_result,BranchImage.branch]

def branchBudget (n clauses literals : Nat) : Nat :=
  2*n+EliminateCost.insertCellBudget n+5+
    (n+1)*(jointBudget n clauses literals+2)+1+6*(AffineCarrier.Cost.cellBound n+1)+8

theorem branch_paid {n : Nat} (formula : CNFFormula n) (result : Result) (valid : result.triangular ∧ result.within n)
    (i : Fin n) (value : Bool) :
    (branch formula result i value).paidCells ≤ branchBudget n formula.length (Extract.literalCount formula) := by
  have rowInside : InterferenceProgram.Parity.Within n [i.val] := by
    intro j member
    simpa only [List.mem_singleton] using (List.mem_singleton.mp member ▸ i.isLt)
  have inserted := EliminateCost.insert_cells n result valid.1 valid.2 ⟨[i.val],value⟩ rowInside
  have nextValid : (EliminateCost.insert result ⟨[i.val],value⟩).result.triangular ∧
      (EliminateCost.insert result ⟨[i.val],value⟩).result.within n := by
    rw [EliminateCost.insert_result]
    exact ⟨Result.insert_triangular result valid.1 _,Result.insert_within n result valid.2 _ rowInside⟩
  have generated := iterate_paid formula (n+1) _ nextValid
  have inputSize := AffineCarrier.Cost.result_size n result valid.1 valid.2
  have intermediate := AffineCarrier.Cost.result_size n _ nextValid.1 nextValid.2
  have lastValid := JointFeedback.iterate_invariants formula (n+1) _ nextValid.2 nextValid.1
  rw [← iterate_value] at lastValid
  have outputSize := AffineCarrier.Cost.result_size n _ lastValid.2 lastValid.1
  simp only [List.length_cons,List.length_nil] at inserted
  simp only [branch,branchBudget]
  omega

theorem branch_holds {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool)
    (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (branch formula result i value).value.holds assignment)=
      (CNFFormula.eval formula assignment && result.holds assignment && (assignment i.val==value)) := by
  rw [branch_value]
  exact BranchImage.branch_holds formula result i value assignment

end SaturationMonoid.ComplexityProjection.SATSource.AffineAtomFeedbackCost

import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.RelationExtractionCost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineRelationExtractionCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowCells rowsCells)
open InterferenceProgram

def unitClause {n : Nat} : CNFClause n → Counted (List Row)
  | [] => ⟨[⟨[],true⟩],7⟩
  | [literal] => ⟨[⟨[literal.var.val],literal.positive⟩],10⟩
  | _::_::_ => ⟨[],4⟩

def unitRows {n : Nat} (formula : CNFFormula n) : Counted (List Row) :=
  CapacityMatching.RowCost.gather unitClause formula

theorem unitRows_value {n : Nat} (formula : CNFFormula n) : (unitRows formula).value=Atoms.unitRows formula := by
  rw [unitRows,CapacityMatching.RowCost.gather_value]
  apply congrArg (List.flatMap · formula)
  funext clause
  cases clause with
  | nil => rfl
  | cons literal rest => cases rest <;> rfl

theorem unitClause_cells {n : Nat} (clause : CNFClause n) : (unitClause clause).cells ≤ 10 := by
  cases clause with
  | nil => simp [unitClause]
  | cons literal rest => cases rest <;> simp [unitClause]

theorem unitClause_storage {n : Nat} (clause : CNFClause n) : rowsCells (unitClause clause).value ≤ 3 := by
  cases clause with
  | nil => simp [unitClause,rowsCells,rowCells]
  | cons literal rest => cases rest <;> simp [unitClause,rowsCells,rowCells]

def unitsBudget (count : Nat) : Nat := count*(10+(count+1)*3+5)+1

theorem unitRows_cells {n : Nat} (formula : CNFFormula n) : (unitRows formula).cells ≤ unitsBudget formula.length :=
  CapacityMatching.RowCost.gather_cells unitClause formula 10 3
    (fun clause _ => unitClause_cells clause) (fun clause _ => unitClause_storage clause)

theorem unitRows_size {n : Nat} (formula : CNFFormula n) : rowsCells (unitRows formula).value ≤ 3*formula.length := by
  rw [unitRows_value]
  exact AffineAtomFeedbackCost.unitRows_storage formula

def templateSize {n : Nat} : CNFClause n → Nat
  | [_,_] => 17
  | [_,_,_] => 45
  | _ => 0

theorem binary_template_size {n : Nat} (a b : CNFLiteral n) : size (Extract.binaryBlock a b)=17 := by
  simp [size,CapacityMatching.RowCost.formulaCells,Extract.literalCount,Extract.binaryBlock]

theorem ternary_template_size {n : Nat} (a b c : CNFLiteral n) : size (CouncilParityProbe.parityBlock a b c)=45 := by
  simp [size,CapacityMatching.RowCost.formulaCells,Extract.literalCount,CouncilParityProbe.parityBlock]

theorem templateSize_bound {n : Nat} (clause : CNFClause n) : templateSize clause ≤ 45 := by
  unfold templateSize
  split <;> omega

theorem inspect_arity {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) (row : Row)
    (found : (Extract.inspect formula clause).row=some row) : clause.length ≤ 3 := by
  unfold Extract.inspect at found
  split at found <;> simp_all

/-- The successful old inspection normalizes exactly the addresses of its source anchor. -/
def normalizationCells {n : Nat} (clause : CNFClause n) : Option Row → Nat
  | none => 0
  | some row => Table.mergeVisits (clause.map (fun literal => literal.var.val)) []+2*rowCells row+2

theorem normalizationCells_bound {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) :
    normalizationCells clause (Extract.inspect formula clause).row ≤ 6*n+28 := by
  cases found : (Extract.inspect formula clause).row with
  | none => simp [normalizationCells]
  | some row =>
      have length := inspect_arity formula clause row found
      have valid := Extract.inspect_wellFormed formula clause row found
      have rowLength := valid.2.1
      have inside : Parity.Within n (clause.map (fun literal => literal.var.val)) := by
        intro i member
        obtain ⟨literal,_,rfl⟩ := List.mem_map.mp member
        exact literal.var.isLt
      have merged := Table.mergeVisits_bound n _ [] inside (by simp) (by simp [Parity.Within])
      simp only [List.length_map] at merged
      simp only [normalizationCells,rowCells]
      nlinarith [Nat.mul_le_mul_right (2*n+5) length]

theorem inspection_payload {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) :
    payloadSize rowCells (Extract.inspect formula clause).row ≤ 6 := by
  cases found : (Extract.inspect formula clause).row with
  | none => simp [payloadSize]
  | some row =>
      have valid := Extract.inspect_wellFormed formula clause row found
      have rowLength := valid.2.1
      simp only [payloadSize,rowCells]
      omega

def inspect {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) : Counted (Option Row) :=
  let original := Extract.inspect formula clause
  ⟨original.row,original.visits+normalizationCells clause original.row+
    2*(size formula+3*clause.length+1+templateSize clause+payloadSize rowCells original.row)+9⟩

theorem inspect_value {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) :
    (inspect formula clause).value=(Extract.inspect formula clause).row := rfl

def inspectionBudget (width clauses literals query : Nat) : Nat :=
  56*literals+40*clauses+41+6*width+28+
    2*(3*literals+2*clauses+1+3*query+1+45+6)+9

theorem inspect_cells {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) :
    (inspect formula clause).cells ≤ inspectionBudget n formula.length (Extract.literalCount formula) clause.length := by
  have checked := Extract.inspect_visits formula clause
  have normalized := normalizationCells_bound formula clause
  have template := templateSize_bound clause
  have payload := inspection_payload formula clause
  simp only [inspect,inspectionBudget,size,CapacityMatching.RowCost.formulaCells]
  omega

def extractOne {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) : Counted (List Row) :=
  let checked := inspect formula clause
  ⟨checked.value.toList,checked.cells+2*rowsCells checked.value.toList+3⟩

theorem extractOne_storage {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) :
    rowsCells (extractOne formula clause).value ≤ 5 := by
  cases found : (Extract.inspect formula clause).row with
  | none => simp [extractOne,inspect_value,found,rowsCells]
  | some row =>
      have valid := Extract.inspect_wellFormed formula clause row found
      have rowLength := valid.2.1
      simp only [extractOne,inspect_value,found,Option.toList_some,CapacityMatching.RowCost.rowsCells_cons,
        CapacityMatching.RowCost.rowsCells_nil,rowCells]
      omega

def extract {n : Nat} (formula : CNFFormula n) : Counted (List Row) :=
  CapacityMatching.RowCost.gather (extractOne formula) formula

theorem gather_extract_value {n : Nat} (formula anchors : CNFFormula n) :
    (CapacityMatching.RowCost.gather (extractOne formula) anchors).value=(Extract.scan formula anchors).rows := by
  induction anchors with
  | nil => rfl
  | cons clause rest ih =>
      simp only [CapacityMatching.RowCost.gather,CapacityMatching.RowCost.append,extractOne,inspect_value,ih,Extract.scan]

theorem extract_value {n : Nat} (formula : CNFFormula n) : (extract formula).value=Extract.extract formula :=
  gather_extract_value formula formula

def extractionBudget (width clauses literals : Nat) : Nat :=
  clauses*(inspectionBudget width clauses literals literals+13+(clauses+1)*5+5)+1

theorem extract_cells {n : Nat} (formula : CNFFormula n) :
    (extract formula).cells ≤ extractionBudget n formula.length (Extract.literalCount formula) := by
  apply CapacityMatching.RowCost.gather_cells (extractOne formula) formula
    (inspectionBudget n formula.length (Extract.literalCount formula) (Extract.literalCount formula)+13) 5
  · intro clause member
    have length : clause.length ≤ Extract.literalCount formula := List.le_sum_of_mem (List.mem_map.mpr ⟨clause,member,rfl⟩)
    have inspected := inspect_cells formula clause
    have cost : (inspect formula clause).cells ≤
        inspectionBudget n formula.length (Extract.literalCount formula) (Extract.literalCount formula) := by
      apply inspected.trans
      unfold inspectionBudget
      gcongr
    have stored := extractOne_storage formula clause
    simp only [extractOne] at stored ⊢
    omega
  · intro clause _
    exact extractOne_storage formula clause

theorem extract_storage {n : Nat} (formula : CNFFormula n) : rowsCells (extract formula).value ≤ 5*formula.length := by
  have copied := CapacityMatching.RowCost.gather_storage (extractOne formula) formula 5 (fun clause _ => extractOne_storage formula clause)
  simpa only [extract,Nat.mul_comm] using copied

def equations {n : Nat} (formula : CNFFormula n) : Counted (List Row) :=
  let units := unitRows formula
  let extracted := extract formula
  let joined := CapacityMatching.RowCost.append units.value extracted.value
  ⟨joined.value,units.cells+extracted.cells+joined.cells+2*(size formula+rowsCells joined.value)+5⟩

theorem equations_value {n : Nat} (formula : CNFFormula n) : (equations formula).value=Atoms.equations formula := by
  simp only [equations,CapacityMatching.RowCost.append,unitRows_value,extract_value,Atoms.equations]

def equationsBudget (width clauses literals : Nat) : Nat :=
  unitsBudget clauses+extractionBudget width clauses literals+32*clauses+2*(3*literals+2*clauses+1)+10

theorem equations_cells {n : Nat} (formula : CNFFormula n) :
    (equations formula).cells ≤ equationsBudget n formula.length (Extract.literalCount formula) := by
  have units := unitRows_cells formula
  have unitSize := unitRows_size formula
  have extracted := extract_cells formula
  have extractSize := extract_storage formula
  simp only [equations,CapacityMatching.RowCost.append,CapacityMatching.RowCost.rowsCells_append,
    equationsBudget,size,CapacityMatching.RowCost.formulaCells]
  omega

theorem equations_size {n : Nat} (formula : CNFFormula n) : rowsCells (equations formula).value ≤ 8*formula.length := by
  rw [equations_value]
  exact AffineAtomFeedbackCost.equations_storage formula

theorem binary_normalization_work {n : Nat} (formula : CNFFormula n) (a b : CNFLiteral n) :
    normalizationCells [a,b] (Extract.inspect formula [a,b]).row=
      if (Extract.allBlocks formula (Extract.binaryBlock a b)).accepted then
        (CapacityMatching.RowCost.normalize ⟨[a.var.val,b.var.val],!(a.positive ^^ b.positive)⟩).cells else 0 := by
  simp only [Extract.inspect]
  split <;> rfl

theorem ternary_normalization_work {n : Nat} (formula : CNFFormula n) (a b c : CNFLiteral n) :
    normalizationCells [a,b,c] (Extract.inspect formula [a,b,c]).row=
      if (Extract.allBlocks formula (CouncilParityProbe.parityBlock a b c)).accepted then
        (CapacityMatching.RowCost.normalize ⟨[a.var.val,b.var.val,c.var.val],a.positive ^^ (b.positive ^^ c.positive)⟩).cells else 0 := by
  simp only [Extract.inspect]
  split <;> rfl

attribute [local irreducible] AffineAtomFeedbackCost.data AffineAtomFeedbackCost.front

def middle (source : AffineAtomFeedbackCost.Data) : Counted (List Row) :=
  let prepared := AffineAtomFeedbackCost.front source
  let normalized := reduce prepared.formula
  let generated := equations normalized.value
  let decoded := CapacityMatching.RowCost.decodeRows prepared.table generated.value
  ⟨decoded.value,prepared.cells+normalized.cells+generated.cells+decoded.cells+
    2*(AffineAtomFeedbackCost.dataSize source+size normalized.value+rowsCells generated.value+rowsCells decoded.value)+7⟩

def extra (source : AffineAtomFeedbackCost.Data) : Nat :=
  let prepared := AffineAtomFeedbackCost.front source
  let normalized := reduce prepared.formula
  normalized.cells+(equations normalized.value).cells

theorem middle_value (source : AffineAtomFeedbackCost.Data) :
    (middle source).value=(AffineAtomFeedbackCost.learnFrom source).value := by
  simp only [middle,AffineAtomFeedbackCost.learnFrom,reduce_value,equations_value]

theorem middle_cells (source : AffineAtomFeedbackCost.Data) :
    (middle source).cells=(AffineAtomFeedbackCost.learnFrom source).paidCells+extra source := by
  simp only [middle,extra,AffineAtomFeedbackCost.learnFrom,reduce_value,equations_value,size]
  ring

def compiledBound (clauses literals : Nat) : Nat := 3*(literals+1)+2*(clauses+1)+1
def extraBudget (clauses literals : Nat) : Nat :=
  reduceBudget (compiledBound clauses literals)+equationsBudget (literals+1) (clauses+1) (literals+1)

theorem reduceBudget_mono (small large : Nat) (bound : small ≤ large) : reduceBudget small ≤ reduceBudget large := by
  unfold reduceBudget roundBudget
  have normalized := normalizeBudget_mono small large bound
  have scanned := scanBudget_mono small large bound
  have updated := updateBudget_mono small large bound
  gcongr

theorem equationsBudget_mono (q Q m M ell E : Nat) (width : q ≤ Q) (clauses : m ≤ M) (literals : ell ≤ E) :
    equationsBudget q m ell ≤ equationsBudget Q M E := by
  unfold equationsBudget unitsBudget extractionBudget inspectionBudget
  gcongr

theorem extra_cells {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    extra (Atoms.data basis formula) ≤ extraBudget formula.length (Extract.literalCount formula) := by
  have inputSize : size (AffineAtomFeedbackCost.front (Atoms.data basis formula)).formula=
      compiledBound formula.length (Extract.literalCount formula) := by
    rw [AffineAtomFeedbackCost.front_formula]
    simp only [size,CapacityMatching.RowCost.formulaCells,StrongFeedbackScale.compile_literals,
      Atoms.compile_length,Atoms.data_length,Atoms.data_literals,← StrongFeedbackScale.literalCount_flatten,compiledBound]
  have normalized := reduce_cells (AffineAtomFeedbackCost.front (Atoms.data basis formula)).formula
  rw [inputSize] at normalized
  have generated := equations_cells (reduce (AffineAtomFeedbackCost.front (Atoms.data basis formula)).formula).value
  have clauses : (reduce (AffineAtomFeedbackCost.front (Atoms.data basis formula)).formula).value.length ≤ formula.length+1 := by
    rw [reduce_value,AffineAtomFeedbackCost.front_formula]
    exact (StrongFeedbackScale.atom_formula_size basis formula).1
  have literals : Extract.literalCount (reduce (AffineAtomFeedbackCost.front (Atoms.data basis formula)).formula).value ≤
      Extract.literalCount formula+1 := by
    rw [reduce_value,AffineAtomFeedbackCost.front_formula]
    exact (StrongFeedbackScale.atom_formula_size basis formula).2
  have bound := generated.trans (equationsBudget_mono _ _ _ _ _ _ (StrongFeedbackScale.atom_width basis formula) clauses literals)
  exact Nat.add_le_add normalized bound

def learn {n : Nat} (basis : List Row) (formula : CNFFormula n) : Counted (List Row) :=
  let source := AffineAtomFeedbackCost.data basis formula
  let result := middle source.value
  ⟨result.value,source.cells+result.cells⟩

theorem learn_value {n : Nat} (basis : List Row) (formula : CNFFormula n) : (learn basis formula).value=Atoms.learn basis formula := by
  simp only [learn,middle_value]
  exact AffineAtomFeedbackCost.learn_value basis formula

theorem learn_counter {n : Nat} (basis : List Row) (formula : CNFFormula n) :
    (learn basis formula).cells=(AffineAtomFeedbackCost.learn basis formula).paidCells+extra (Atoms.data basis formula) := by
  simp only [learn,middle_cells,AffineAtomFeedbackCost.learn,AffineAtomFeedbackCost.data_value]
  omega

def learnBudget (n clauses literals : Nat) : Nat :=
  AffineAtomFeedbackCost.learnBudget n clauses literals+extraBudget clauses literals

theorem learn_cells {n : Nat} (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (formula : CNFFormula n) :
    (learn basis formula).cells ≤ learnBudget n formula.length (Extract.literalCount formula) := by
  rw [learn_counter]
  exact Nat.add_le_add (AffineAtomFeedbackCost.learn_paid basis valid formula) (extra_cells basis formula)

def advance {n : Nat} (formula : CNFFormula n) : Result → Counted Result
  | .contradiction => ⟨.contradiction,1⟩
  | .basis basis =>
      let generated := learn basis formula
      let returned := EliminateCost.runFrom (.basis basis) generated.value
      ⟨returned.result,generated.cells+returned.cells+
        2*(AffineCarrier.cellSize basis+rowsCells generated.value+AffineCarrier.resultSize returned.result)+5⟩

theorem advance_value {n : Nat} (formula : CNFFormula n) (result : Result) : (advance formula result).value=Atoms.advance formula result := by
  cases result <;> simp only [advance,learn_value,EliminateCost.runFrom_result,Atoms.advance]

theorem advance_counter {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (advance formula (.basis basis)).cells=(AffineAtomFeedbackCost.advance formula (.basis basis)).paidCells+
      extra (Atoms.data basis formula) := by
  simp only [advance,learn_counter,learn_value,AffineAtomFeedbackCost.advance,AffineAtomFeedbackCost.learn_value]
  ring

def advanceBudget (n clauses literals : Nat) : Nat :=
  AffineAtomFeedbackCost.advanceBudget n clauses literals+extraBudget clauses literals

theorem advance_cells {n : Nat} (formula : CNFFormula n) (result : Result) (valid : result.triangular ∧ result.within n) :
    (advance formula result).cells ≤ advanceBudget n formula.length (Extract.literalCount formula) := by
  cases result with
  | contradiction =>
      have old := AffineAtomFeedbackCost.advance_paid formula (.contradiction) valid
      simp only [advance,AffineAtomFeedbackCost.advance,advanceBudget] at *
      omega
  | basis basis =>
      rw [advance_counter]
      exact Nat.add_le_add (AffineAtomFeedbackCost.advance_paid formula (.basis basis) valid) (extra_cells basis formula)

def joint {n : Nat} (formula : CNFFormula n) (result : Result) : Counted Result :=
  let propagated := AffineFeedbackCost.Propagation.update formula result
  let atoms := advance formula propagated.value
  ⟨atoms.value,propagated.cells+atoms.cells+2⟩

theorem joint_value {n : Nat} (formula : CNFFormula n) (result : Result) : (joint formula result).value=JointFeedback.step formula result := by
  simp only [joint,advance_value,AffineFeedbackCost.Propagation.update_value,JointFeedback.step]

def jointBudget (n clauses literals : Nat) : Nat :=
  AffineFeedbackCost.Propagation.updateBudget n clauses literals+advanceBudget n clauses literals+2

theorem joint_cells {n : Nat} (formula : CNFFormula n) (result : Result) (valid : result.triangular ∧ result.within n) :
    (joint formula result).cells ≤ jointBudget n formula.length (Extract.literalCount formula) := by
  have first := AffineFeedbackCost.Propagation.update_cells formula result valid
  have next : (AffineFeedbackCost.Propagation.update formula result).value.triangular ∧
      (AffineFeedbackCost.Propagation.update formula result).value.within n := by
    rw [AffineFeedbackCost.Propagation.update_value]
    exact ⟨Propagation.update_triangular formula result valid.1,Propagation.update_within formula result valid.2⟩
  exact Nat.add_le_add_right (Nat.add_le_add first (advance_cells formula _ next)) 2

def iterate {n : Nat} (formula : CNFFormula n) : Nat → Result → Counted Result
  | 0,result => ⟨result,1⟩
  | fuel+1,result =>
      let next := joint formula result
      let tail := iterate formula fuel next.value
      ⟨tail.value,next.cells+tail.cells+2⟩

theorem iterate_value {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result) :
    (iterate formula fuel result).value=JointFeedback.iterate formula fuel result := by
  induction fuel generalizing result with
  | zero => rfl
  | succ fuel ih => simp only [iterate,ih,joint_value,JointFeedback.iterate]

theorem iterate_cells {n : Nat} (formula : CNFFormula n) (fuel : Nat) (result : Result) (valid : result.triangular ∧ result.within n) :
    (iterate formula fuel result).cells ≤ fuel*(jointBudget n formula.length (Extract.literalCount formula)+2)+1 := by
  induction fuel generalizing result with
  | zero => simp [iterate]
  | succ fuel ih =>
      have first := joint_cells formula result valid
      have next := JointFeedback.step_invariants formula result valid.2 valid.1
      rw [← joint_value] at next
      have tail := ih _ next.symm
      simp only [iterate]
      nlinarith

def branch {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool) : Counted Result :=
  let inserted := EliminateCost.insert result ⟨[i.val],value⟩
  let generated := iterate formula (n+1) inserted.result
  ⟨generated.value,inserted.cells+generated.cells+
    2*(AffineCarrier.resultSize result+AffineCarrier.resultSize inserted.result+AffineCarrier.resultSize generated.value)+8⟩

theorem branch_value {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool) :
    (branch formula result i value).value=BranchImage.branch formula result i value := by
  simp only [branch,iterate_value,EliminateCost.insert_result,BranchImage.branch]

def branchBudget (n clauses literals : Nat) : Nat :=
  2*n+EliminateCost.insertCellBudget n+5+(n+1)*(jointBudget n clauses literals+2)+1+
    6*(AffineCarrier.Cost.cellBound n+1)+8

theorem branch_cells {n : Nat} (formula : CNFFormula n) (result : Result) (valid : result.triangular ∧ result.within n)
    (i : Fin n) (value : Bool) : (branch formula result i value).cells ≤ branchBudget n formula.length (Extract.literalCount formula) := by
  have inside : Parity.Within n [i.val] := by
    intro j member
    have same := List.mem_singleton.mp member
    exact same ▸ i.isLt
  have inserted := EliminateCost.insert_cells n result valid.1 valid.2 ⟨[i.val],value⟩ inside
  have next : (EliminateCost.insert result ⟨[i.val],value⟩).result.triangular ∧
      (EliminateCost.insert result ⟨[i.val],value⟩).result.within n := by
    rw [EliminateCost.insert_result]
    exact ⟨Result.insert_triangular result valid.1 _,Result.insert_within n result valid.2 _ inside⟩
  have generated := iterate_cells formula (n+1) _ next
  have inputSize := AffineCarrier.Cost.result_size n result valid.1 valid.2
  have middleSize := AffineCarrier.Cost.result_size n _ next.1 next.2
  have final := JointFeedback.iterate_invariants formula (n+1) _ next.2 next.1
  rw [← iterate_value] at final
  have outputSize := AffineCarrier.Cost.result_size n _ final.2 final.1
  simp only [List.length_cons,List.length_nil] at inserted
  simp only [branch,branchBudget]
  omega

theorem branch_holds {n : Nat} (formula : CNFFormula n) (result : Result) (i : Fin n) (value : Bool) (assignment : Nat → Bool) :
    (CNFFormula.eval formula assignment && (branch formula result i value).value.holds assignment)=
      (CNFFormula.eval formula assignment && result.holds assignment && (assignment i.val==value)) := by
  rw [branch_value]
  exact BranchImage.branch_holds formula result i value assignment

end SaturationMonoid.ComplexityProjection.SATSource.AffineRelationExtractionCost

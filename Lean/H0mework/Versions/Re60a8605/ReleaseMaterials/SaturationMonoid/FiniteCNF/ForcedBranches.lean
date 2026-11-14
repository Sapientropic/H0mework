import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalSourceCost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ForcedBranches
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open FunctionalSubstitution (Instruction)
open CapacityMatching.RowCost (rowCells rowsCells)
open FunctionalSchedule.Cost (inputSize instructionSize)
abbrev Counted := CapacityMatching.SourceCost.Counted

def force (table : Array Row) (i : Nat) (value : Bool) : Counted (List Instruction) :=
  let row := table.getD i Gates.zeroRow
  match row.vars with
  | [] => ⟨[],2*AffineCollect.tableSize table+8⟩
  | address::rest =>
      let body := ConditionalCandidateCost.Code.compileRow ⟨rest,row.rhs ^^ value⟩
      ⟨[⟨address,body.value⟩],body.cells+
        2*(AffineCollect.tableSize table+rowCells row+body.value.code.size)+16⟩

private theorem solve_value (r a t v : Bool) (source : (r ^^ (a ^^ t))=v) : a=((r ^^ v) ^^ t) := by
  cases r <;> cases a <;> cases t <;> cases v <;> simp_all

private theorem not_rejected (a b : Bool) (source : false=(a==b)) : a= !b := by
  cases a <;> cases b <;> simp_all

theorem force_fixes (table : Array Row) (i : Nat) (value : Bool) (point : Nat → Bool)
    (source : Gates.coordinate table point i=value) (item : Instruction)
    (member : item ∈ (force table i value).value) : item.bind point=point := by
  have equation := source
  rw [Table.coordinate_getD] at equation
  cases shape : (table.getD i Gates.zeroRow).vars with
  | nil => simp only [force,shape,List.not_mem_nil] at member
  | cons address rest =>
    simp only [force,shape,List.mem_singleton] at member
    subst item
    apply FunctionalSubstitution.bind_fixes
    rw [ConditionalCandidateCost.Code.compileRow_value,Gates.eval_compileRow,truth_bit]
    simp only [Gates.value,Row.eval,shape,Parity.eval] at equation ⊢
    exact solve_value _ _ _ _ equation

theorem rejected_value {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (i : Fin n) (rejected : Bool)
    (impossible : BranchImage.branch formula (.basis basis) i rejected=.contradiction)
    (point : Nat → Bool) (accepted : CNFFormula.eval formula point=true)
    (relations : holds basis point=true) : point i.val= !rejected := by
  have branch := BranchImage.branch_holds formula (.basis basis) i rejected point
  rw [impossible,accepted] at branch
  simp only [Result.holds,relations,Bool.true_and] at branch
  exact not_rejected _ _ branch

def branch {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (table : Array Row) (free : Nat) (i : Fin n) : Counted (List Instruction) :=
  let left := AffineRelationExtractionCost.branch formula (.basis basis) i false
  let right := AffineRelationExtractionCost.branch formula (.basis basis) i true
  let ends := left.cells+right.cells+
    2*(AffineCarrier.cellSize basis+AffineCarrier.resultSize left.value+AffineCarrier.resultSize right.value)+8
  match left.value,right.value with
  | .contradiction,_ =>
      let output := force table i.val true
      ⟨output.value,ends+output.cells+2*inputSize output.value+8⟩
  | .basis _,.contradiction =>
      let output := force table i.val false
      ⟨output.value,ends+output.cells+2*inputSize output.value+8⟩
  | .basis a,.basis b =>
      let first := ConditionalCandidateCost.project table a
      let second := ConditionalCandidateCost.project table b
      let output := ConditionalCandidateCost.makeCalls table i.val first.value second.value (List.finRange free)
      ⟨output.value,ends+first.cells+second.cells+output.cells+
        2*(rowsCells a+rowsCells b+rowsCells first.value+rowsCells second.value+inputSize output.value)+3*free+12⟩

theorem branch_entails {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (i : Fin n) (point : Nat → Bool)
    (accepted : CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true)
    (item : Instruction)
    (member : item ∈ (branch formula basis (Table.coordinates n basis) (freeIndices n basis).length i).value) :
    item.bind point=point := by
  have relations : holds basis (Gates.coordinate (Table.coordinates n basis) point)=true := by
    rw [Table.coordinates_value n basis valid.2]
    exact fill_holds basis valid.1 _
  simp only [branch,AffineRelationExtractionCost.branch_value] at member
  cases left : BranchImage.branch formula (.basis basis) i false with
  | contradiction =>
      simp only [left] at member
      exact force_fixes _ _ true point
        (rejected_value formula basis i false left _ accepted relations) item member
  | basis a =>
      cases right : BranchImage.branch formula (.basis basis) i true with
      | contradiction =>
          simp only [left,right] at member
          exact force_fixes _ _ false point
            (rejected_value formula basis i true right _ accepted relations) item member
      | basis b =>
          apply ConditionalPivot.branchCandidates_fixes formula basis valid.2 valid.1 i item ?_ point accepted
          simp only [left,right,ConditionalCandidateCost.makeCalls_value,
            ConditionalCandidateCost.project_value] at member
          change item ∈ (List.finRange (freeIndices n basis).length).map
            (ConditionalPivot.instruction n basis (Table.coordinates n basis) i
              (ConditionalPivot.project (Table.coordinates n basis) a)
              (ConditionalPivot.project (Table.coordinates n basis) b)) at member
          simpa only [ConditionalPivot.branchCandidates,ConditionalPivot.split,left,right] using member

def branches {n : Nat} (formula : CNFFormula n) (basis : List Row) (table : Array Row) (free : Nat) :
    List (Fin n) → Counted (List Instruction)
  | [] => ⟨[],1⟩
  | i::rest =>
      let first := branch formula basis table free i
      let tail := branches formula basis table free rest
      ⟨first.value++tail.value,first.cells+tail.cells+2*(inputSize first.value+inputSize tail.value)+8⟩

theorem branches_entails {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (indices : List (Fin n)) (point : Nat → Bool)
    (accepted : CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true)
    (item : Instruction)
    (member : item ∈ (branches formula basis (Table.coordinates n basis) (freeIndices n basis).length indices).value) :
    item.bind point=point := by
  induction indices with
  | nil => simp [branches] at member
  | cons i rest ih =>
      rcases List.mem_append.mp member with member | member
      · exact branch_entails formula basis valid i point accepted item member
      · exact ih member

def generate {n : Nat} (formula : CNFFormula n) (basis : List Row) : Counted (List Instruction) :=
  let table := ConditionalCandidateCost.coordinates n basis
  let free := ConditionalCandidateCost.width n basis
  let functional := ConditionalCandidateCost.Functional.candidates table.value formula
  let conditional := branches formula basis table.value free.value (List.finRange n)
  ⟨functional.value++conditional.value,table.cells+free.cells+functional.cells+conditional.cells+
    2*(AffineCollect.tableSize table.value+inputSize functional.value+inputSize conditional.value)+2*n+20⟩

theorem generate_entails {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool)
    (accepted : truth ((Acceptance.compile (Table.coordinates n basis) formula).eval point)=true)
    (item : Instruction) (member : item ∈ (generate formula basis).value) : item.bind point=point := by
  rcases List.mem_append.mp member with functional | conditional
  · apply FunctionalPivot.candidates_entails formula basis point accepted item
    simpa only [ConditionalCandidateCost.Functional.candidates_value,ConditionalCandidateCost.coordinates_value,
      FunctionalPivot.candidates] using functional
  · apply branches_entails formula basis valid (List.finRange n) point ?_ item conditional
    simpa only [Acceptance.eval_compile,truth_bit] using accepted

theorem generated_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (FunctionalAffine.legal (FunctionalFeedback.generate (generate formula basis).value) point &&
      truth ((FunctionalFeedback.prepare (generate formula basis).value
        (Acceptance.compile (Table.coordinates n basis) formula)).eval point))=
      CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  rw [FunctionalFeedback.prepare_read _ _ (generate_entails formula basis valid),Acceptance.eval_compile,truth_bit]

end SaturationMonoid.ComplexityProjection.SATSource.ForcedBranches

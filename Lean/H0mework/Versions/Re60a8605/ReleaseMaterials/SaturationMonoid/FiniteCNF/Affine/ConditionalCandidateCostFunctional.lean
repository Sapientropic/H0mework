import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.ConditionalCandidateCostCode

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ConditionalCandidateCost.Functional
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram
open FunctionalRelations (Relation)
open FunctionalSubstitution (Instruction)
open FunctionalSchedule.Cost (instructionSize inputSize)
abbrev Counted := CapacityMatching.SourceCost.Counted

def relationOne {n : Nat} (formula : CNFFormula n) (clause : CNFClause n) : Counted (List (Relation n)) :=
  let tested := FunctionalRelations.inspect formula clause
  ⟨tested.relations,tested.visits+
    2*(CapacityMatching.RowCost.formulaCells formula+3*clause.length+12*tested.relations.length)+256⟩

def relationScan {n : Nat} (formula : CNFFormula n) : CNFFormula n → Counted (List (Relation n))
  | [] => ⟨[],1⟩
  | clause::rest =>
      let first := relationOne formula clause
      let tail := relationScan formula rest
      ⟨first.value++tail.value,first.cells+tail.cells+24*(first.value.length+tail.value.length)+8⟩

theorem relationScan_value {n : Nat} (formula anchors : CNFFormula n) :
    (relationScan formula anchors).value=(FunctionalRelations.scan formula anchors).relations := by
  induction anchors with
  | nil => rfl
  | cons clause rest ih => simp only [relationScan,relationOne,FunctionalRelations.scan,ih]

theorem relationScan_length {n : Nat} (formula anchors : CNFFormula n) :
    (relationScan formula anchors).value.length ≤ 3*anchors.length := by
  rw [relationScan_value]
  exact FunctionalRelations.scan_length formula anchors

def relationRound (clauses literals : Nat) : Nat :=
  126*literals+90*clauses+41+8*(3*literals+2*clauses+1)+328+72*(clauses+1)+8

def relationsBudget (clauses literals : Nat) : Nat := clauses*relationRound clauses literals+1

theorem relationScan_cells {n : Nat} (formula anchors : CNFFormula n)
    (count : anchors.length ≤ formula.length) (source : ∀ clause ∈ anchors, clause ∈ formula) :
    (relationScan formula anchors).cells ≤ anchors.length*relationRound formula.length (Extract.literalCount formula)+1 := by
  induction anchors with
  | nil => simp [relationScan]
  | cons clause rest ih =>
      have tail := ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) count)
        (fun row member => source row (by simp [member]))
      have checked := FunctionalRelations.inspect_visits formula clause
      have generated := FunctionalRelations.inspect_length formula clause
      have remaining := relationScan_length formula rest
      have length := AffineRelationExtractionCost.clause_length_le_size formula clause (source clause (by simp))
      simp only [relationScan,relationOne,List.length_cons,relationRound,
        AffineRelationExtractionCost.size,CapacityMatching.RowCost.formulaCells] at *
      nlinarith

def relations {n : Nat} (formula : CNFFormula n) : Counted (List (Relation n)) := relationScan formula formula

theorem relations_value {n : Nat} (formula : CNFFormula n) :
    (relations formula).value=FunctionalRelations.extract formula := relationScan_value formula formula

theorem relations_length {n : Nat} (formula : CNFFormula n) : (relations formula).value.length ≤ 3*formula.length :=
  relationScan_length formula formula

theorem relations_cells {n : Nat} (formula : CNFFormula n) :
    (relations formula).cells ≤ relationsBudget formula.length (Extract.literalCount formula) :=
  relationScan_cells formula formula (by omega) (fun _ member => member)

def call {n : Nat} (coordinates : Array Row) (relation : Relation n) (address : Nat) : Counted Instruction :=
  let body := Code.functionalBody coordinates relation address
  ⟨⟨address,body.value⟩,body.cells+2*body.value.code.size+16⟩

theorem call_value {n : Nat} (coordinates : Array Row) (relation : Relation n) (address : Nat) :
    (call coordinates relation address).value=FunctionalPivot.call coordinates relation address := by
  simp only [call,Code.functionalBody_value,FunctionalPivot.call]

def callSize (size : Nat) : Nat := 22+6*size
def callBudget (size : Nat) : Nat := Code.functionalBudget size+20*(size+3)

theorem call_size {n : Nat} (coordinates : Array Row) (relation : Relation n) (address size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    instructionSize (call coordinates relation address).value ≤ callSize size := by
  have source := Code.functionalBody_size coordinates relation address size bounded
  simp only [call,instructionSize,callSize]
  omega

theorem call_cells {n : Nat} (coordinates : Array Row) (relation : Relation n) (address size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (call coordinates relation address).cells ≤ callBudget size := by
  have stored := Code.functionalBody_size coordinates relation address size bounded
  have source := Code.functionalBody_cells coordinates relation address size bounded
  simp only [call,callBudget]
  omega

def calls {n : Nat} (coordinates : Array Row) (relation : Relation n) : List Nat → Counted (List Instruction)
  | [] => ⟨[],1⟩
  | address::rest =>
      let first := call coordinates relation address
      let tail := calls coordinates relation rest
      ⟨first.value::tail.value,first.cells+tail.cells+2*(instructionSize first.value+inputSize tail.value)+8⟩

theorem calls_value {n : Nat} (coordinates : Array Row) (relation : Relation n) (addresses : List Nat) :
    (calls coordinates relation addresses).value=addresses.map (FunctionalPivot.call coordinates relation) := by
  induction addresses <;> simp_all [calls,call_value]

theorem calls_length {n : Nat} (coordinates : Array Row) (relation : Relation n) (addresses : List Nat) :
    (calls coordinates relation addresses).value.length=addresses.length := by simp only [calls_value,List.length_map]

theorem calls_storage {n : Nat} (coordinates : Array Row) (relation : Relation n) (addresses : List Nat) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    inputSize (calls coordinates relation addresses).value ≤ addresses.length*callSize size+1 := by
  induction addresses with
  | nil => simp [calls]
  | cons address rest ih =>
      have first := call_size coordinates relation address size bounded
      simp only [calls,FunctionalSchedule.Cost.inputSize_cons,List.length_cons]
      nlinarith

def callsBudget (count size : Nat) : Nat := count*(callBudget size+4*(count+1)*callSize size+10)+1

theorem calls_cells_aux {n : Nat} (coordinates : Array Row) (relation : Relation n) (addresses : List Nat) (count size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) (length : addresses.length ≤ count) :
    (calls coordinates relation addresses).cells ≤ addresses.length*(callBudget size+4*(count+1)*callSize size+10)+1 := by
  induction addresses with
  | nil => simp [calls]
  | cons address rest ih =>
      have tail := ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) length)
      have first := call_cells coordinates relation address size bounded
      have stored := call_size coordinates relation address size bounded
      have remaining := calls_storage coordinates relation rest size bounded
      simp only [calls,List.length_cons] at *
      nlinarith

theorem calls_cells {n : Nat} (coordinates : Array Row) (relation : Relation n) (addresses : List Nat) (count size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) (length : addresses.length ≤ count) :
    (calls coordinates relation addresses).cells ≤ callsBudget count size := by
  have source := calls_cells_aux coordinates relation addresses count size bounded length
  apply source.trans
  unfold callsBudget
  gcongr

theorem first_ready (source : List Instruction) :
    ((FunctionalSchedule.Cost.eligible (FunctionalSchedule.Cost.entries source).value).value.head?.map
      FunctionalSchedule.Entry.instruction)=source.find? (FunctionalSubstitution.ready []) := by
  rw [FunctionalSchedule.Cost.eligible_value,FunctionalSchedule.Cost.entries_value]
  induction source with
  | nil => rfl
  | cons instruction rest ih =>
      have same : decide (instruction.address ∉ (FunctionalSchedule.entry instruction).dependencies)=
          FunctionalSubstitution.ready [] instruction := by
        simp [FunctionalSchedule.entry,FunctionalSubstitution.ready,FunctionalSubstitution.inputs]
      simp only [List.map_cons,List.filter_cons,List.find?_cons]
      change ((if decide (instruction.address ∉ (FunctionalSchedule.entry instruction).dependencies) then
        FunctionalSchedule.entry instruction::(rest.map FunctionalSchedule.entry).filter _ else
        (rest.map FunctionalSchedule.entry).filter _).head?.map FunctionalSchedule.Entry.instruction)=_
      rw [same]
      cases ready : FunctionalSubstitution.ready [] instruction with
      | false => simpa only [Bool.false_eq_true,if_false] using ih
      | true => rfl

def choose {n : Nat} (coordinates : Array Row) (relation : Relation n) : Counted (Option Instruction) :=
  let source := Code.tableRead coordinates relation.output.var.val
  let generated := calls coordinates relation source.value.vars
  let prepared := FunctionalSchedule.Cost.entries generated.value
  let accepted := FunctionalSchedule.Cost.eligible prepared.value
  let output := accepted.value.head?.map FunctionalSchedule.Entry.instruction
  ⟨output,source.cells+generated.cells+prepared.visits+accepted.visits+
    2*(inputSize generated.value+FunctionalSchedule.storage prepared.value+2*FunctionalSchedule.storage accepted.value)+10⟩

theorem choose_value {n : Nat} (coordinates : Array Row) (relation : Relation n) :
    (choose coordinates relation).value=FunctionalPivot.choose coordinates relation := by
  simp only [choose,first_ready,calls_value,Code.tableRead_value,FunctionalPivot.choose]

def callsStorage (size : Nat) : Nat := size*callSize size+1

def chooseBudget (size : Nat) : Nat :=
  9*size+20+callsBudget size size+
    FunctionalSchedule.Cost.entriesBudget size (callsStorage size)+
    FunctionalSchedule.Cost.eligibleBudget (2*callsStorage size)+14*callsStorage size

theorem choose_cells {n : Nat} (coordinates : Array Row) (relation : Relation n) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (choose coordinates relation).cells ≤ chooseBudget size := by
  have readWork := Code.tableRead_cells coordinates relation.output.var.val
  have readSize := Code.tableRead_size coordinates relation.output.var.val
  have width : (Code.tableRead coordinates relation.output.var.val).value.vars.length ≤ size := by
    unfold CapacityMatching.RowCost.rowCells at readSize; omega
  have generated := calls_cells coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars size size bounded width
  have written := calls_storage coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars size bounded
  have length := calls_length coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars
  have ceiling : inputSize (calls coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars).value ≤ callsStorage size := by
    unfold callsStorage
    nlinarith
  have prepared := FunctionalSchedule.Cost.entries_visits
    (calls coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars).value (callsStorage size) ceiling
  have preparedSize := FunctionalSchedule.Cost.entries_storage
    (calls coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars).value
  have filtered := FunctionalSchedule.Cost.eligible_visits
    (FunctionalSchedule.Cost.entries (calls coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars).value).value
    (2*callsStorage size) (by omega)
  have filteredSize := FunctionalSchedule.Cost.eligible_storage
    (FunctionalSchedule.Cost.entries (calls coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars).value).value
  have enlarged : FunctionalSchedule.Cost.entriesBudget
      (calls coordinates relation (Code.tableRead coordinates relation.output.var.val).value.vars).value.length (callsStorage size) ≤
      FunctionalSchedule.Cost.entriesBudget size (callsStorage size) := by
    unfold FunctionalSchedule.Cost.entriesBudget
    gcongr
    omega
  simp only [choose,chooseBudget]
  omega

theorem choose_size {n : Nat} (coordinates : Array Row) (relation : Relation n) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) (instruction : Instruction)
    (found : (choose coordinates relation).value=some instruction) : instructionSize instruction ≤ callSize size := by
  rw [choose_value,FunctionalPivot.choose] at found
  obtain ⟨address,_,same⟩ := List.mem_map.mp (List.mem_of_find?_eq_some found)
  rw [← same,← call_value]
  exact call_size coordinates relation address size bounded

def filter {n : Nat} (coordinates : Array Row) : List (Relation n) → Counted (List Instruction)
  | [] => ⟨[],1⟩
  | relation::rest =>
      let first := choose coordinates relation
      let tail := filter coordinates rest
      let output := first.value.toList++tail.value
      ⟨output,first.cells+tail.cells+2*(inputSize first.value.toList+inputSize tail.value+inputSize output)+16⟩

theorem filter_value {n : Nat} (coordinates : Array Row) (source : List (Relation n)) :
    (filter coordinates source).value=source.filterMap (FunctionalPivot.choose coordinates) := by
  induction source with
  | nil => rfl
  | cons relation rest ih =>
      simp only [filter,choose_value,ih,List.filterMap_cons]
      cases FunctionalPivot.choose coordinates relation <;> rfl

theorem filter_length {n : Nat} (coordinates : Array Row) (source : List (Relation n)) :
    (filter coordinates source).value.length ≤ source.length := by
  rw [filter_value]
  exact List.length_filterMap_le _ _

theorem inputSize_append (left right : List Instruction) : inputSize (left++right)=inputSize left+inputSize right-1 := by
  simp only [inputSize,List.map_append,List.sum_append]
  omega

theorem choice_storage {n : Nat} (coordinates : Array Row) (relation : Relation n) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    inputSize (choose coordinates relation).value.toList ≤ callSize size+1 := by
  cases found : (choose coordinates relation).value with
  | none => simp
  | some instruction =>
      have output := choose_size coordinates relation size bounded instruction found
      simp only [Option.toList_some,FunctionalSchedule.Cost.inputSize_cons,FunctionalSchedule.Cost.inputSize_nil]
      omega

theorem filter_storage {n : Nat} (coordinates : Array Row) (source : List (Relation n)) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    inputSize (filter coordinates source).value ≤ source.length*callSize size+1 := by
  induction source with
  | nil => simp [filter]
  | cons relation rest ih =>
      have first := choice_storage coordinates relation size bounded
      have headPositive := FunctionalSchedule.Cost.inputSize_pos (choose coordinates relation).value.toList
      have tailPositive := FunctionalSchedule.Cost.inputSize_pos (filter coordinates rest).value
      have joined : inputSize (choose coordinates relation).value.toList+inputSize (filter coordinates rest).value ≤
          (rest.length+1)*callSize size+2 := by nlinarith
      simp only [filter,inputSize_append,List.length_cons]
      omega

def filterBudget (count size : Nat) : Nat := count*(chooseBudget size+8*(count+1)*callSize size+32)+1

theorem filter_cells_aux {n : Nat} (coordinates : Array Row) (source : List (Relation n)) (count size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) (length : source.length ≤ count) :
    (filter coordinates source).cells ≤ source.length*(chooseBudget size+8*(count+1)*callSize size+32)+1 := by
  induction source with
  | nil => simp [filter]
  | cons relation rest ih =>
      have tail := ih (by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) length)
      have first := choose_cells coordinates relation size bounded
      have headSize := choice_storage coordinates relation size bounded
      have tailSize := filter_storage coordinates rest size bounded
      have outputSize := filter_storage coordinates (relation::rest) size bounded
      simp only [filter,List.length_cons] at outputSize ⊢
      simp only [List.length_cons] at length
      nlinarith

theorem filter_cells {n : Nat} (coordinates : Array Row) (source : List (Relation n)) (count size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) (length : source.length ≤ count) :
    (filter coordinates source).cells ≤ filterBudget count size := by
  apply (filter_cells_aux coordinates source count size bounded length).trans
  unfold filterBudget
  gcongr

def candidates {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) : Counted (List Instruction) :=
  let source := relations formula
  let output := filter coordinates source.value
  ⟨output.value,source.cells+output.cells+
    2*(CapacityMatching.RowCost.formulaCells formula+12*source.value.length+inputSize output.value)+16⟩

theorem candidates_value {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (candidates (Table.coordinates n basis) formula).value=FunctionalPivot.candidates formula basis := by
  simp only [candidates,filter_value,relations_value,FunctionalPivot.candidates]

theorem candidates_length {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) :
    (candidates coordinates formula).value.length ≤ 3*formula.length :=
  (filter_length coordinates (relations formula).value).trans (relations_length formula)

def candidatesBudget (clauses literals size : Nat) : Nat :=
  relationsBudget clauses literals+filterBudget (3*clauses) size+
    2*(3*literals+2*clauses+1+36*clauses+3*clauses*callSize size+1)+16

theorem candidates_cells {n : Nat} (coordinates : Array Row) (formula : CNFFormula n) (size : Nat)
    (bounded : AffineCollect.tableSize coordinates ≤ size) :
    (candidates coordinates formula).cells ≤ candidatesBudget formula.length (Extract.literalCount formula) size := by
  have source := relations_cells formula
  have count := relations_length formula
  have generated := filter_cells coordinates (relations formula).value (3*formula.length) size bounded count
  have stored := filter_storage coordinates (relations formula).value size bounded
  simp only [candidates,candidatesBudget,CapacityMatching.RowCost.formulaCells]
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.ConditionalCandidateCost.Functional

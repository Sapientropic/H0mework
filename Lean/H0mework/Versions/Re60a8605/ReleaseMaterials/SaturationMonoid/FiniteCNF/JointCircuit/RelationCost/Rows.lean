import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.RelationUpdate

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointRelationCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
abbrev Counted := ArenaCost.Counted

def addresses (state : ArenaSource.State) : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | slot::rest =>
      let value := JointInputRelations.address state slot
      let tail := addresses state rest
      ⟨value::tail.value,tail.cells+8*state.arena.code.size+8*tail.value.length+16⟩

theorem addresses_value (state : ArenaSource.State) (slots : List Nat) :
    (addresses state slots).value=slots.map (JointInputRelations.address state) := by
  induction slots <;> simp_all only [addresses,List.map_nil,List.map_cons]

theorem addresses_length (state : ArenaSource.State) (slots : List Nat) : (addresses state slots).value.length=slots.length := by
  rw [addresses_value,List.length_map]

def addressBudget (nodes count : Nat) : Nat := count*(8*nodes+8*(count+1)+16)+1

theorem addresses_cells (state : ArenaSource.State) (slots : List Nat) :
    (addresses state slots).cells ≤ addressBudget state.arena.code.size slots.length := by
  induction slots with
  | nil => simp [addresses,addressBudget]
  | cons slot rest ih => simp only [addresses,addresses_length,List.length_cons,addressBudget] at *; nlinarith

theorem normalize_length (row : Row) : (CapacityMatching.RowCost.normalize row).value.vars.length ≤ row.vars.length := by
  simpa only [CapacityMatching.RowCost.normalize,Row.normalize,List.length_nil,Nat.add_zero] using Parity.merge_length row.vars []

def normalizeBudget (count : Nat) : Nat := count*(2*count+5)+2*count+7

theorem normalize_cells (row : Row) : (CapacityMatching.RowCost.normalize row).cells ≤ normalizeBudget row.vars.length := by
  have work := ConditionalCandidateCost.Code.merge_work row.vars []
  have size := normalize_length row
  simp only [List.length_nil,Nat.add_zero] at work
  change Table.mergeVisits row.vars []+2*((CapacityMatching.RowCost.normalize row).value.vars.length+2)+2 ≤ _
  unfold normalizeBudget
  omega

def row (state : ArenaSource.State) (source : Row) : Counted (Option FunctionalSubstitution.Instruction) :=
  let mapped := addresses state source.vars
  let normalized := CapacityMatching.RowCost.normalize ⟨mapped.value,source.rhs⟩
  match normalized.value.vars with
  | [] => ⟨none,mapped.cells+normalized.cells+16*(mapped.value.length+1)+16⟩
  | i::rest =>
      let body := ConditionalCandidateCost.Code.compileRow ⟨rest,normalized.value.rhs⟩
      ⟨some ⟨i,body.value⟩,mapped.cells+normalized.cells+body.cells+
        16*(mapped.value.length+rest.length+body.value.code.size+1)+24⟩

theorem row_value (state : ArenaSource.State) (source : Row) :
    (row state source).value=JointInputRelations.instruction
      (CapacityMatching.RowCost.normalize (JointInputRelations.mapped state source)).value := by
  simp only [row,addresses_value,JointInputRelations.mapped,JointInputRelations.instruction,ConditionalCandidateCost.Code.compileRow_value]
  split <;> simp_all

def itemSize : Option FunctionalSubstitution.Instruction → Nat
  | none => 1
  | some instruction => instruction.body.code.size+9

theorem row_size (state : ArenaSource.State) (source : Row) : itemSize (row state source).value ≤ 2*source.vars.length+10 := by
  have normalized := normalize_length (⟨(addresses state source.vars).value,source.rhs⟩ : Row)
  simp only [addresses_length] at normalized
  simp only [row]
  split
  · simp only [itemSize]; omega
  · rename_i i rest shape
    have body := ConditionalCandidateCost.Code.compileRow_size (⟨rest,(CapacityMatching.RowCost.normalize
      ⟨(addresses state source.vars).value,source.rhs⟩).value.rhs⟩ : Row)
    rw [shape] at normalized
    simp only [List.length_cons] at normalized
    simp only [itemSize,body]
    omega

def rowBudget (nodes : Nat) : Nat :=
  addressBudget nodes nodes+normalizeBudget nodes+ConditionalCandidateCost.Code.compileBudget nodes+128*(nodes+1)+32

theorem row_cells (state : ArenaSource.State) (source : Row) (bounded : source.vars.length ≤ state.arena.code.size) :
    (row state source).cells ≤ rowBudget state.arena.code.size := by
  have mapping := addresses_cells state source.vars
  have mappedWork : (addresses state source.vars).cells ≤ addressBudget state.arena.code.size state.arena.code.size :=
    mapping.trans (by unfold addressBudget; gcongr)
  have normalized := normalize_length (⟨(addresses state source.vars).value,source.rhs⟩ : Row)
  have normalizedWork := normalize_cells (⟨(addresses state source.vars).value,source.rhs⟩ : Row)
  simp only [addresses_length] at normalized normalizedWork
  have nw : (CapacityMatching.RowCost.normalize ⟨(addresses state source.vars).value,source.rhs⟩).cells ≤ normalizeBudget state.arena.code.size :=
    normalizedWork.trans (by unfold normalizeBudget; gcongr)
  simp only [row]
  split
  · simp only [addresses_length,rowBudget]; omega
  · rename_i i rest shape
    have body := ConditionalCandidateCost.Code.compileRow_size (⟨rest,(CapacityMatching.RowCost.normalize
      ⟨(addresses state source.vars).value,source.rhs⟩).value.rhs⟩ : Row)
    have built := ConditionalCandidateCost.Code.compileRow_cells (⟨rest,(CapacityMatching.RowCost.normalize
      ⟨(addresses state source.vars).value,source.rhs⟩).value.rhs⟩ : Row)
    rw [shape] at normalized
    simp only [List.length_cons] at normalized
    have restBound : rest.length ≤ state.arena.code.size := by omega
    have bw := built.trans (ConditionalCandidateCost.Code.compileBudget_mono rest.length state.arena.code.size restBound)
    simp only [addresses_length,body,rowBudget]
    omega

def collect (state : ArenaSource.State) : List Row → Counted (List FunctionalSubstitution.Instruction)
  | [] => ⟨[],1⟩
  | first::rest =>
      let generated := row state first
      let tail := collect state rest
      let output := match generated.value with | none => tail.value | some instruction => instruction::tail.value
      ⟨output,generated.cells+tail.cells+8*(itemSize generated.value+ArenaCost.historySize tail.value+1)+16⟩

theorem collect_value (state : ArenaSource.State) (rows : List Row) :
    (collect state rows).value=rows.filterMap (fun source => JointInputRelations.instruction
      (CapacityMatching.RowCost.normalize (JointInputRelations.mapped state source)).value) := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      simp only [collect,row_value,ih,List.filterMap_cons]
      split <;> simp_all

theorem collect_storage (state : ArenaSource.State) (rows : List Row)
    (bounded : ∀ row ∈ rows, row.vars.length ≤ state.arena.code.size) :
    ArenaCost.historySize (collect state rows).value ≤ rows.length*(2*state.arena.code.size+10)+1 := by
  induction rows with
  | nil => simp [collect,ArenaCost.historySize]
  | cons first rest ih =>
      have firstSize := row_size state first
      have firstBound := bounded first (by simp)
      have tail := ih (fun row member => bounded row (by simp [member]))
      simp only [collect]
      cases found : (row state first).value with
      | none => simp only [List.length_cons]; nlinarith
      | some instruction =>
          simp only [found,itemSize] at firstSize
          simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_cons,FunctionalSchedule.Cost.instructionSize,List.length_cons]
          change FunctionalSchedule.Cost.inputSize (collect state rest).value ≤ rest.length*(2*state.arena.code.size+10)+1 at tail
          nlinarith

def collectBudget (nodes count : Nat) : Nat := count*(rowBudget nodes+8*((count+1)*(2*nodes+10)+2)+16)+1

theorem collect_cells (state : ArenaSource.State) (rows : List Row)
    (bounded : ∀ row ∈ rows, row.vars.length ≤ state.arena.code.size) :
    (collect state rows).cells ≤ collectBudget state.arena.code.size rows.length := by
  induction rows with
  | nil => simp [collect,collectBudget]
  | cons first rest ih =>
      have firstWork := row_cells state first (bounded first (by simp))
      have firstSize := row_size state first
      have firstBound := bounded first (by simp)
      have tail := ih (fun row member => bounded row (by simp [member]))
      have stored := collect_storage state rest (fun row member => bounded row (by simp [member]))
      simp only [collect,collectBudget,List.length_cons] at *
      nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.JointRelationCost

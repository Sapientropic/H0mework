import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.RelationCost.Rows

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointRelationCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowCells rowsCells)

def keepFrom (state : ArenaSource.State) : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | slot::rest =>
      let retained := JointInputRelations.input state slot
      let tail := keepFrom state rest
      ⟨if retained then slot::tail.value else tail.value,tail.cells+8*state.arena.code.size+8*tail.value.length+8⟩

theorem keepFrom_value (state : ArenaSource.State) (slots : List Nat) :
    (keepFrom state slots).value=slots.filter (JointInputRelations.input state) := by
  induction slots <;> simp_all only [keepFrom,List.filter_nil,List.filter_cons]

theorem keepFrom_length (state : ArenaSource.State) (slots : List Nat) : (keepFrom state slots).value.length ≤ slots.length := by
  rw [keepFrom_value]
  exact List.length_filter_le _ _

theorem keepFrom_cells (state : ArenaSource.State) (slots : List Nat) :
    (keepFrom state slots).cells ≤ slots.length*(8*state.arena.code.size+8*(slots.length+1)+8)+1 := by
  induction slots with
  | nil => simp [keepFrom]
  | cons slot rest ih =>
      have length := keepFrom_length state rest
      simp only [keepFrom,List.length_cons]
      nlinarith

def keep (state : ArenaSource.State) : Counted (List Nat) :=
  let result := keepFrom state (List.range state.arena.code.size)
  ⟨result.value,result.cells+8*state.arena.code.size+8⟩

theorem keep_value (state : ArenaSource.State) : (keep state).value=JointInputRelations.keep state := by
  simp only [keep,keepFrom_value,JointInputRelations.keep]

def keepBudget (nodes : Nat) : Nat := nodes*(16*nodes+16)+8*nodes+9

theorem keep_cells (state : ArenaSource.State) : (keep state).cells ≤ keepBudget state.arena.code.size := by
  have work := keepFrom_cells state (List.range state.arena.code.size)
  simp only [List.length_range] at work
  simp only [keep,keepBudget]
  nlinarith

def rawRows (state : ArenaSource.State) (basis : List Row) : Counted (List Row) :=
  let retained := keep state
  let source := AffineForget.Cost.generate state.arena.code.size retained.value basis
  let erased := AffineForget.Cost.eraseRows retained.value source.value.image.kernel
  ⟨erased.value,retained.cells+source.cells+erased.cells+
    8*(AffineForget.Cost.modelSize source.value+rowsCells erased.value+retained.value.length+1)+16⟩

theorem rawRows_value (state : ArenaSource.State) (basis : List Row) :
    (rawRows state basis).value=JointInputRelations.rawRows state basis := by
  simp only [rawRows,keep_value,JointInputRelations.rawRows]

theorem rawRows_count (state : ArenaSource.State) (basis : List Row) : (rawRows state basis).value.length ≤ state.arena.code.size := by
  rw [rawRows_value,JointInputRelations.rawRows_value,List.length_map]
  exact AffineForget.Cost.kernel_length _ _ _

theorem rawRows_each (state : ArenaSource.State) (basis : List Row) (row : Row) (member : row ∈ (rawRows state basis).value) :
    row.vars.length ≤ state.arena.code.size := by
  rw [rawRows_value,JointInputRelations.rawRows_value] at member
  obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
  have originalSize := Table.row_length_le state.arena.code.size original
    (AffineForget.Cost.kernel_valid state.arena.code.size (JointInputRelations.keep state) basis original present)
  exact (List.length_filter_le _ _).trans originalSize

theorem rawRows_storage (state : ArenaSource.State) (basis : List Row) :
    rowsCells (rawRows state basis).value ≤ state.arena.code.size*(state.arena.code.size+2) := by
  have size := AffineForget.Cost.eraseRows_storage (JointInputRelations.keep state)
    (AtomImage.generate (AffineForget.source state.arena.code.size (JointInputRelations.keep state) basis)).kernel
  have source := AffineForget.Cost.kernel_storage state.arena.code.size (JointInputRelations.keep state) basis
  rw [AffineForget.Cost.eraseRows_value] at size
  rw [rawRows_value,JointInputRelations.rawRows_value]
  exact size.trans source

theorem forgetBudget_keep_mono (n a b : Nat) (bound : a ≤ b) :
    AffineForget.Cost.generateBudget n a ≤ AffineForget.Cost.generateBudget n b := by
  unfold AffineForget.Cost.generateBudget AffineForget.Cost.sourceBudget AffineForget.Cost.selectBudget
    AffineForget.Cost.eraseBudget AffineForget.Cost.eraseRowBudget AffineForget.Cost.modelBudget
  gcongr

def rawBudget (nodes : Nat) : Nat :=
  keepBudget nodes+AffineForget.Cost.generateBudget nodes nodes+AffineForget.Cost.eraseBudget nodes nodes+
    8*(AffineForget.Cost.modelBudget nodes nodes+nodes*(nodes+2)+nodes+1)+16

theorem rawRows_cells (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) :
    (rawRows state basis).cells ≤ rawBudget state.arena.code.size := by
  have kept := keep_cells state
  have count := JointInputRelations.keep_length state
  have source := (AffineForget.Cost.generate_cells state.arena.code.size (keep state).value basis valid).trans
    (forgetBudget_keep_mono state.arena.code.size _ state.arena.code.size (by rw [keep_value]; exact count))
  have erased := AffineForget.Cost.eraseRows_cells state.arena.code.size (keep state).value
    (AtomImage.generate (AffineForget.source state.arena.code.size (keep state).value basis)).kernel
    (AffineForget.Cost.kernel_valid _ _ _) (AffineForget.Cost.kernel_length _ _ _)
  have eraseWork : (AffineForget.Cost.eraseRows (keep state).value
      (AtomImage.generate (AffineForget.source state.arena.code.size (keep state).value basis)).kernel).cells ≤
        AffineForget.Cost.eraseBudget state.arena.code.size state.arena.code.size := by
    apply erased.trans
    unfold AffineForget.Cost.eraseBudget AffineForget.Cost.eraseRowBudget
    have bound : (keep state).value.length ≤ state.arena.code.size := by rw [keep_value]; exact count
    gcongr
  have model := AffineForget.Cost.generated_modelSize state.arena.code.size (keep state).value basis valid
  have modelBound : AffineForget.Cost.modelSize (AffineForget.generate state.arena.code.size (keep state).value basis) ≤
      AffineForget.Cost.modelBudget state.arena.code.size state.arena.code.size := by
    apply model.trans
    unfold AffineForget.Cost.modelBudget
    have bound : (keep state).value.length ≤ state.arena.code.size := by rw [keep_value]; exact count
    omega
  have stored := rawRows_storage state basis
  simp only [rawRows,AffineForget.Cost.generate_value,AffineForget.generate] at stored ⊢
  change rowsCells (AffineForget.Cost.eraseRows (keep state).value
    (AtomImage.generate (AffineForget.source state.arena.code.size (keep state).value basis)).kernel).value ≤ _ at stored
  change (keep state).cells+(AffineForget.Cost.generate state.arena.code.size (keep state).value basis).cells+
    (AffineForget.Cost.eraseRows (keep state).value (AtomImage.generate (AffineForget.source state.arena.code.size (keep state).value basis)).kernel).cells+
      8*(AffineForget.Cost.modelSize (AffineForget.generate state.arena.code.size (keep state).value basis)+
        rowsCells (AffineForget.Cost.eraseRows (keep state).value (AtomImage.generate (AffineForget.source state.arena.code.size (keep state).value basis)).kernel).value+
          (keep state).value.length+1)+16 ≤ _
  have keptCount : (keep state).value.length ≤ state.arena.code.size := by rw [keep_value]; exact count
  unfold rawBudget
  omega

def calls (state : ArenaSource.State) (basis : List Row) : Counted (List FunctionalSubstitution.Instruction) :=
  let source := rawRows state basis
  let output := collect state source.value
  ⟨output.value,source.cells+output.cells+8*(rowsCells source.value+ArenaCost.historySize output.value+1)+16⟩

theorem calls_value (state : ArenaSource.State) (basis : List Row) : (calls state basis).value=JointInputRelations.calls state basis := by
  simp only [calls,collect_value,rawRows_value,JointInputRelations.calls,JointInputRelations.rows,List.filterMap_map,Function.comp_def]

theorem calls_storage (state : ArenaSource.State) (basis : List Row) :
    ArenaCost.historySize (calls state basis).value ≤ state.arena.code.size*(2*state.arena.code.size+10)+1 := by
  have each := rawRows_each state basis
  have bound := rawRows_count state basis
  exact (collect_storage state (rawRows state basis).value each).trans (by gcongr)

def callsBudget (nodes : Nat) : Nat := rawBudget nodes+collectBudget nodes nodes+
  8*(nodes*(nodes+2)+nodes*(2*nodes+10)+2)+16

theorem calls_cells (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) : (calls state basis).cells ≤ callsBudget state.arena.code.size := by
  have first := rawRows_cells state basis valid
  have source := rawRows_storage state basis
  have count := rawRows_count state basis
  have output := calls_storage state basis
  have work := collect_cells state (rawRows state basis).value (rawRows_each state basis)
  have bodyWork : (collect state (rawRows state basis).value).cells ≤ collectBudget state.arena.code.size state.arena.code.size := by
    apply work.trans
    unfold collectBudget
    gcongr
  change ArenaCost.historySize (collect state (rawRows state basis).value).value ≤ _ at output
  simp only [calls,callsBudget]
  omega

def generate (state : ArenaSource.State) : Counted (List FunctionalSubstitution.Instruction) :=
  let checked := JointCircuitCost.checked state.arena.code.toList
  if checked.value then
    let joint := JointCircuitCost.analyzed state
    match joint.value with
    | .contradiction => ⟨[],checked.cells+joint.cells+8*(state.arena.code.size+state.relations.length+1)+16⟩
    | .basis basis =>
        let output := calls state basis
        ⟨output.value,checked.cells+joint.cells+output.cells+
          8*(state.arena.code.size+state.relations.length+AffineCarrier.cellSize basis+ArenaCost.historySize output.value+1)+16⟩
  else ⟨[],checked.cells+8*(state.arena.code.size+state.relations.length+1)+16⟩

theorem generate_value (state : ArenaSource.State) : (generate state).value=JointInputRelations.generate state := by
  simp only [generate,JointCircuitCost.checked_value,JointInputRelations.generate,JointCircuit.noAdd,calls_value]
  split
  · split <;> simp_all
  · simp_all

def generateBudget (nodes count : Nat) : Nat :=
  4*nodes+1+JointCircuitCost.analysisBudget nodes count+callsBudget nodes+
    8*(nodes+count+AffineCarrier.Cost.cellBound nodes+nodes*(2*nodes+10)+2)+16

theorem generate_cells (state : ArenaSource.State) : (generate state).cells ≤ generateBudget state.arena.code.size state.relations.length := by
  have checked := JointCircuitCost.checked_cells state.arena.code.toList
  simp only [Array.length_toList] at checked
  have joint := JointCircuitCost.analyzed_cells state
  have valid := JointCircuitCost.analyzed_valid state
  simp only [generate]
  split
  · cases found : (JointCircuitCost.analyzed state).value with
    | contradiction => simp only [generateBudget]; omega
    | basis basis =>
        have vb : Triangular basis ∧ RowsWithin state.arena.code.size basis := by simpa only [found,Result.triangular,Result.within] using valid
        have generated := calls_cells state basis vb
        have stored := calls_storage state basis
        have basisSize := AffineCarrier.Cost.cell_size state.arena.code.size basis vb.1 vb.2
        simp only [generateBudget]
        omega
  · simp only [generateBudget]; omega


theorem generate_storage (state : ArenaSource.State) :
    ArenaCost.historySize (generate state).value ≤ state.arena.code.size*(2*state.arena.code.size+10)+1 := by
  simp only [generate]
  split
  · split
    · simp [ArenaCost.historySize]
    · exact calls_storage state _
  · simp [ArenaCost.historySize]


end SaturationMonoid.ComplexityProjection.SATSource.JointRelationCost

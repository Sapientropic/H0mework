import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.RelationCost.Source

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointRelationCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

private theorem head_member {α : Type} (items : List α) (item : α) (found : items.head?=some item) : item ∈ items := by
  cases items with
  | nil => cases found
  | cons first rest =>
      simp only [List.head?_cons,Option.some.injEq] at found
      subst item
      exact List.mem_cons_self

def shifted (offset : Nat) : List ArenaSource.RawRelation → Counted (List ArenaSource.RawRelation)
  | [] => ⟨[],1⟩
  | item::rest =>
      let tail := shifted offset rest
      ⟨⟨item.address,offset+item.left,offset+item.right⟩::tail.value,tail.cells+8*tail.value.length+12⟩

theorem shifted_length (offset : Nat) (items : List ArenaSource.RawRelation) : (shifted offset items).value.length=items.length := by
  induction items <;> simp_all only [shifted,List.length_nil,List.length_cons]

theorem shifted_cells (offset : Nat) (items : List ArenaSource.RawRelation) :
    (shifted offset items).cells ≤ items.length*(8*items.length+12)+1 := by
  induction items with
  | nil => simp [shifted]
  | cons item rest ih => simp only [shifted,shifted_length,List.length_cons]; nlinarith

/-- The sealed source update executes its own constructor. Both executions of
prefix generation, reduction, root lookup, and payload copying are paid. -/
def substitute (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction) : Counted ArenaSource.State :=
  let compiled := SharedFunctional.execute [call] state.program.program
  let loaded := ArenaCost.Reduction.compact compiled.value.code
  let shifted := shifted call.body.code.size (ArenaCost.rawRelations state)
  let relations := ArenaCost.remap loaded.value.mapping shifted.value
  let weight := ArenaCost.lookup loaded.value.mapping (call.body.code.size+state.program.weight.val)
  let phase := ArenaCost.lookup loaded.value.mapping (call.body.code.size+state.program.phase.val)
  ⟨ArenaSource.substitute state call,2*(compiled.visits+loaded.cells+shifted.cells+relations.cells+weight.cells+phase.cells)+
    32*(state.arena.code.size+call.body.code.size+state.relations.length+1)+48⟩

theorem substitute_value (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction) :
    (substitute state call).value=ArenaSource.substitute state call := rfl

def substituteBudget (nodes count body : Nat) : Nat :=
  let size := nodes+body
  2*(2*(40*size+13)+ArenaCost.Reduction.budget size+count*(8*count+12)+1+
    count*(4*size+6*count+24)+1+4*size+8)+32*(size+count+1)+48

theorem substitute_cells (state : ArenaSource.State) (call : FunctionalSubstitution.Instruction) :
    (substitute state call).cells ≤ substituteBudget state.arena.code.size state.relations.length call.body.code.size := by
  let compiled := SharedFunctional.execute [call] state.program.program
  let loaded := ArenaCost.Reduction.compact compiled.value.code
  let displaced := shifted call.body.code.size (ArenaCost.rawRelations state)
  have compiledSize := SharedFunctional.execute_size [call] state.program.program
  change compiled.value.code.size=state.arena.code.size+call.body.code.size at compiledSize
  have compiledWork := SharedFunctional.execute_cells [call] state.program.program
  change compiled.visits ≤ 2*(40*(state.arena.code.size+call.body.code.size)+13) at compiledWork
  have reduction := ArenaCost.Reduction.compact_cells compiled.value.code
  have mapping := ArenaCost.reduction_mapping_size compiled.value.code
  change loaded.value.mapping.size=compiled.value.code.size at mapping
  have shiftedWork := shifted_cells call.body.code.size (ArenaCost.rawRelations state)
  have count : displaced.value.length=state.relations.length := by simp only [displaced,shifted_length,ArenaCost.rawRelations,List.length_map]
  have remapping := ArenaCost.remap_cells loaded.value.mapping displaced.value
  rw [count,mapping,compiledSize] at remapping
  simp only [ArenaCost.rawRelations,List.length_map] at shiftedWork
  rw [compiledSize] at reduction
  change 2*(compiled.visits+loaded.cells+displaced.cells+(ArenaCost.remap loaded.value.mapping displaced.value).cells+
    (ArenaCost.lookup loaded.value.mapping (call.body.code.size+state.program.weight.val)).cells+
    (ArenaCost.lookup loaded.value.mapping (call.body.code.size+state.program.phase.val)).cells)+
      32*(state.arena.code.size+call.body.code.size+state.relations.length+1)+48 ≤ _
  simp only [ArenaCost.lookup,mapping,compiledSize,substituteBudget]
  change loaded.cells ≤ _ at reduction
  change displaced.cells ≤ _ at shiftedWork
  omega

def update (state : ArenaSource.State) : Counted JointCircuit.Update :=
  let previous := JointCircuitCost.update state
  if JointRelationUpdate.usePrevious previous.value then
    ⟨previous.value,previous.cells+16*(state.arena.code.size+state.relations.length+
      ArenaCost.historySize previous.value.binding+JointCircuitCost.jointStorage previous.value.joint+1)+24⟩
  else
    let fresh := generate state
    match fresh.value.head? with
    | none => ⟨previous.value,previous.cells+fresh.cells+16*(state.arena.code.size+state.relations.length+
        ArenaCost.historySize fresh.value+ArenaCost.historySize previous.value.binding+JointCircuitCost.jointStorage previous.value.joint+1)+24⟩
    | some call =>
        let changed := substitute state call
        ⟨⟨changed.value,false,[call],previous.value.joint⟩,previous.cells+fresh.cells+changed.cells+
          32*(state.arena.code.size+state.relations.length+ArenaCost.historySize fresh.value+call.body.code.size+
            ArenaCost.historySize previous.value.binding+JointCircuitCost.jointStorage previous.value.joint+1)+48⟩

theorem update_value (state : ArenaSource.State) : (update state).value=JointRelationUpdate.update state := by
  simp only [update,JointCircuitCost.update_value,generate_value,substitute_value,JointRelationUpdate.update]
  split
  · simp_all
  · split <;> simp_all

def updateBudget (nodes count : Nat) : Nat :=
  JointCircuitCost.updateBudget nodes count+generateBudget nodes count+substituteBudget nodes count (2*nodes+1)+
    32*(nodes+count+nodes*(2*nodes+10)+1+(2*nodes+1)+(nodes+9)+AffineCarrier.Cost.cellBound nodes+3)+48

theorem update_cells (state : ArenaSource.State) :
    (update state).cells ≤ updateBudget state.arena.code.size state.relations.length := by
  have previous := JointCircuitCost.update_cells state
  have oldHistory := JointCircuitCost.update_history state
  have oldJoint := JointCircuitCost.update_joint state
  have fresh := generate_cells state
  have newHistory := generate_storage state
  simp only [update]
  split
  · simp only [updateBudget]; omega
  · cases chosen : (generate state).value.head? with
    | none => simp only [updateBudget]; omega
    | some call =>
        have member : call ∈ JointInputRelations.generate state := by
          rw [← generate_value]
          exact head_member _ _ chosen
        have body := (JointInputRelations.generate_present_size state call member).2
        have inputs := FunctionalSubstitution.inputs_size state.arena.code
        have step := substitute_cells state call
        have stepBound : (substitute state call).cells ≤ substituteBudget state.arena.code.size state.relations.length (2*state.arena.code.size+1) := by
          apply step.trans
          simp only [substituteBudget,ArenaCost.Reduction.budget]
          gcongr <;> omega
        simp only [updateBudget]
        omega

theorem update_history (state : ArenaSource.State) :
    ArenaCost.historySize (update state).value.binding ≤ 2*state.arena.code.size+10 := by
  have old := JointCircuitCost.update_history state
  simp only [update]
  split
  · simpa only using old.trans (by omega)
  · cases chosen : (generate state).value.head? with
    | none => exact old.trans (by omega)
    | some call =>
        have member : call ∈ JointInputRelations.generate state := by rw [← generate_value]; exact head_member _ _ chosen
        have body := (JointInputRelations.generate_present_size state call member).2
        have inputs := FunctionalSubstitution.inputs_size state.arena.code
        simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_cons,FunctionalSchedule.Cost.inputSize_nil,FunctionalSchedule.Cost.instructionSize]
        omega

theorem update_joint (state : ArenaSource.State) :
    JointCircuitCost.jointStorage (update state).value.joint ≤ AffineCarrier.Cost.cellBound state.arena.code.size+2 := by
  have old := JointCircuitCost.update_joint state
  simp only [update]
  split
  · exact old
  · split <;> exact old


attribute [local gcongr] JointCircuitCost.jointBudget_mono JointCircuitCost.formulaStorage_mono

theorem updateBudget_mono (n N c C : Nat) (nodes : n ≤ N) (count : c ≤ C) : updateBudget n c ≤ updateBudget N C := by
  simp only [updateBudget,generateBudget,callsBudget,rawBudget,keepBudget,collectBudget,rowBudget,addressBudget,normalizeBudget,
    substituteBudget,ConditionalCandidateCost.Code.compileBudget,
    JointCircuitCost.updateBudget,JointCircuitCost.analysisBudget,JointCircuitCost.formulaBudget,JointCircuitCost.aliasRowBudget,
    JointCircuitCost.gatherBudget,JointCircuitCost.pickBudget,JointCircuitCost.rootBudget,JointCircuitCost.linkBudget,
    ArenaCost.nextBudget,ArenaCost.applyBudget,ArenaCost.eligibleBudget,ArenaCost.Dependency.budget,ArenaCost.Rewiring.budget,
    ArenaCost.inputsBudget,ArenaCost.Reduction.budget,AffineForget.Cost.generateBudget,AffineForget.Cost.sourceBudget,
    AffineForget.Cost.selectBudget,AffineForget.Cost.imageBudget,AffineForget.Cost.imageVisitsBudget,AffineForget.Cost.imageWorkspace,
    AffineForget.Cost.eraseBudget,AffineForget.Cost.eraseRowBudget,AffineForget.Cost.gaussianBudget,AffineForget.Cost.modelBudget,
    AffineCollect.Cost.coordinateBudget,AffineCarrier.Cost.cellBound,EliminateCost.insertCellBudget,EliminateCost.reduceCellBudget,
    AtomImage.stepBudget]
  gcongr

def iterate : Nat → ArenaSource.State → Counted JointCircuit.Update
  | 0,state => ⟨⟨state,false,[],none⟩,16*(state.arena.code.size+state.relations.length+1)+24⟩
  | fuel+1,state =>
      let first := update state
      if JointIteration.done first.value then
        ⟨first.value,first.cells+16*(state.arena.code.size+state.relations.length+
          ArenaCost.historySize first.value.binding+JointCircuitCost.jointStorage first.value.joint+1)+24⟩
      else
        let tail := iterate fuel first.value.state
        ⟨JointIteration.combine first.value tail.value,first.cells+tail.cells+
          16*(state.arena.code.size+state.relations.length+ArenaCost.historySize first.value.binding+
            ArenaCost.historySize tail.value.binding+JointCircuitCost.jointStorage tail.value.joint+1)+24⟩

theorem iterate_value (fuel : Nat) (state : ArenaSource.State) :
    (iterate fuel state).value=JointRelationUpdate.iterate fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => simp only [iterate,update_value,ih,JointRelationUpdate.iterate]; split <;> rfl

theorem update_capacity (fuel bound limit : Nat) (state : ArenaSource.State)
    (inputBound : ArenaTotal.remaining state ≤ bound)
    (capacity : state.arena.code.size+(fuel+1)*(2*bound+2) ≤ limit) :
    (update state).value.state.arena.code.size+fuel*(2*bound+2) ≤ limit := by
  have size := JointRelationUpdate.update_size state
  rw [JointRelationUpdate.remaining_length] at inputBound
  rw [update_value]
  nlinarith

theorem iterate_history (fuel bound limit : Nat) (state : ArenaSource.State)
    (inputBound : ArenaTotal.remaining state ≤ bound)
    (capacity : state.arena.code.size+fuel*(2*bound+2) ≤ limit) :
    ArenaCost.historySize (iterate fuel state).value.binding ≤ fuel*(2*limit+10)+1 := by
  induction fuel generalizing state with
  | zero => simp [iterate,ArenaCost.historySize]
  | succ fuel ih =>
      have first := update_history state
      have current : state.arena.code.size ≤ limit := by omega
      have nextCapacity := update_capacity fuel bound limit state inputBound capacity
      have nextInput : ArenaTotal.remaining (update state).value.state ≤ bound := by
        rw [update_value]
        exact (JointRelationUpdate.update_remaining state).trans inputBound
      have tail := ih (update state).value.state nextInput nextCapacity
      have joined := JointCircuitCost.history_append (update state).value.binding (iterate fuel (update state).value.state).value.binding
      simp only [iterate]
      split
      · nlinarith
      · change ArenaCost.historySize ((update state).value.binding++(iterate fuel (update state).value.state).value.binding) ≤ _
        nlinarith

theorem iterate_joint (fuel bound limit : Nat) (state : ArenaSource.State)
    (inputBound : ArenaTotal.remaining state ≤ bound)
    (capacity : state.arena.code.size+fuel*(2*bound+2) ≤ limit) :
    JointCircuitCost.jointStorage (iterate fuel state).value.joint ≤ AffineCarrier.Cost.cellBound limit+2 := by
  induction fuel generalizing state with
  | zero => simp [iterate,JointCircuitCost.jointStorage]
  | succ fuel ih =>
      have current : state.arena.code.size ≤ limit := by omega
      have first := (update_joint state).trans (show AffineCarrier.Cost.cellBound state.arena.code.size+2 ≤
        AffineCarrier.Cost.cellBound limit+2 by unfold AffineCarrier.Cost.cellBound; gcongr)
      have nextCapacity := update_capacity fuel bound limit state inputBound capacity
      have nextInput : ArenaTotal.remaining (update state).value.state ≤ bound := by
        rw [update_value]
        exact (JointRelationUpdate.update_remaining state).trans inputBound
      have tail := ih (update state).value.state nextInput nextCapacity
      simp only [iterate]
      split
      · exact first
      · exact tail

def roundBudget (nodes count rounds : Nat) : Nat :=
  updateBudget nodes count+16*(nodes+count+(rounds+1)*(2*nodes+10)+AffineCarrier.Cost.cellBound nodes+5)+24

def iterateBudget (nodes count rounds : Nat) : Nat := (rounds+1)*roundBudget nodes count rounds

set_option maxRecDepth 2000 in
theorem iterate_cells_aux (fuel rounds bound limit : Nat) (state : ArenaSource.State)
    (enough : fuel ≤ rounds) (inputBound : ArenaTotal.remaining state ≤ bound)
    (capacity : state.arena.code.size+fuel*(2*bound+2) ≤ limit) :
    (iterate fuel state).cells ≤ (fuel+1)*roundBudget limit state.relations.length rounds := by
  induction fuel generalizing state with
  | zero => simp only [iterate,roundBudget]; omega
  | succ fuel ih =>
      have current : state.arena.code.size ≤ limit := by omega
      have first := (update_cells state).trans (updateBudget_mono _ limit _ _ current le_rfl)
      have history := update_history state
      have joint := (update_joint state).trans (show AffineCarrier.Cost.cellBound state.arena.code.size+2 ≤
        AffineCarrier.Cost.cellBound limit+2 by unfold AffineCarrier.Cost.cellBound; gcongr)
      have nextCapacity := update_capacity fuel bound limit state inputBound capacity
      have nextInput : ArenaTotal.remaining (update state).value.state ≤ bound := by
        rw [update_value]
        exact (JointRelationUpdate.update_remaining state).trans inputBound
      have nextCount : (update state).value.state.relations.length=state.relations.length := by rw [update_value,JointRelationUpdate.update_count]
      have later := ih (update state).value.state (by omega) nextInput nextCapacity
      rw [nextCount] at later
      have laterHistory := iterate_history fuel bound limit (update state).value.state nextInput nextCapacity
      have laterJoint := iterate_joint fuel bound limit (update state).value.state nextInput nextCapacity
      have kept : ArenaCost.historySize (iterate fuel (update state).value.state).value.binding ≤ rounds*(2*limit+10)+1 :=
        laterHistory.trans (by gcongr; omega)
      simp only [iterate]
      split
      · have this : (update state).cells+16*(state.arena.code.size+state.relations.length+
            ArenaCost.historySize (update state).value.binding+JointCircuitCost.jointStorage (update state).value.joint+1)+24 ≤
              roundBudget limit state.relations.length rounds := by
          unfold roundBudget
          nlinarith only [first,history,joint,current]
        exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
      · simp only [roundBudget] at later ⊢
        nlinarith only [first,history,later,kept,laterJoint,current]

def capacity (nodes : Nat) : Nat := 2*nodes*nodes+3*nodes

theorem capacity_fuel (state : ArenaSource.State) :
    state.arena.code.size+state.arena.code.size*(2*state.arena.code.size+2) ≤ capacity state.arena.code.size := by
  unfold capacity
  nlinarith

def run (state : ArenaSource.State) : Counted JointCircuit.Update :=
  let output := iterate state.arena.code.size state
  ⟨output.value,output.cells+16*(state.arena.code.size+state.relations.length+
    ArenaCost.historySize output.value.binding+JointCircuitCost.jointStorage output.value.joint+1)+24⟩

theorem run_value (state : ArenaSource.State) : (run state).value=JointRelationUpdate.run state := by
  simp only [run,iterate_value,JointRelationUpdate.run]

def runBudget (nodes count : Nat) : Nat :=
  iterateBudget (capacity nodes) count nodes+
    16*(nodes+count+nodes*(2*capacity nodes+10)+AffineCarrier.Cost.cellBound (capacity nodes)+4)+24

theorem run_cells (state : ArenaSource.State) : (run state).cells ≤ runBudget state.arena.code.size state.relations.length := by
  have work := iterate_cells_aux state.arena.code.size state.arena.code.size state.arena.code.size (capacity state.arena.code.size)
    state le_rfl (ArenaTotal.remaining_le_nodes state) (capacity_fuel state)
  have history := iterate_history state.arena.code.size state.arena.code.size (capacity state.arena.code.size) state
    (ArenaTotal.remaining_le_nodes state) (capacity_fuel state)
  have joint := iterate_joint state.arena.code.size state.arena.code.size (capacity state.arena.code.size) state
    (ArenaTotal.remaining_le_nodes state) (capacity_fuel state)
  simp only [run,runBudget,iterateBudget]
  omega



attribute [local gcongr] updateBudget_mono

theorem runBudget_mono (n N c C : Nat) (nodes : n ≤ N) (count : c ≤ C) : runBudget n c ≤ runBudget N C := by
  simp only [runBudget,iterateBudget,roundBudget,capacity,AffineCarrier.Cost.cellBound]
  gcongr

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Counted JointCircuit.Update :=
  let source := ArenaTotal.Cost.compile formula basis
  let generated := run source.value.state
  let output : JointCircuit.Update :=
    ⟨generated.value.state,generated.value.rejected,source.value.instructions++generated.value.binding,generated.value.joint⟩
  ⟨output,source.cells+generated.cells+32*(source.value.state.arena.code.size+source.value.state.relations.length+
    ArenaCost.historySize source.value.instructions+ArenaCost.historySize generated.value.binding+
      JointCircuitCost.jointStorage generated.value.joint+1)+48⟩

set_option maxHeartbeats 1200000 in
theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (compile formula basis).value=JointRelationUpdate.compile formula basis := by
  simp only [compile,run_value,JointRelationUpdate.compile]

def compileBudget (n clauses literals basisSize : Nat) : Nat :=
  let nodes := ArenaSource.sourceBound n clauses literals
  let count := 3*clauses+n*n
  ArenaTotal.Cost.compileBudget n clauses literals basisSize+runBudget nodes count+
    32*(nodes+count+nodes*(nodes+8)+1+nodes*(2*capacity nodes+10)+1+AffineCarrier.Cost.cellBound (capacity nodes)+3)+48

set_option maxHeartbeats 1200000 in
theorem compile_cells {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).cells ≤ compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  let source := ArenaTotal.Cost.compile formula basis
  let generated := run source.value.state
  let nodes := ArenaSource.sourceBound n formula.length (Extract.literalCount formula)
  let count := 3*formula.length+n*n
  have original := ArenaTotal.Cost.compile_cells formula basis valid
  have size := ArenaTotal.Cost.compile_size formula basis valid
  change source.value.state.arena.code.size ≤ nodes at size
  have relations : source.value.state.relations.length ≤ count := by
    rw [ArenaTotal.Cost.compile_count]
    exact ForcedBranches.Cost.generate_length formula basis
  have work := (run_cells source.value.state).trans (runBudget_mono _ nodes _ count size relations)
  change generated.cells ≤ runBudget nodes count at work
  have firstHistory := JointCircuitCost.prepared_history formula basis valid
  change ArenaCost.historySize source.value.instructions ≤ nodes*(nodes+8)+1 at firstHistory
  have lastHistory := iterate_history source.value.state.arena.code.size source.value.state.arena.code.size
    (capacity source.value.state.arena.code.size) source.value.state
    (ArenaTotal.remaining_le_nodes source.value.state) (capacity_fuel source.value.state)
  change ArenaCost.historySize generated.value.binding ≤ source.value.state.arena.code.size*(2*capacity source.value.state.arena.code.size+10)+1 at lastHistory
  have kept : ArenaCost.historySize generated.value.binding ≤ nodes*(2*capacity nodes+10)+1 :=
    lastHistory.trans (by unfold capacity; gcongr)
  have joint := iterate_joint source.value.state.arena.code.size source.value.state.arena.code.size
    (capacity source.value.state.arena.code.size) source.value.state
    (ArenaTotal.remaining_le_nodes source.value.state) (capacity_fuel source.value.state)
  change JointCircuitCost.jointStorage generated.value.joint ≤ AffineCarrier.Cost.cellBound (capacity source.value.state.arena.code.size)+2 at joint
  have jointBound : JointCircuitCost.jointStorage generated.value.joint ≤ AffineCarrier.Cost.cellBound (capacity nodes)+2 :=
    joint.trans (by unfold AffineCarrier.Cost.cellBound capacity; gcongr)
  change source.cells ≤ _ at original
  change source.cells+generated.cells+32*(source.value.state.arena.code.size+source.value.state.relations.length+
    ArenaCost.historySize source.value.instructions+ArenaCost.historySize generated.value.binding+
      JointCircuitCost.jointStorage generated.value.joint+1)+48 ≤ _
  change _ ≤ ArenaTotal.Cost.compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis)+
    runBudget nodes count+32*(nodes+count+nodes*(nodes+8)+1+nodes*(2*capacity nodes+10)+1+AffineCarrier.Cost.cellBound (capacity nodes)+3)+48
  omega

set_option maxHeartbeats 1200000 in
theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).value.read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  rw [compile_value]
  exact JointRelationUpdate.compile_read formula basis valid point

set_option maxHeartbeats 1200000 in
theorem compile_settled {n : Nat} (formula : CNFFormula n) (basis : List Row) : JointRelationUpdate.Settled (compile formula basis).value := by
  rw [compile_value]
  exact JointRelationUpdate.compile_settled formula basis


end SaturationMonoid.ComplexityProjection.SATSource.JointRelationCost

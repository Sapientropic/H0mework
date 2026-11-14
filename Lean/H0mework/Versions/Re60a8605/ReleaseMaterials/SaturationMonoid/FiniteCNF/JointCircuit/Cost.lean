import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Cost.Query

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointCircuitCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

attribute [local gcongr] AffineAtomFeedbackCost.frontBudget_mono
  AffineRelationExtractionCost.reduceBudget_mono AffineRelationExtractionCost.equationsBudget_mono

theorem jointBudget_mono (n N m M ell E : Nat) (width : n ≤ N) (clauses : m ≤ M) (literals : ell ≤ E) :
    AffineRelationExtractionCost.jointBudget n m ell ≤ AffineRelationExtractionCost.jointBudget N M E := by
  unfold AffineRelationExtractionCost.jointBudget AffineRelationExtractionCost.advanceBudget
    AffineRelationExtractionCost.extraBudget AffineRelationExtractionCost.compiledBound
    AffineAtomFeedbackCost.advanceBudget AffineAtomFeedbackCost.learnBudget
    AffineAtomFeedbackCost.sourceBound AffineAtomFeedbackCost.returnRowsBound
    AffineFeedbackCost.Propagation.updateBudget AffineFeedbackCost.Propagation.findBudget
    AffineFeedbackCost.Propagation.inspectBudget AffineFeedbackCost.Propagation.residualsBudget
    AffineFeedbackCost.Propagation.residualBudget AffineFeedbackCost.Propagation.scanBudget
    AffineFeedbackCost.Propagation.scanUnit AffineFeedbackCost.permBudget
    AffineFeedbackCost.permUnit AffineFeedbackCost.eraseBudget
    AffineAtomFeedbackCost.dataBudget AffineAtomFeedbackCost.dataClauseBudget
    CapacityMatching.RowCost.decodeBudget CapacityMatching.RowCost.decodeUnit
    AffineCarrier.Cost.cellBound EliminateCost.insertCellBudget EliminateCost.reduceCellBudget
  gcongr
  · unfold AffineFeedbackCost.Propagation.residualsBudget AffineFeedbackCost.Propagation.residualBudget EliminateCost.reduceCellBudget
    gcongr
  · unfold AffineAtomFeedbackCost.canonicalRowsBudget AffineAtomFeedbackCost.canonicalBudget
      AffineAtomFeedbackCost.sortBudget AffineAtomFeedbackCost.insertionBudget
    gcongr

def analyzed (state : ArenaSource.State) : Counted Result :=
  let data := formula state
  let source := AffineRelationExtractionCost.iterate data.value (state.arena.code.size+1) (.basis [])
  ⟨source.value,data.cells+source.cells+8*(storage data.value+AffineCarrier.resultSize source.value+1)+16⟩

theorem analyzed_value (state : ArenaSource.State) : (analyzed state).value=(JointCircuit.analyzed state).value := by
  simp only [analyzed,formula_value,JointCircuit.analyzed]

theorem analyzed_valid (state : ArenaSource.State) :
    (analyzed state).value.triangular ∧ (analyzed state).value.within state.arena.code.size := by
  rw [analyzed_value,JointCircuit.analyzed_value]
  exact (JointFeedback.generate_invariants (JointCircuit.formula state) [] (by simp [RowsWithin])).symm

def analysisBudget (nodes count : Nat) : Nat :=
  formulaBudget nodes count+(nodes+1)*
    (AffineRelationExtractionCost.jointBudget nodes (formulaStorage nodes count) (formulaStorage nodes count)+2)+1+
    8*(formulaStorage nodes count+AffineCarrier.Cost.cellBound nodes+2)+16

theorem analyzed_cells (state : ArenaSource.State) :
    (analyzed state).cells ≤ analysisBudget state.arena.code.size state.relations.length := by
  have data := formula_cells state
  have shape := formula_storage state
  have measures := storage_measures (formula state).value
  have solver := AffineRelationExtractionCost.iterate_cells (formula state).value (state.arena.code.size+1) (.basis [])
    ⟨triangular_nil,by simp [Result.within,RowsWithin]⟩
  have uniform := jointBudget_mono state.arena.code.size state.arena.code.size
    (formula state).value.length (formulaStorage state.arena.code.size state.relations.length)
    (Extract.literalCount (formula state).value) (formulaStorage state.arena.code.size state.relations.length)
    le_rfl (measures.1.trans shape) (measures.2.trans shape)
  have work := solver.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right uniform 2)) 1)
  have stored := AffineCarrier.Cost.result_size state.arena.code.size (analyzed state).value
    (analyzed_valid state).1 (analyzed_valid state).2
  change (formula state).cells+
    (AffineRelationExtractionCost.iterate (formula state).value (state.arena.code.size+1) (.basis [])).cells+
      8*(storage (formula state).value+AffineCarrier.resultSize (analyzed state).value+1)+16 ≤ _
  unfold analysisBudget
  omega

def update (state : ArenaSource.State) : Counted JointCircuit.Update :=
  let permitted := checked state.arena.code.toList
  if permitted.value then
    let source := analyzed state
    match source.value with
    | .contradiction =>
        ⟨⟨state,true,[],some source.value⟩,permitted.cells+source.cells+16*(state.arena.code.size+state.relations.length+1)+24⟩
    | .basis basis =>
        let chosen := pick state basis
        match chosen.value with
        | none =>
            ⟨⟨state,false,[],some source.value⟩,permitted.cells+source.cells+chosen.cells+
              16*(state.arena.code.size+state.relations.length+AffineCarrier.cellSize basis+1)+24⟩
        | some item =>
            let changed := ArenaCost.next state item.address item.relation.right
            let body := ArenaCost.Dependency.compact (ArenaAction.focus state.arena.code item.relation.right)
            let selected := ArenaSource.selected state item
            ⟨⟨changed.value,false,[selected],some source.value⟩,permitted.cells+source.cells+chosen.cells+changed.cells+2*body.cells+
              32*(state.arena.code.size+state.relations.length+AffineCarrier.cellSize basis+1)+48⟩
  else ⟨⟨state,false,[],none⟩,permitted.cells+16*(state.arena.code.size+state.relations.length+1)+24⟩

theorem update_value (state : ArenaSource.State) : (update state).value=JointCircuit.update state := by
  simp only [update,checked_value,JointCircuit.update,JointCircuit.noAdd,analyzed_value,pick_value,ArenaCost.next_value]
  split
  · split
    · simp_all
    · split <;> simp_all
  · simp_all


def updateBudget (nodes count : Nat) : Nat :=
  4*nodes+1+analysisBudget nodes count+pickBudget nodes+ArenaCost.nextBudget nodes count+
    2*ArenaCost.Dependency.budget nodes+32*(nodes+count+AffineCarrier.Cost.cellBound nodes+1)+48

theorem update_cells (state : ArenaSource.State) :
    (update state).cells ≤ updateBudget state.arena.code.size state.relations.length := by
  have check := checked_cells state.arena.code.toList
  simp only [Array.length_toList] at check
  have analysis := analyzed_cells state
  have valid := analyzed_valid state
  simp only [update]
  split
  · cases source : (analyzed state).value with
    | contradiction => simp only [updateBudget]; omega
    | basis basis =>
        have vb : Triangular basis ∧ RowsWithin state.arena.code.size basis := by simpa only [source,Result.triangular,Result.within] using valid
        have picked := pick_cells state basis vb
        have space := AffineCarrier.Cost.cell_size state.arena.code.size basis vb.1 vb.2
        simp only
        split
        · simp only [updateBudget]; omega
        · rename_i item found
          have changed := ArenaCost.next_cells state item.address item.relation.right
          have body := ArenaCost.Dependency.compact_cells (ArenaAction.focus state.arena.code item.relation.right)
          change _ ≤ ArenaCost.Dependency.budget state.arena.code.size at body
          simp only [updateBudget]
          omega
  · simp only [updateBudget]; omega

def jointStorage : Option Result → Nat
  | none => 1
  | some result => AffineCarrier.resultSize result+1

theorem update_joint (state : ArenaSource.State) :
    jointStorage (update state).value.joint ≤ AffineCarrier.Cost.cellBound state.arena.code.size+2 := by
  have valid := analyzed_valid state
  have space := AffineCarrier.Cost.result_size state.arena.code.size (analyzed state).value valid.1 valid.2
  simp only [update]
  split
  · split
    · simpa only [jointStorage] using Nat.add_le_add_right space 1
    · split <;> simpa only [jointStorage] using Nat.add_le_add_right space 1
  · simp only [jointStorage]; omega

theorem update_history (state : ArenaSource.State) :
    ArenaCost.historySize (update state).value.binding ≤ state.arena.code.size+9 := by
  rw [update_value]
  by_cases checked : JointCircuit.noAdd state.arena.code=true
  · cases source : (JointCircuit.analyzed state).value with
    | contradiction => simp [JointCircuit.update,checked,source,ArenaCost.historySize]
    | basis basis =>
        cases picked : JointCircuit.pick state basis with
        | none => simp [JointCircuit.update,checked,source,picked,ArenaCost.historySize]
        | some item =>
            have size := ArenaAction.actualBody_size state.arena item.relation.right
            simp only [JointCircuit.update,checked,if_true,source,picked,ArenaCost.historySize,
              FunctionalSchedule.Cost.inputSize_cons,FunctionalSchedule.Cost.inputSize_nil,
              FunctionalSchedule.Cost.instructionSize,ArenaSource.selected]
            omega
  · simp [JointCircuit.update,checked,ArenaCost.historySize]

theorem history_append (first second : List FunctionalSubstitution.Instruction) :
    ArenaCost.historySize (first++second)+1=ArenaCost.historySize first+ArenaCost.historySize second := by
  simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize,List.map_append,List.sum_append]
  omega

def iterate : Nat → ArenaSource.State → Counted JointCircuit.Update
  | 0,state => ⟨⟨state,false,[],none⟩,16*(state.arena.code.size+state.relations.length+1)+24⟩
  | fuel+1,state =>
      let first := update state
      if JointIteration.done first.value then
        ⟨first.value,first.cells+16*(state.arena.code.size+state.relations.length+
          ArenaCost.historySize first.value.binding+jointStorage first.value.joint+1)+24⟩
      else
        let tail := iterate fuel first.value.state
        let result := JointIteration.combine first.value tail.value
        ⟨result,first.cells+tail.cells+16*(state.arena.code.size+state.relations.length+
          ArenaCost.historySize first.value.binding+ArenaCost.historySize tail.value.binding+jointStorage tail.value.joint+1)+24⟩

theorem iterate_value (fuel : Nat) (state : ArenaSource.State) :
    (iterate fuel state).value=JointIteration.iterate fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => simp only [iterate,update_value,ih,JointIteration.iterate]; split <;> rfl

theorem iterate_joint (fuel : Nat) (state : ArenaSource.State) :
    jointStorage (iterate fuel state).value.joint ≤ AffineCarrier.Cost.cellBound state.arena.code.size+2 := by
  induction fuel generalizing state with
  | zero => simp [iterate,jointStorage]
  | succ fuel ih =>
      have first := update_joint state
      have tail := ih (update state).value.state
      have same : (update state).value.state.arena.code.size=state.arena.code.size := by
        rw [update_value,JointCircuit.update_next_size]
      rw [same] at tail
      simp only [iterate]
      split
      · exact first
      · exact tail

theorem iterate_history (fuel : Nat) (state : ArenaSource.State) :
    ArenaCost.historySize (iterate fuel state).value.binding ≤ fuel*(state.arena.code.size+8)+1 := by
  induction fuel generalizing state with
  | zero => simp [iterate,ArenaCost.historySize]
  | succ fuel ih =>
      have first := update_history state
      have tail := ih (update state).value.state
      have same : (update state).value.state.arena.code.size=state.arena.code.size := by
        rw [update_value,JointCircuit.update_next_size]
      rw [same] at tail
      have joined := history_append (update state).value.binding (iterate fuel (update state).value.state).value.binding
      simp only [iterate]
      split
      · nlinarith
      · change ArenaCost.historySize ((update state).value.binding++(iterate fuel (update state).value.state).value.binding) ≤ _
        nlinarith

def roundBudget (nodes count fuel : Nat) : Nat :=
  updateBudget nodes count+16*(nodes+count+(fuel+1)*(nodes+8)+AffineCarrier.Cost.cellBound nodes+5)+24

def iterateBudget (nodes count fuel : Nat) : Nat := (fuel+1)*roundBudget nodes count fuel

set_option maxRecDepth 2000 in
theorem iterate_cells_aux (fuel rounds : Nat) (state : ArenaSource.State) (enough : fuel ≤ rounds) :
    (iterate fuel state).cells ≤ (fuel+1)*roundBudget state.arena.code.size state.relations.length rounds := by
  induction fuel generalizing state with
  | zero => simp only [iterate,roundBudget]; omega
  | succ fuel ih =>
      have first := update_cells state
      have history := update_history state
      have joint := update_joint state
      have nextSize : (update state).value.state.arena.code.size=state.arena.code.size := by rw [update_value,JointCircuit.update_next_size]
      have nextCount : (update state).value.state.relations.length=state.relations.length := by rw [update_value,JointCircuit.update_relations]
      have later := ih (update state).value.state (by omega)
      rw [nextSize,nextCount] at later
      have laterHistory := iterate_history fuel (update state).value.state
      have laterJoint := iterate_joint fuel (update state).value.state
      rw [nextSize] at laterHistory laterJoint
      have kept : ArenaCost.historySize (iterate fuel (update state).value.state).value.binding ≤ rounds*(state.arena.code.size+8)+1 :=
        laterHistory.trans (by gcongr; omega)
      simp only [iterate]
      split
      · have this : (update state).cells+16*(state.arena.code.size+state.relations.length+
            ArenaCost.historySize (update state).value.binding+jointStorage (update state).value.joint+1)+24 ≤
              roundBudget state.arena.code.size state.relations.length rounds := by
          unfold roundBudget
          nlinarith
        exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
      · simp only [roundBudget] at later ⊢
        nlinarith only [first,history,later,kept,laterJoint]

theorem iterate_cells (fuel : Nat) (state : ArenaSource.State) :
    (iterate fuel state).cells ≤ iterateBudget state.arena.code.size state.relations.length fuel :=
  iterate_cells_aux fuel fuel state le_rfl



theorem formulaStorage_mono (n N c C : Nat) (nodes : n ≤ N) (count : c ≤ C) :
    formulaStorage n c ≤ formulaStorage N C := by unfold formulaStorage; gcongr

attribute [local gcongr] jointBudget_mono formulaStorage_mono

theorem iterateBudget_mono (n N c C f F : Nat) (nodes : n ≤ N) (count : c ≤ C) (fuel : f ≤ F) :
    iterateBudget n c f ≤ iterateBudget N C F := by
  unfold iterateBudget roundBudget updateBudget analysisBudget formulaBudget aliasRowBudget gatherBudget
    pickBudget rootBudget linkBudget ArenaCost.nextBudget ArenaCost.applyBudget ArenaCost.eligibleBudget
    ArenaCost.Dependency.budget ArenaCost.Rewiring.budget ArenaCost.inputsBudget
    AffineCarrier.Cost.cellBound EliminateCost.reduceCellBudget
  gcongr

def run (state : ArenaSource.State) : Counted JointCircuit.Update :=
  let output := iterate state.arena.code.size state
  ⟨output.value,output.cells+16*(state.arena.code.size+state.relations.length+
    ArenaCost.historySize output.value.binding+jointStorage output.value.joint+1)+24⟩

theorem run_value (state : ArenaSource.State) : (run state).value=JointIteration.run state := by
  simp only [run,iterate_value,JointIteration.run]

def runBudget (nodes count : Nat) : Nat :=
  iterateBudget nodes count nodes+16*(nodes+count+nodes*(nodes+8)+AffineCarrier.Cost.cellBound nodes+4)+24

theorem run_cells (state : ArenaSource.State) :
    (run state).cells ≤ runBudget state.arena.code.size state.relations.length := by
  have work := iterate_cells state.arena.code.size state
  have history := iterate_history state.arena.code.size state
  have joint := iterate_joint state.arena.code.size state
  simp only [run,runBudget]
  omega

theorem runBudget_mono (n N c C : Nat) (nodes : n ≤ N) (count : c ≤ C) : runBudget n c ≤ runBudget N C := by
  have work := iterateBudget_mono n N c C n N nodes count nodes
  unfold runBudget AffineCarrier.Cost.cellBound
  gcongr

theorem run_read (state : ArenaSource.State) (point : Nat → Bool) :
    (run state).value.read point=JointCircuit.read state point := by
  rw [run_value]
  exact JointIteration.run_read state point

theorem run_settled (state : ArenaSource.State) : JointIteration.Settled (run state).value := by
  rw [run_value]
  exact JointIteration.run_settled state

def compile {n : Nat} (query : CNFFormula n) (basis : List Row) : Counted JointCircuit.Update :=
  let source := ArenaTotal.Cost.compile query basis
  let generated := run source.value.state
  let output : JointCircuit.Update :=
    ⟨generated.value.state,generated.value.rejected,source.value.instructions++generated.value.binding,generated.value.joint⟩
  ⟨output,source.cells+generated.cells+32*(source.value.state.arena.code.size+source.value.state.relations.length+
    ArenaCost.historySize source.value.instructions+ArenaCost.historySize generated.value.binding+jointStorage generated.value.joint+1)+48⟩

set_option maxHeartbeats 1200000 in
theorem compile_value {n : Nat} (query : CNFFormula n) (basis : List Row) :
    (compile query basis).value=JointIteration.compile query basis := by
  simp only [compile,run_value,JointIteration.compile]

def compileBudget (n clauses literals basisSize : Nat) : Nat :=
  let nodes := ArenaSource.sourceBound n clauses literals
  let count := 3*clauses+n*n
  ArenaTotal.Cost.compileBudget n clauses literals basisSize+runBudget nodes count+
    32*(nodes+count+2*(nodes*(nodes+8)+1)+AffineCarrier.Cost.cellBound nodes+3)+48

theorem prepared_history {n : Nat} (query : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    ArenaCost.historySize (ArenaTotal.Cost.compile query basis).value.instructions ≤
      let size := ArenaSource.sourceBound n query.length (Extract.literalCount query)
      size*(size+8)+1 := by
  let source := ArenaSource.front query basis
  let initial := ArenaCost.build source.initial source.candidates
  have size := (ArenaCost.build_nodes source.initial source.candidates).trans (ArenaCost.source_inventory query basis valid)
  have history := ArenaTotal.Cost.run_history initial.value
  change ArenaCost.historySize (ArenaTotal.Cost.compile query basis).value.instructions ≤ initial.value.arena.code.size*(initial.value.arena.code.size+8)+1 at history
  apply history.trans
  change initial.value.arena.code.size*(initial.value.arena.code.size+8)+1 ≤
    ArenaSource.sourceBound n query.length (Extract.literalCount query)*
      (ArenaSource.sourceBound n query.length (Extract.literalCount query)+8)+1
  change initial.value.arena.code.size ≤ ArenaSource.sourceBound n query.length (Extract.literalCount query) at size
  gcongr

set_option maxHeartbeats 1200000 in
theorem compile_cells {n : Nat} (query : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile query basis).cells ≤ compileBudget n query.length (Extract.literalCount query) (AffineCarrier.cellSize basis) := by
  let source := ArenaTotal.Cost.compile query basis
  let generated := run source.value.state
  let nodes := ArenaSource.sourceBound n query.length (Extract.literalCount query)
  let count := 3*query.length+n*n
  have original := ArenaTotal.Cost.compile_cells query basis valid
  have size := ArenaTotal.Cost.compile_size query basis valid
  change source.value.state.arena.code.size ≤ nodes at size
  have relations : source.value.state.relations.length ≤ count := by
    rw [ArenaTotal.Cost.compile_count]
    exact ForcedBranches.Cost.generate_length query basis
  have work := (run_cells source.value.state).trans (runBudget_mono _ nodes _ count size relations)
  change generated.cells ≤ runBudget nodes count at work
  have firstHistory := prepared_history query basis valid
  have lastHistory := iterate_history source.value.state.arena.code.size source.value.state
  change ArenaCost.historySize generated.value.binding ≤ source.value.state.arena.code.size*(source.value.state.arena.code.size+8)+1 at lastHistory
  have kept : ArenaCost.historySize generated.value.binding ≤ nodes*(nodes+8)+1 := lastHistory.trans (by gcongr)
  have joint := iterate_joint source.value.state.arena.code.size source.value.state
  change jointStorage generated.value.joint ≤ AffineCarrier.Cost.cellBound source.value.state.arena.code.size+2 at joint
  have jointBound : jointStorage generated.value.joint ≤ AffineCarrier.Cost.cellBound nodes+2 := joint.trans (by unfold AffineCarrier.Cost.cellBound; gcongr)
  change source.cells ≤ _ at original
  change source.cells+generated.cells+32*(source.value.state.arena.code.size+source.value.state.relations.length+
    ArenaCost.historySize source.value.instructions+ArenaCost.historySize generated.value.binding+jointStorage generated.value.joint+1)+48 ≤ _
  change _ ≤ ArenaTotal.Cost.compileBudget n query.length (Extract.literalCount query) (AffineCarrier.cellSize basis)+
    runBudget nodes count+32*(nodes+count+2*(nodes*(nodes+8)+1)+AffineCarrier.Cost.cellBound nodes+3)+48
  change ArenaCost.historySize source.value.instructions ≤ nodes*(nodes+8)+1 at firstHistory
  omega

set_option maxHeartbeats 1200000 in
theorem compile_read {n : Nat} (query : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile query basis).value.read point=CNFFormula.eval query (Gates.coordinate (Table.coordinates n basis) point) := by
  rw [compile_value]
  exact JointIteration.compile_read query basis valid point

set_option maxHeartbeats 1200000 in
theorem compile_settled {n : Nat} (query : CNFFormula n) (basis : List Row) :
    JointIteration.Settled (compile query basis).value := by
  rw [compile_value]
  exact JointIteration.compile_settled query basis


end SaturationMonoid.ComplexityProjection.SATSource.JointCircuitCost

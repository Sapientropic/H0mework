import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Cost.Action

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open CapacityMatching.RowCost (rowCells rowsCells)

def iterate : Nat → Frame → List Row → Counted PortUpdate.Output
  | 0,frame,rows => ⟨⟨frame,false,[],none⟩,32*(frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+rowsCells rows+1)+48⟩
  | fuel+1,frame,rows =>
      let first := update frame rows
      if JointIteration.done first.value.value then
        ⟨first.value,first.cells+32*(frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+rowsCells rows+
          ArenaCost.historySize first.value.binding+JointCircuitCost.jointStorage first.value.joint+1)+48⟩
      else
        let tail := iterate fuel first.value.frame rows
        ⟨PortUpdate.combine first.value tail.value,first.cells+tail.cells+
          32*(frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+rowsCells rows+
            ArenaCost.historySize first.value.binding+ArenaCost.historySize tail.value.binding+JointCircuitCost.jointStorage tail.value.joint+1)+48⟩

theorem iterate_value (fuel : Nat) (frame : Frame) (rows : List Row) : (iterate fuel frame rows).value=ProductRows.iterate fuel frame rows := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih => simp only [iterate,update_value,ih,ProductRows.iterate]; split <;> rfl

theorem iterate_history (fuel : Nat) (frame : Frame) (rows : List Row) :
    ArenaCost.historySize (iterate fuel frame rows).value.binding ≤ fuel*(frame.state.arena.code.size+9)+1 := by
  induction fuel generalizing frame with
  | zero => simp [iterate,ArenaCost.historySize]
  | succ fuel ih =>
      have first := update_history frame rows
      have size : (update frame rows).value.frame.state.arena.code.size=frame.state.arena.code.size := by rw [update_value,ProductRows.update_size]
      have tail := ih (update frame rows).value.frame
      rw [size] at tail
      have joined := JointCircuitCost.history_append (update frame rows).value.binding (iterate fuel (update frame rows).value.frame rows).value.binding
      simp only [iterate]
      split
      · nlinarith
      · change ArenaCost.historySize ((update frame rows).value.binding++(iterate fuel (update frame rows).value.frame rows).value.binding) ≤ _
        nlinarith

theorem iterate_joint (fuel : Nat) (frame : Frame) (rows : List Row) :
    JointCircuitCost.jointStorage (iterate fuel frame rows).value.joint ≤ AffineCarrier.Cost.cellBound frame.state.arena.code.size+2 := by
  induction fuel generalizing frame with
  | zero => simp [iterate,JointCircuitCost.jointStorage]
  | succ fuel ih =>
      have first := update_joint frame rows
      have size : (update frame rows).value.frame.state.arena.code.size=frame.state.arena.code.size := by rw [update_value,ProductRows.update_size]
      have tail := ih (update frame rows).value.frame
      rw [size] at tail
      simp only [iterate]
      split
      · exact first
      · exact tail

def roundBudget (n p c s r : Nat) : Nat := updateBudget n p c s+
  32*(n+p+c+s+(r+1)*(n+9)+AffineCarrier.Cost.cellBound n+5)+48
def iterateBudget (n p c s r : Nat) : Nat := (r+1)*roundBudget n p c s r

theorem iterate_cells_aux (fuel rounds : Nat) (frame : Frame) (rows : List Row) (enough : fuel ≤ rounds) :
    (iterate fuel frame rows).cells ≤ (fuel+1)*roundBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length (rowsCells rows) rounds := by
  induction fuel generalizing frame with
  | zero => simp only [iterate,roundBudget]; omega
  | succ fuel ih =>
      have first := update_cells frame rows
      have history := update_history frame rows
      have joint := update_joint frame rows
      have size : (update frame rows).value.frame.state.arena.code.size=frame.state.arena.code.size := by rw [update_value,ProductRows.update_size]
      have ports : (update frame rows).value.frame.ports.size=frame.ports.size := by rw [update_value,ProductRows.update_ports]
      have count : (update frame rows).value.frame.state.relations.length=frame.state.relations.length := by rw [update_value,ProductRows.update_count]
      have tail := ih (update frame rows).value.frame (by omega)
      rw [ports,count,size] at tail
      have lastHistory := iterate_history fuel (update frame rows).value.frame rows
      have lastJoint := iterate_joint fuel (update frame rows).value.frame rows
      rw [size] at lastHistory lastJoint
      have kept := lastHistory.trans (show fuel*(frame.state.arena.code.size+9)+1 ≤ rounds*(frame.state.arena.code.size+9)+1 by gcongr; omega)
      simp only [iterate]
      split
      · have this : (update frame rows).cells+32*(frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+rowsCells rows+
            ArenaCost.historySize (update frame rows).value.binding+JointCircuitCost.jointStorage (update frame rows).value.joint+1)+48 ≤
              roundBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length (rowsCells rows) rounds := by
          unfold roundBudget
          nlinarith only [first,history,joint]
        exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
      · simp only [roundBudget] at tail ⊢
        nlinarith only [first,history,tail,kept,lastJoint]

attribute [local gcongr] JointCircuitCost.jointBudget_mono JointCircuitCost.formulaStorage_mono PortCost.bindBudget_mono

theorem iterateBudget_mono (n N p P c C s S r R : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) (hs : s ≤ S) (hr : r ≤ R) :
    iterateBudget n p c s r ≤ iterateBudget N P C S R := by
  simp only [iterateBudget,roundBudget,updateBudget,analyzeBudget,gaussianBudget,remapBudget,rowBudget,refsBudget,
    JointCircuitCost.pickBudget,JointCircuitCost.rootBudget,JointCircuitCost.linkBudget,
    ArenaCost.eligibleBudget,ArenaCost.Dependency.budget,ArenaCost.inputsBudget,
    AffineCarrier.Cost.cellBound,EliminateCost.insertCellBudget,EliminateCost.reduceCellBudget]
  gcongr

def portsBound (n : Nat) : Nat := n+n*n
def inventoryBound (n : Nat) : Nat := n+n*n+1

def run (state : ArenaSource.State) : Counted PortUpdate.Output :=
  let source := prepare state
  if source.value.rejected then
    ⟨⟨source.value.frame,true,[],none⟩,source.cells+32*(source.value.frame.state.arena.code.size+source.value.frame.ports.size+
      source.value.frame.state.relations.length+rowsCells source.value.rows+1)+64⟩
  else
    let generated := iterate source.value.frame.state.arena.code.size source.value.frame source.value.rows
    ⟨generated.value,source.cells+generated.cells+32*(source.value.frame.state.arena.code.size+source.value.frame.ports.size+
      source.value.frame.state.relations.length+rowsCells source.value.rows+ArenaCost.historySize generated.value.binding+
        JointCircuitCost.jointStorage generated.value.joint+1)+64⟩

theorem run_value (state : ArenaSource.State) : (run state).value=ProductRows.run state := by
  simp only [run,prepare_value,iterate_value,ProductRows.run]
  split <;> rfl

def runBudget (n c : Nat) : Nat :=
  let nodes := inventoryBound n
  let ports := portsBound n
  let rows := ProductRows.rowBound n
  prepareBudget n c+iterateBudget nodes ports c rows nodes+
    32*(nodes+ports+c+rows+nodes*(nodes+9)+AffineCarrier.Cost.cellBound nodes+4)+64

theorem prepare_size (state : ArenaSource.State) : (prepare state).value.frame.state.arena.code.size ≤ inventoryBound state.arena.code.size := by
  rw [prepare_value,ProductRows.prepare_frame]
  have size := ProductBatch.generate_size (PortEmbedding.initial state)
  simpa only [PortEmbedding.initial,Array.size_ofFn,inventoryBound] using size

theorem prepare_ports (state : ArenaSource.State) : (prepare state).value.frame.ports.size=portsBound state.arena.code.size := by
  rw [prepare_value,ProductRows.prepare_frame,ProductBatch.generate_ports,PortEmbedding.initial_size]
  rfl

theorem prepare_count (state : ArenaSource.State) : (prepare state).value.frame.state.relations.length=state.relations.length := by
  rw [prepare_value,ProductRows.prepare_frame,ProductBatch.generate_count]
  rfl

theorem run_cells (state : ArenaSource.State) : (run state).cells ≤ runBudget state.arena.code.size state.relations.length := by
  let source := prepare state
  let nodes := inventoryBound state.arena.code.size
  let ports := portsBound state.arena.code.size
  let rowBound := ProductRows.rowBound state.arena.code.size
  have first := prepare_cells state
  have size := prepare_size state
  have width := prepare_ports state
  have count := prepare_count state
  have rows : rowsCells source.value.rows ≤ rowBound := by rw [prepare_value]; exact ProductRows.prepare_storage state
  have generated := iterate_cells_aux source.value.frame.state.arena.code.size source.value.frame.state.arena.code.size source.value.frame source.value.rows le_rfl
  change _ ≤ iterateBudget source.value.frame.state.arena.code.size source.value.frame.ports.size source.value.frame.state.relations.length
    (rowsCells source.value.rows) source.value.frame.state.arena.code.size at generated
  have work := generated.trans (iterateBudget_mono _ nodes _ ports _ state.relations.length _ rowBound _ nodes size width.le count.le rows size)
  have history := iterate_history source.value.frame.state.arena.code.size source.value.frame source.value.rows
  have kept := history.trans (show source.value.frame.state.arena.code.size*(source.value.frame.state.arena.code.size+9)+1 ≤ nodes*(nodes+9)+1 by gcongr)
  have joint := iterate_joint source.value.frame.state.arena.code.size source.value.frame source.value.rows
  have jointBound := joint.trans (show AffineCarrier.Cost.cellBound source.value.frame.state.arena.code.size+2 ≤ AffineCarrier.Cost.cellBound nodes+2 by unfold AffineCarrier.Cost.cellBound; gcongr)
  change source.cells ≤ _ at first
  change source.value.frame.state.arena.code.size ≤ nodes at size
  change source.value.frame.ports.size=ports at width
  change source.value.frame.state.relations.length=state.relations.length at count
  simp only [run]
  split <;> simp only [runBudget] <;> dsimp only [source,nodes,ports,rowBound] at * <;> omega

theorem runBudget_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : runBudget n c ≤ runBudget N C := by
  simp only [runBudget,prepareBudget,expandBudget,codeBudget,pairsBudget,seedBudget,equationsBudget,lawsBudget,gatesBudget,gateBudget,indexBudget,
    multipliedBudget,multiplyPoolBudget,multiplyBudget,JointCircuitCost.analysisBudget,JointCircuitCost.formulaBudget,
    JointCircuitCost.gatherBudget,JointCircuitCost.aliasRowBudget,ArenaCost.Reduction.budget,
    portsBound,inventoryBound,ProductRows.rowBound,AffineCarrier.Cost.cellBound]
  gcongr
  exact iterateBudget_mono _ _ _ _ _ _ _ _ _ _ (by gcongr) (by gcongr) hc (by gcongr) (by gcongr)

theorem run_payload (state : ArenaSource.State) : BranchCost.payload (run state).value ≤ (run state).cells+1 := by
  let source := prepare state
  let generated := iterate source.value.frame.state.arena.code.size source.value.frame source.value.rows
  have ports : generated.value.frame.ports.size=source.value.frame.ports.size := by rw [iterate_value,ProductRows.iterate_ports]
  have count : generated.value.frame.state.relations.length=source.value.frame.state.relations.length := by rw [iterate_value,ProductRows.iterate_count]
  have size : generated.value.frame.state.arena.code.size=source.value.frame.state.arena.code.size := by rw [iterate_value,ProductRows.iterate_size]
  by_cases rejected : source.value.rejected=true
  · have same : run state=⟨⟨source.value.frame,true,[],none⟩,source.cells+
      32*(source.value.frame.state.arena.code.size+source.value.frame.ports.size+source.value.frame.state.relations.length+rowsCells source.value.rows+1)+64⟩ := by
        simp only [run,show (prepare state).value.rejected=true from rejected,if_true]
        rfl
    rw [same]
    simp only [BranchCost.payload,ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_nil,JointCircuitCost.jointStorage]
    omega
  · have same : run state=⟨generated.value,source.cells+generated.cells+
      32*(source.value.frame.state.arena.code.size+source.value.frame.ports.size+source.value.frame.state.relations.length+rowsCells source.value.rows+
        ArenaCost.historySize generated.value.binding+JointCircuitCost.jointStorage generated.value.joint+1)+64⟩ := by
        simp only [run,if_neg (show ¬ (prepare state).value.rejected=true from rejected)]
        rfl
    rw [same]
    simp only [BranchCost.payload,ports,count,size]
    omega

def continueFrom (previous : PortUpdate.Output) : Counted PortUpdate.Output :=
  if previous.rejected then ⟨previous,32*(BranchCost.payload previous+1)+64⟩ else
    let generated := run previous.frame.state
    let output := PortUpdate.combine previous generated.value
    ⟨output,generated.cells+32*(BranchCost.payload previous+BranchCost.payload output+1)+64⟩

theorem continueFrom_value (previous : PortUpdate.Output) : (continueFrom previous).value=ProductRows.continueFrom previous := by
  simp only [continueFrom,run_value,ProductRows.continueFrom]
  split <;> rfl

def continueBudget (size : Nat) : Nat := runBudget size size+32*(2*size+runBudget size size+2)+64

theorem continueFrom_cells (previous : PortUpdate.Output) (size : Nat) (bound : BranchCost.payload previous ≤ size) :
    (continueFrom previous).cells ≤ continueBudget size := by
  have nodes : previous.frame.state.arena.code.size ≤ size := by unfold BranchCost.payload at bound; omega
  have count : previous.frame.state.relations.length ≤ size := by unfold BranchCost.payload at bound; omega
  have generated := (run_cells previous.frame.state).trans (runBudget_mono _ _ _ _ nodes count)
  have combined := BranchCost.combine_payload previous (run previous.frame.state).value
  have stored := run_payload previous.frame.state
  simp only [continueFrom,continueBudget]
  split <;> simp only <;> omega

theorem prior_continue_payload (previous : PortUpdate.Output) :
    BranchCost.payload (BranchCost.continueFrom previous).value ≤ (BranchCost.continueFrom previous).cells+1 := by
  simp only [BranchCost.continueFrom]
  split <;> simp only <;> omega

theorem prepared_payload {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    BranchCost.payload (BranchCost.compile formula basis).value ≤ (BranchCost.compile formula basis).cells+1 := by
  have source := prior_continue_payload (PortCost.compile formula basis).value
  simp only [BranchCost.compile]
  omega

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Counted PortUpdate.Output :=
  let previous := BranchCost.compile formula basis
  let generated := continueFrom previous.value
  ⟨generated.value,previous.cells+generated.cells⟩

theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Row) : (compile formula basis).value=ProductRows.compile formula basis := by
  simp only [compile,continueFrom_value,ProductRows.compile]

def compileBudget (n clauses literals basisSize : Nat) : Nat :=
  let front := BranchCost.compileBudget n clauses literals basisSize
  front+continueBudget (front+1)

theorem compile_cells {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).cells ≤ compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  let previous := BranchCost.compile formula basis
  let front := BranchCost.compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis)
  have first := BranchCost.compile_cells formula basis valid
  have kept := prepared_payload formula basis
  change previous.cells ≤ front at first
  change BranchCost.payload previous.value ≤ previous.cells+1 at kept
  have second := continueFrom_cells previous.value (front+1) (by omega)
  change previous.cells+(continueFrom previous.value).cells ≤ front+continueBudget (front+1)
  omega

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).value.value.read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  rw [compile_value]
  exact ProductRows.compile_read formula basis valid point

end SaturationMonoid.ComplexityProjection.SATSource.ProductCost

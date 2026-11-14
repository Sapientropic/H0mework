import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Closure.Cost.Source

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductClosureCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open CapacityMatching.RowCost (rowCells rowsCells)

theorem iterate_payload (fuel : Nat) (frame : Frame) (rows : List Row) :
    BranchCost.payload (ProductCost.iterate fuel frame rows).value ≤ frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+
      fuel*(frame.state.arena.code.size+9)+AffineCarrier.Cost.cellBound frame.state.arena.code.size+4 := by
  have history := ProductCost.iterate_history fuel frame rows
  have joint := ProductCost.iterate_joint fuel frame rows
  rw [ProductCost.iterate_value] at history joint
  rw [ProductCost.iterate_value]
  simp only [BranchCost.payload,ProductRows.iterate_ports,ProductRows.iterate_count,ProductRows.iterate_size]
  omega

def finish (inventory : Frame) : Result → Counted PortUpdate.Output
  | .contradiction =>
      let output : PortUpdate.Output := ⟨inventory,true,[],some .contradiction⟩
      ⟨output,32*(BranchCost.payload output+1)+64⟩
  | .basis basis =>
      let generated := ProductCost.iterate inventory.state.arena.code.size inventory basis
      ⟨generated.value,generated.cells+32*(inventory.state.arena.code.size+inventory.ports.size+inventory.state.relations.length+
        rowsCells basis+BranchCost.payload generated.value+1)+64⟩

theorem finish_value (inventory : Frame) (result : Result) : (finish inventory result).value=
    match result with
    | .contradiction => ⟨inventory,true,[],some .contradiction⟩
    | .basis basis => ProductRows.iterate inventory.state.arena.code.size inventory basis := by
  cases result <;> simp only [finish,ProductCost.iterate_value]

theorem finish_payload (inventory : Frame) (result : Result) :
    BranchCost.payload (finish inventory result).value ≤ (finish inventory result).cells+1 := by
  cases result <;> simp only [finish] <;> omega

def finishBudget (m p c : Nat) : Nat := ProductCost.iterateBudget m p c (AffineCarrier.Cost.cellBound m) m+
  32*(2*m+2*p+2*c+2*AffineCarrier.Cost.cellBound m+m*(m+9)+5)+64

theorem finish_cells (inventory : Frame) (result : Result)
    (valid : result.triangular ∧ result.within inventory.state.arena.code.size) :
    (finish inventory result).cells ≤ finishBudget inventory.state.arena.code.size inventory.ports.size inventory.state.relations.length := by
  cases result with
  | contradiction =>
      simp only [finish,finishBudget,BranchCost.payload,ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_nil,
        JointCircuitCost.jointStorage,AffineCarrier.resultSize]
      omega
  | basis basis =>
      have stored := AffineCarrier.Cost.cell_size inventory.state.arena.code.size basis valid.1 valid.2
      have rows : rowsCells basis ≤ AffineCarrier.Cost.cellBound inventory.state.arena.code.size := by unfold AffineCarrier.cellSize at stored; omega
      have first := ProductCost.iterate_cells_aux inventory.state.arena.code.size inventory.state.arena.code.size inventory basis le_rfl
      change _ ≤ ProductCost.iterateBudget _ _ _ _ _ at first
      have work := first.trans (ProductCost.iterateBudget_mono _ _ _ _ _ _ _ _ _ _ le_rfl le_rfl le_rfl rows le_rfl)
      have payload := iterate_payload inventory.state.arena.code.size inventory basis
      simp only [finish,finishBudget]
      omega

theorem finishBudget_mono (m M p P c C : Nat) (hm : m ≤ M) (hp : p ≤ P) (hc : c ≤ C) :
    finishBudget m p c ≤ finishBudget M P C := by
  unfold finishBudget
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact ProductCost.iterateBudget_mono _ _ _ _ _ _ _ _ _ _ hm hp hc (by unfold AffineCarrier.Cost.cellBound; gcongr) hm
  · unfold AffineCarrier.Cost.cellBound; gcongr

def close (original : Frame) (source : ProductRows.Prepared) : Counted Result :=
  if source.rejected then ⟨.contradiction,32*(context original source.frame+rowsCells source.rows+1)+64⟩
  else fromPrepared original source

theorem close_value (original : Frame) (source : ProductRows.Prepared) : (close original source).value=
    if source.rejected then .contradiction else ProductClosure.fromPrepared original source := by
  simp only [close]
  split
  · rfl
  · exact fromPrepared_value original source

theorem close_valid (original : Frame) (source : ProductRows.Prepared) :
    (close original source).value.triangular ∧ (close original source).value.within source.frame.state.arena.code.size := by
  simp only [close]
  split
  · exact ⟨trivial,trivial⟩
  · exact fromPrepared_valid original source

def closeBudget (n p c m q d s : Nat) : Nat := preparedBudget n p c m q d s+32*(n+p+c+m+q+d+s+1)+64

theorem close_cells (original : Frame) (source : ProductRows.Prepared) :
    (close original source).cells ≤ closeBudget original.state.arena.code.size original.ports.size original.state.relations.length
      source.frame.state.arena.code.size source.frame.ports.size source.frame.state.relations.length (rowsCells source.rows) := by
  have work := fromPrepared_cells original source
  simp only [close,closeBudget,context]
  split
  · dsimp only; omega
  · omega

theorem closeBudget_mono (n N p P c C m M q Q d D s S : Nat)
    (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) (hm : m ≤ M) (hq : q ≤ Q) (hd : d ≤ D) (hs : s ≤ S) :
    closeBudget n p c m q d s ≤ closeBudget N P C M Q D S := by
  unfold closeBudget
  have bound := preparedBudget_mono n N p P c C m M q Q d D s S hn hp hc hm hq hd hs
  gcongr

def run (state : ArenaSource.State) : Counted PortUpdate.Output :=
  let source := ProductCost.prepare state
  let closed := close (PortEmbedding.initial state) source.value
  let generated := finish (PortEmbedding.initial source.value.frame.state) closed.value
  ⟨generated.value,source.cells+closed.cells+generated.cells+
    32*(context (PortEmbedding.initial state) source.value.frame+rowsCells source.value.rows+
      AffineCarrier.resultSize closed.value+BranchCost.payload generated.value+1)+64⟩

theorem run_value (state : ArenaSource.State) : (run state).value=ProductClosed.run state := by
  simp only [run,close_value,ProductClosed.run]
  split <;> simp only [finish_value]
  rfl

def runBudget (n c : Nat) : Nat :=
  let m := ProductCost.inventoryBound n
  let p := ProductCost.portsBound n
  let s := ProductRows.rowBound n
  let closed := closeBudget n n c m p c s
  let done := finishBudget m m c
  ProductCost.prepareBudget n c+closed+done+32*(2*n+2*c+m+p+s+AffineCarrier.Cost.cellBound m+done+3)+64

theorem run_cells (state : ArenaSource.State) : (run state).cells ≤ runBudget state.arena.code.size state.relations.length := by
  let source := ProductCost.prepare state
  let original := PortEmbedding.initial state
  let inventory := PortEmbedding.initial source.value.frame.state
  let closed := close original source.value
  let generated := finish inventory closed.value
  let m := ProductCost.inventoryBound state.arena.code.size
  let p := ProductCost.portsBound state.arena.code.size
  let s := ProductRows.rowBound state.arena.code.size
  have first := ProductCost.prepare_cells state
  have size := ProductCost.prepare_size state
  have ports := ProductCost.prepare_ports state
  have count := ProductCost.prepare_count state
  have rows : rowsCells source.value.rows ≤ s := by rw [ProductCost.prepare_value]; exact ProductRows.prepare_storage state
  have second := close_cells original source.value
  have secondBound := second.trans (closeBudget_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ le_rfl (by rw [PortEmbedding.initial_size]) le_rfl size ports.le count.le rows)
  have valid := close_valid original source.value
  have third := finish_cells inventory closed.value valid
  have thirdBound := third.trans (finishBudget_mono _ m _ m _ state.relations.length size (by rw [PortEmbedding.initial_size]; exact size) count.le)
  have stored := AffineCarrier.Cost.result_size source.value.frame.state.arena.code.size closed.value valid.1 valid.2
  have storage := stored.trans (show AffineCarrier.Cost.cellBound source.value.frame.state.arena.code.size+1 ≤ AffineCarrier.Cost.cellBound m+1 by
    unfold AffineCarrier.Cost.cellBound; gcongr)
  have payload := finish_payload inventory closed.value
  change generated.cells ≤ finishBudget m m state.relations.length at thirdBound
  change BranchCost.payload generated.value ≤ generated.cells+1 at payload
  change closed.cells ≤ closeBudget state.arena.code.size state.arena.code.size state.relations.length m p state.relations.length s at secondBound
  change source.cells ≤ _ at first
  change source.value.frame.state.arena.code.size ≤ m at size
  change source.value.frame.ports.size=p at ports
  change source.value.frame.state.relations.length=state.relations.length at count
  change source.cells+closed.cells+generated.cells+
    32*(context original source.value.frame+rowsCells source.value.rows+AffineCarrier.resultSize closed.value+BranchCost.payload generated.value+1)+64 ≤ _
  simp only [context,original,PortEmbedding.initial,Array.size_ofFn,runBudget]
  dsimp only [m,p,s] at *
  omega

theorem run_payload (state : ArenaSource.State) : BranchCost.payload (run state).value ≤ (run state).cells+1 := by
  simp only [run]
  omega

attribute [local gcongr] JointCircuitCost.jointBudget_mono JointCircuitCost.formulaStorage_mono
  preparedBudget_mono closeBudget_mono finishBudget_mono

theorem sourceBudget_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) :
    ProductCost.prepareBudget n c ≤ ProductCost.prepareBudget N C := by
  simp only [ProductCost.prepareBudget,ProductCost.expandBudget,ProductCost.codeBudget,ProductCost.pairsBudget,
    ProductCost.seedBudget,ProductCost.equationsBudget,ProductCost.lawsBudget,ProductCost.gatesBudget,ProductCost.gateBudget,ProductCost.indexBudget,
    ProductCost.multipliedBudget,ProductCost.multiplyPoolBudget,ProductCost.multiplyBudget,JointCircuitCost.analysisBudget,JointCircuitCost.formulaBudget,
    JointCircuitCost.gatherBudget,JointCircuitCost.aliasRowBudget,ArenaCost.Reduction.budget,ProductRows.rowBound,AffineCarrier.Cost.cellBound]
  gcongr

attribute [local gcongr] sourceBudget_mono

theorem runBudget_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : runBudget n c ≤ runBudget N C := by
  simp only [runBudget,ProductCost.inventoryBound,ProductCost.portsBound,ProductRows.rowBound,AffineCarrier.Cost.cellBound]
  gcongr

def continueFrom (previous : PortUpdate.Output) : Counted PortUpdate.Output :=
  if previous.rejected then ⟨previous,32*(BranchCost.payload previous+1)+64⟩ else
    let generated := run previous.frame.state
    let output := PortUpdate.combine previous generated.value
    ⟨output,generated.cells+32*(BranchCost.payload previous+BranchCost.payload output+1)+64⟩

theorem continueFrom_value (previous : PortUpdate.Output) : (continueFrom previous).value=ProductClosed.continueFrom previous := by
  simp only [continueFrom,run_value,ProductClosed.continueFrom]
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

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Counted PortUpdate.Output :=
  let previous := BranchCost.compile formula basis
  let generated := continueFrom previous.value
  ⟨generated.value,previous.cells+generated.cells⟩

theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Row) : (compile formula basis).value=ProductClosed.compile formula basis := by
  simp only [compile,continueFrom_value,ProductClosed.compile]

def compileBudget (n clauses literals basisSize : Nat) : Nat :=
  let front := BranchCost.compileBudget n clauses literals basisSize
  front+continueBudget (front+1)

theorem compile_cells {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).cells ≤ compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  let previous := BranchCost.compile formula basis
  let front := BranchCost.compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis)
  have first := BranchCost.compile_cells formula basis valid
  have kept := ProductCost.prepared_payload formula basis
  change previous.cells ≤ front at first
  change BranchCost.payload previous.value ≤ previous.cells+1 at kept
  have second := continueFrom_cells previous.value (front+1) (by omega)
  change previous.cells+(continueFrom previous.value).cells ≤ front+continueBudget (front+1)
  omega

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).value.value.read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  rw [compile_value]
  exact ProductClosed.compile_read formula basis valid point

theorem compile_decision {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    PortUpdate.stateDecision (compile formula basis).value.frame.state (compile formula basis).value.rejected=true ↔
      ∃ point, CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point)=true := by
  have same := compile_value formula basis
  rw [same]
  exact ProductClosed.decide_correct formula basis valid

end SaturationMonoid.ComplexityProjection.SATSource.ProductClosureCost

import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Branch.Cost.Source

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.BranchCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open FunctionalSubstitution (Instruction)

def iterate : Nat → Frame → List Instruction → Counted PortUpdate.Output
  | 0,frame,calls => ⟨⟨frame,false,[],none⟩,32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+ArenaCost.historySize calls+1)+48⟩
  | fuel+1,frame,calls =>
      let first := update frame calls
      if first.value.binding.isEmpty then
        ⟨first.value,first.cells+32*(first.value.frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
          ArenaCost.historySize calls+ArenaCost.historySize first.value.binding+1)+48⟩
      else
        let tail := iterate fuel first.value.frame calls
        ⟨PortUpdate.combine first.value tail.value,first.cells+tail.cells+
          32*(tail.value.frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+ArenaCost.historySize calls+
            ArenaCost.historySize first.value.binding+ArenaCost.historySize tail.value.binding+1)+48⟩

theorem iterate_value (fuel : Nat) (frame : Frame) (calls : List Instruction) :
    (iterate fuel frame calls).value=BranchPorts.iterate fuel frame calls := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih => simp only [iterate,update_value,ih,BranchPorts.iterate]; split <;> rfl

theorem update_capacity (fuel limit : Nat) (frame : Frame) (calls : List Instruction)
    (capacity : frame.state.arena.code.size+(fuel+1)*(ArenaCost.historySize calls+1) ≤ limit) :
    (update frame calls).value.frame.state.arena.code.size+fuel*(ArenaCost.historySize calls+1) ≤ limit := by
  have size := update_size frame calls
  nlinarith

theorem iterate_size (fuel : Nat) (frame : Frame) (calls : List Instruction) :
    (iterate fuel frame calls).value.frame.state.arena.code.size ≤ frame.state.arena.code.size+fuel*(ArenaCost.historySize calls+1) := by
  induction fuel generalizing frame with
  | zero => simp [iterate]
  | succ fuel ih =>
      have first := update_size frame calls
      have tail := ih (update frame calls).value.frame
      simp only [iterate]
      split
      · nlinarith
      · change (iterate fuel (update frame calls).value.frame calls).value.frame.state.arena.code.size ≤ _
        nlinarith

theorem iterate_history (fuel limit : Nat) (frame : Frame) (calls : List Instruction)
    (capacity : frame.state.arena.code.size+fuel*(ArenaCost.historySize calls+1) ≤ limit) :
    ArenaCost.historySize (iterate fuel frame calls).value.binding ≤ fuel*(limit+ArenaCost.historySize calls+10)+1 := by
  induction fuel generalizing frame with
  | zero => simp [iterate,ArenaCost.historySize]
  | succ fuel ih =>
      have first := update_history frame calls
      have current : frame.state.arena.code.size ≤ limit := by omega
      have tail := ih (update frame calls).value.frame (update_capacity fuel limit frame calls capacity)
      have joined := JointCircuitCost.history_append (update frame calls).value.binding (iterate fuel (update frame calls).value.frame calls).value.binding
      simp only [iterate]
      split
      · nlinarith
      · change ArenaCost.historySize ((update frame calls).value.binding++(iterate fuel (update frame calls).value.frame calls).value.binding) ≤ _
        nlinarith

def roundBudget (n p c s rounds : Nat) : Nat := updateBudget n p c s+32*(n+c+p+s+(rounds+1)*(n+s+10)+3)+48
def iterateBudget (n p c s rounds : Nat) : Nat := (rounds+1)*roundBudget n p c s rounds

theorem iterate_cells_aux (fuel rounds limit : Nat) (frame : Frame) (calls : List Instruction) (enough : fuel ≤ rounds)
    (capacity : frame.state.arena.code.size+fuel*(ArenaCost.historySize calls+1) ≤ limit) :
    (iterate fuel frame calls).cells ≤ (fuel+1)*roundBudget limit frame.ports.size frame.state.relations.length (ArenaCost.historySize calls) rounds := by
  induction fuel generalizing frame with
  | zero => simp only [iterate,roundBudget]; omega
  | succ fuel ih =>
      have current : frame.state.arena.code.size ≤ limit := by omega
      have first := (update_cells frame calls).trans (updateBudget_mono _ limit _ _ _ _ _ _ current le_rfl le_rfl le_rfl)
      have history := update_history frame calls
      have nextCapacity := update_capacity fuel limit frame calls capacity
      have firstSize : (update frame calls).value.frame.state.arena.code.size ≤ limit := by omega
      have ports : (update frame calls).value.frame.ports.size=frame.ports.size := by rw [update_value,BranchPorts.update_ports]
      have count : (update frame calls).value.frame.state.relations.length=frame.state.relations.length := by rw [update_value,BranchPorts.update_count]
      have later := ih (update frame calls).value.frame (by omega) nextCapacity
      rw [ports,count] at later
      have lastSize := (iterate_size fuel (update frame calls).value.frame calls).trans nextCapacity
      have kept := (iterate_history fuel limit (update frame calls).value.frame calls nextCapacity).trans
        (show fuel*(limit+ArenaCost.historySize calls+10)+1 ≤ rounds*(limit+ArenaCost.historySize calls+10)+1 by gcongr; omega)
      simp only [iterate]
      split
      · have this : (update frame calls).cells+32*((update frame calls).value.frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
            ArenaCost.historySize calls+ArenaCost.historySize (update frame calls).value.binding+1)+48 ≤
              roundBudget limit frame.ports.size frame.state.relations.length (ArenaCost.historySize calls) rounds := by
          unfold roundBudget
          nlinarith only [first,history,current,firstSize]
        exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
      · simp only [roundBudget] at later ⊢
        nlinarith only [first,history,later,kept,current,lastSize]

attribute [local gcongr] updateBudget_mono forcedBudget_mono BranchPorts.poolBound_mono BranchPorts.inventoryBound_mono
  JointCircuitCost.formulaStorage_mono

theorem generateBudget_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : generateBudget n c ≤ generateBudget N C := by
  simp only [generateBudget,JointCircuitCost.formulaBudget,JointCircuitCost.gatherBudget,JointCircuitCost.aliasRowBudget]
  gcongr

theorem iterateBudget_mono (n N p P c C s S r R : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) (hs : s ≤ S) (hr : r ≤ R) :
    iterateBudget n p c s r ≤ iterateBudget N P C S R := by
  simp only [iterateBudget,roundBudget]
  gcongr

def run (state : ArenaSource.State) : Counted PortUpdate.Output :=
  let source := BranchPorts.generate state
  let generated := iterate state.arena.code.size (PortEmbedding.initial state) source.value
  ⟨generated.value,source.cells+generated.cells+16*(state.arena.code.size+ArenaCost.historySize source.value+1)+
    32*(generated.value.frame.state.arena.code.size+state.relations.length+state.arena.code.size+ArenaCost.historySize generated.value.binding+1)+48⟩

theorem run_value (state : ArenaSource.State) : (run state).value=BranchPorts.run state := by
  simp only [run,iterate_value,BranchPorts.run]

def runBudget (n c : Nat) : Nat :=
  let s := BranchPorts.poolBound n c
  let size := BranchPorts.inventoryBound n c
  generateBudget n c+iterateBudget size n c s n+16*(n+s+1)+32*(size+c+n+n*(size+s+10)+2)+48

theorem run_cells (state : ArenaSource.State) : (run state).cells ≤ runBudget state.arena.code.size state.relations.length := by
  let source := BranchPorts.generate state
  let size := BranchPorts.inventoryBound state.arena.code.size state.relations.length
  let bound := BranchPorts.poolBound state.arena.code.size state.relations.length
  have poolSize := BranchPorts.generate_storage state
  have capacity : state.arena.code.size+state.arena.code.size*(ArenaCost.historySize source.value+1) ≤ size := by
    dsimp only [size,BranchPorts.inventoryBound]
    gcongr
  have first := generate_cells state
  have generated := iterate_cells_aux state.arena.code.size state.arena.code.size size (PortEmbedding.initial state) source.value le_rfl capacity
  simp only [PortEmbedding.initial_size] at generated
  change _ ≤ iterateBudget size state.arena.code.size state.relations.length (ArenaCost.historySize source.value) state.arena.code.size at generated
  have work := generated.trans (iterateBudget_mono _ _ _ _ _ _ _ bound _ _ le_rfl le_rfl le_rfl poolSize le_rfl)
  have history := iterate_history state.arena.code.size size (PortEmbedding.initial state) source.value capacity
  have kept := history.trans (show state.arena.code.size*(size+ArenaCost.historySize source.value+10)+1 ≤ state.arena.code.size*(size+bound+10)+1 by gcongr)
  have finalSize := (iterate_size state.arena.code.size (PortEmbedding.initial state) source.value).trans capacity
  change source.cells+(iterate state.arena.code.size (PortEmbedding.initial state) source.value).cells+
    16*(state.arena.code.size+ArenaCost.historySize source.value+1)+
      32*((iterate state.arena.code.size (PortEmbedding.initial state) source.value).value.frame.state.arena.code.size+state.relations.length+
        state.arena.code.size+ArenaCost.historySize (iterate state.arena.code.size (PortEmbedding.initial state) source.value).value.binding+1)+48 ≤ _
  change source.cells ≤ _ at first
  change ArenaCost.historySize source.value ≤ bound at poolSize
  change _ ≤ generateBudget state.arena.code.size state.relations.length+iterateBudget size state.arena.code.size state.relations.length bound state.arena.code.size+
    16*(state.arena.code.size+bound+1)+32*(size+state.relations.length+state.arena.code.size+state.arena.code.size*(size+bound+10)+2)+48
  omega

attribute [local gcongr] generateBudget_mono iterateBudget_mono

theorem runBudget_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : runBudget n c ≤ runBudget N C := by
  simp only [runBudget]
  gcongr

def payload (output : PortUpdate.Output) : Nat := output.frame.state.arena.code.size+output.frame.state.relations.length+
  output.frame.ports.size+ArenaCost.historySize output.binding+JointCircuitCost.jointStorage output.joint+1

theorem combine_payload (first second : PortUpdate.Output) : payload (PortUpdate.combine first second) ≤ payload first+payload second := by
  have history := JointCircuitCost.history_append first.binding second.binding
  simp only [PortUpdate.combine,payload]
  omega

theorem iterate_joint (fuel : Nat) (frame : Frame) (calls : List Instruction) : (iterate fuel frame calls).value.joint=none := by
  rw [iterate_value]
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih =>
      simp only [BranchPorts.iterate]
      split
      · simp only [BranchPorts.update]; split <;> rfl
      · exact ih _

theorem run_payload (state : ArenaSource.State) : payload (run state).value ≤ (run state).cells+1 := by
  let source := BranchPorts.generate state
  let generated := iterate state.arena.code.size (PortEmbedding.initial state) source.value
  have ports : generated.value.frame.ports.size=state.arena.code.size := by
    rw [iterate_value,BranchPorts.iterate_ports,PortEmbedding.initial_size]
  have count : generated.value.frame.state.relations.length=state.relations.length := by
    rw [iterate_value,BranchPorts.iterate_count]
    rfl
  have joint := iterate_joint state.arena.code.size (PortEmbedding.initial state) source.value
  change payload generated.value ≤ source.cells+generated.cells+16*(state.arena.code.size+ArenaCost.historySize source.value+1)+
    32*(generated.value.frame.state.arena.code.size+state.relations.length+state.arena.code.size+ArenaCost.historySize generated.value.binding+1)+48+1
  unfold payload
  rw [ports,count]
  change generated.value.joint=none at joint
  rw [joint]
  simp only [JointCircuitCost.jointStorage]
  omega

def continueFrom (previous : PortUpdate.Output) : Counted PortUpdate.Output :=
  if previous.rejected then ⟨previous,32*(payload previous+1)+64⟩ else
    let generated := run previous.frame.state
    let output := PortUpdate.combine previous generated.value
    ⟨output,generated.cells+32*(payload previous+payload output+1)+64⟩

theorem continueFrom_value (previous : PortUpdate.Output) : (continueFrom previous).value=BranchPorts.continueFrom previous := by
  simp only [continueFrom,run_value,BranchPorts.continueFrom,PortUpdate.combine]
  split <;> rfl

def continueBudget (size : Nat) : Nat := runBudget size size+32*(2*size+runBudget size size+2)+64

theorem continueFrom_cells (previous : PortUpdate.Output) (size : Nat) (bound : payload previous ≤ size) :
    (continueFrom previous).cells ≤ continueBudget size := by
  have nodes : previous.frame.state.arena.code.size ≤ size := by unfold payload at bound; omega
  have count : previous.frame.state.relations.length ≤ size := by unfold payload at bound; omega
  have generated := (run_cells previous.frame.state).trans (runBudget_mono _ _ _ _ nodes count)
  have combined := combine_payload previous (run previous.frame.state).value
  have stored := run_payload previous.frame.state
  simp only [continueFrom,continueBudget]
  split <;> simp only <;> omega

theorem prior_continue_payload (previous : JointCircuit.Update) :
    payload (PortCost.continueFrom previous).value ≤ (PortCost.continueFrom previous).cells+1 := by
  have ports : (PortCost.run previous.state).value.frame.ports.size=previous.state.arena.code.size := by
    rw [PortCost.run_value]
    exact (PortUpdate.iterate_ports _ _).trans (PortEmbedding.initial_size previous.state)
  have count : (PortCost.run previous.state).value.frame.state.relations.length=previous.state.relations.length := by
    rw [PortCost.run_value]
    exact PortUpdate.iterate_count _ _
  have history := JointCircuitCost.history_append previous.binding (PortCost.run previous.state).value.binding
  by_cases rejected : previous.rejected=true
  · have same : PortCost.continueFrom previous=⟨⟨PortEmbedding.initial previous.state,true,previous.binding,previous.joint⟩,
        32*(2*previous.state.arena.code.size+previous.state.relations.length+
          ArenaCost.historySize previous.binding+JointCircuitCost.jointStorage previous.joint+1)+64⟩ := by
      simp only [PortCost.continueFrom,rejected,if_true]
    rw [same]
    simp only [payload,PortEmbedding.initial,Array.size_ofFn]
    omega
  · have same : PortCost.continueFrom previous=⟨⟨(PortCost.run previous.state).value.frame,(PortCost.run previous.state).value.rejected,
        previous.binding++(PortCost.run previous.state).value.binding,(PortCost.run previous.state).value.joint⟩,
          (PortCost.run previous.state).cells+32*((PortCost.run previous.state).value.frame.state.arena.code.size+
            previous.state.relations.length+previous.state.arena.code.size+ArenaCost.historySize previous.binding+
              ArenaCost.historySize (PortCost.run previous.state).value.binding+
                JointCircuitCost.jointStorage (PortCost.run previous.state).value.joint+1)+64⟩ := by
      simp only [PortCost.continueFrom,if_neg rejected]
    rw [same]
    simp only [payload,ports,count]
    omega

theorem prepared_payload {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    payload (PortCost.compile formula basis).value ≤ (PortCost.compile formula basis).cells+1 := by
  have bound := prior_continue_payload (JointRelationCost.compile formula basis).value
  simp only [PortCost.compile]
  omega

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Counted PortUpdate.Output :=
  let previous := PortCost.compile formula basis
  let generated := continueFrom previous.value
  ⟨generated.value,previous.cells+generated.cells⟩

theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Row) : (compile formula basis).value=BranchPorts.compile formula basis := by
  simp only [compile,continueFrom_value,BranchPorts.compile]

def compileBudget (n clauses literals basisSize : Nat) : Nat :=
  let front := PortCost.compileBudget n clauses literals basisSize
  front+continueBudget (front+1)

theorem compile_cells {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).cells ≤ compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  let previous := PortCost.compile formula basis
  let front := PortCost.compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis)
  have first := PortCost.compile_cells formula basis valid
  have kept := prepared_payload formula basis
  change previous.cells ≤ front at first
  change payload previous.value ≤ previous.cells+1 at kept
  have second := continueFrom_cells previous.value (front+1) (by omega)
  change previous.cells+(continueFrom previous.value).cells ≤ front+continueBudget (front+1)
  omega

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).value.value.read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  rw [compile_value]
  exact BranchPorts.compile_read formula basis valid point

end SaturationMonoid.ComplexityProjection.SATSource.BranchCost

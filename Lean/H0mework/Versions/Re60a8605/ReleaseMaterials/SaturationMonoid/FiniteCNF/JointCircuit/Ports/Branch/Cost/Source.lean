import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Branch

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.BranchCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open FunctionalSubstitution (Instruction)
abbrev Counted := ArenaCost.Counted

attribute [local gcongr] JointCircuitCost.jointBudget_mono

theorem forcedBudget_mono (n N m M e E b B : Nat) (hn : n ≤ N) (hm : m ≤ M) (he : e ≤ E) (hb : b ≤ B) :
    ForcedBranches.Cost.generateBudget n m e b ≤ ForcedBranches.Cost.generateBudget N M E B := by
  simp only [ForcedBranches.Cost.generateBudget,ForcedBranches.Cost.branchesBudget,ForcedBranches.Cost.branchBudget,
    ForcedBranches.Cost.branchStorage,ForcedBranches.Cost.forceBudget,ForcedBranches.Cost.forceStorage,ForcedBranches.Cost.outputStorage,
    ConditionalCandidateCost.Functional.candidatesBudget,ConditionalCandidateCost.Functional.relationsBudget,
    ConditionalCandidateCost.Functional.relationRound,ConditionalCandidateCost.Functional.filterBudget,
    ConditionalCandidateCost.Functional.chooseBudget,ConditionalCandidateCost.Functional.callsBudget,
    ConditionalCandidateCost.Functional.callBudget,ConditionalCandidateCost.Functional.callSize,ConditionalCandidateCost.Functional.callsStorage,
    ConditionalCandidateCost.branchBudget,ConditionalCandidateCost.splitBudget,ConditionalCandidateCost.widthBudget,
    ConditionalCandidateCost.branchStorage,ConditionalCandidateCost.makeCallsBudget,ConditionalCandidateCost.instructionBudget,
    ConditionalCandidateCost.instructionBound,ConditionalCandidateCost.bodyScale,ConditionalCandidateCost.priorStorage,
    ConditionalCandidateCost.Code.conditionalBudget,ConditionalCandidateCost.Code.expressionBudget,ConditionalCandidateCost.Code.findBudget,
    ConditionalCandidateCost.Code.xorBudget,ConditionalCandidateCost.Code.compileBudget,ConditionalCandidateCost.Code.functionalBudget,
    ConditionalCandidateCost.Code.relationBudget,ConditionalCandidateCost.Code.literalBudget,
    AffineCollect.Cost.coordinateBudget,AffineCarrier.Cost.cellBound,AffineRelationExtractionCost.branchBudget,
    CapacityMatching.RowCost.decodeBudget,CapacityMatching.RowCost.decodeUnit,
    FunctionalSchedule.Cost.entriesBudget,FunctionalSchedule.Cost.entryBudget,FunctionalSchedule.Cost.eligibleBudget,
    EliminateCost.insertCellBudget,EliminateCost.reduceCellBudget]
  gcongr

def generateBudget (n c : Nat) : Nat :=
  4*n+1+JointCircuitCost.formulaBudget n c+
    ForcedBranches.Cost.generateBudget n (JointCircuitCost.formulaStorage n c) (JointCircuitCost.formulaStorage n c) 1+
      16*(JointCircuitCost.formulaStorage n c+1+BranchPorts.poolBound n c+n+c+1)+24

theorem generate_cells (state : ArenaSource.State) :
    (BranchPorts.generate state).cells ≤ generateBudget state.arena.code.size state.relations.length := by
  have checked := JointCircuitCost.checked_cells state.arena.code.toList
  simp only [Array.length_toList] at checked
  have source := JointCircuitCost.formula_cells state
  have size := JointCircuitCost.formula_storage state
  have measures := JointCircuitCost.storage_measures (JointCircuitCost.formula state).value
  have calls := (ForcedBranches.Cost.generate_cells (JointCircuitCost.formula state).value [] ⟨triangular_nil,by simp [RowsWithin]⟩).trans
    (forcedBudget_mono _ _ _ _ _ _ _ _ le_rfl (measures.1.trans size) (measures.2.trans size) le_rfl)
  change (ForcedBranches.generate (JointCircuitCost.formula state).value []).cells ≤ ForcedBranches.Cost.generateBudget
    state.arena.code.size (JointCircuitCost.formulaStorage state.arena.code.size state.relations.length)
      (JointCircuitCost.formulaStorage state.arena.code.size state.relations.length) 1 at calls
  have stored := BranchPorts.generate_storage state
  simp only [BranchPorts.generate] at stored ⊢
  split
  · rename_i running
    simp only [if_pos running] at stored
    simp only
    change (JointCircuitCost.checked state.arena.code.toList).cells+(JointCircuitCost.formula state).cells+
      (ForcedBranches.generate (JointCircuitCost.formula state).value []).cells+
        16*(JointCircuitCost.storage (JointCircuitCost.formula state).value+1+
          ArenaCost.historySize (ForcedBranches.generate (JointCircuitCost.formula state).value []).value+
            state.arena.code.size+state.relations.length+1)+24 ≤ _
    unfold generateBudget
    omega
  · simp only [generateBudget]; omega

def fromCall (frame : Frame) (call : Instruction) : Counted (Option (PortRelations.Offer frame)) :=
  if call.address < frame.ports.size then
    let input := PortEmbedding.ref frame.state frame.ports call.address
    match JointCircuit.node frame.state input with
    | .input address =>
        let offer : PortRelations.Offer frame := ⟨input,address,call.body⟩
        let checked := PortCost.allowed frame offer
        ⟨if checked.value then some offer else none,checked.cells+
          16*(frame.ports.size+frame.state.arena.code.size+call.body.code.size+1)+24⟩
    | _ => ⟨none,16*(frame.ports.size+frame.state.arena.code.size+call.body.code.size+1)+24⟩
  else ⟨none,16*(frame.ports.size+call.body.code.size+1)+24⟩

theorem fromCall_value (frame : Frame) (call : Instruction) : (fromCall frame call).value=BranchPorts.fromCall frame call := by
  simp only [fromCall,BranchPorts.fromCall,PortCost.allowed_value]
  split
  · split <;> simp_all
  · simp_all

def callBudget (n p c b : Nat) : Nat := PortCost.allowedBudget n p c b+16*(p+n+b+1)+24

theorem fromCall_cells (frame : Frame) (call : Instruction) :
    (fromCall frame call).cells ≤ callBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length call.body.code.size := by
  simp only [fromCall]
  split
  · split
    · rename_i address shape
      have checked := PortCost.allowed_cells frame
        (⟨PortEmbedding.ref frame.state frame.ports call.address,address,call.body⟩ : PortRelations.Offer frame)
      simp only at checked
      simp only [callBudget]
      omega
    all_goals simp only [callBudget]; omega
  · simp only [callBudget]; omega

theorem fromCall_storage (frame : Frame) (call : Instruction) :
    PortCost.offerSize (fromCall frame call).value ≤ call.body.code.size+9 := by
  simp only [fromCall]
  split
  · split
    · split <;> simp only [PortCost.offerSize] <;> omega
    all_goals simp only [PortCost.offerSize]; omega
  · simp only [PortCost.offerSize]; omega

def choose (frame : Frame) : List Instruction → Counted (Option (PortRelations.Offer frame))
  | [] => ⟨none,1⟩
  | call::rest =>
      let first := fromCall frame call
      match first.value with
      | some offer => ⟨some offer,first.cells+16*(call.body.code.size+PortCost.offerSize first.value+1)+24⟩
      | none =>
          let tail := choose frame rest
          ⟨tail.value,first.cells+tail.cells+16*(call.body.code.size+PortCost.offerSize tail.value+1)+24⟩

theorem choose_value (frame : Frame) (calls : List Instruction) : (choose frame calls).value=BranchPorts.choose frame calls := by
  induction calls with
  | nil => rfl
  | cons call rest ih => simp only [choose,fromCall_value,ih,BranchPorts.choose]; split <;> simp_all

theorem choose_storage (frame : Frame) (calls : List Instruction) :
    PortCost.offerSize (choose frame calls).value ≤ ArenaCost.historySize calls+9 := by
  induction calls with
  | nil => simp [choose,PortCost.offerSize,ArenaCost.historySize]
  | cons call rest ih =>
      have first := fromCall_storage frame call
      simp only [choose]
      cases found : (fromCall frame call).value with
      | some offer => simp only [found] at first; simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_cons,FunctionalSchedule.Cost.instructionSize]; omega
      | none => simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_cons] at ih ⊢; omega

theorem callBudget_mono (n N p P c C b B : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) (hb : b ≤ B) :
    callBudget n p c b ≤ callBudget N P C B := by
  unfold callBudget
  gcongr
  exact PortCost.allowedBudget_mono _ _ _ _ _ _ _ _ hn hp hc hb

def chooseBudget (n p c s : Nat) : Nat := s*(callBudget n p c s+16*(2*s+10)+24)+1

theorem choose_cells_aux (frame : Frame) (calls : List Instruction) (s : Nat) (bound : ArenaCost.historySize calls ≤ s) :
    (choose frame calls).cells ≤ calls.length*(callBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length s+16*(2*s+10)+24)+1 := by
  induction calls with
  | nil => simp [choose]
  | cons call rest ih =>
      have pieces : call.body.code.size+8+ArenaCost.historySize rest ≤ s := bound
      have tail := ih (by omega)
      have tailStored := choose_storage frame rest
      have firstStored := fromCall_storage frame call
      have first := (fromCall_cells frame call).trans (callBudget_mono _ _ _ _ _ _ _ _ le_rfl le_rfl le_rfl (by omega : call.body.code.size ≤ s))
      simp only [choose,List.length_cons]
      cases found : (fromCall frame call).value with
      | none => simp only; nlinarith
      | some offer => simp only [found] at firstStored; simp only; nlinarith

theorem calls_length (calls : List Instruction) : calls.length ≤ ArenaCost.historySize calls := by
  induction calls with
  | nil => simp [ArenaCost.historySize]
  | cons call rest ih => simp only [ArenaCost.historySize,FunctionalSchedule.Cost.inputSize_cons,FunctionalSchedule.Cost.instructionSize,List.length_cons] at ih ⊢; omega

theorem choose_cells (frame : Frame) (calls : List Instruction) :
    (choose frame calls).cells ≤ chooseBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length (ArenaCost.historySize calls) :=
  (choose_cells_aux frame calls _ le_rfl).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (calls_length calls)) 1)

def update (frame : Frame) (calls : List Instruction) : Counted PortUpdate.Output :=
  let chosen := choose frame calls
  match chosen.value with
  | none => ⟨⟨frame,false,[],none⟩,chosen.cells+32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+ArenaCost.historySize calls+1)+48⟩
  | some offer =>
      let changed := PortCost.perform frame offer
      ⟨changed.value,chosen.cells+changed.cells+32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
        ArenaCost.historySize calls+PortCost.offerSize chosen.value+1)+48⟩

theorem update_value (frame : Frame) (calls : List Instruction) : (update frame calls).value=BranchPorts.update frame calls := by
  simp only [update,choose_value,PortCost.perform_value,BranchPorts.update]
  split <;> simp_all

def updateBudget (n p c s : Nat) : Nat := chooseBudget n p c s+PortCost.performBudget n p c s+32*(n+c+p+2*s+10)+48

theorem update_cells (frame : Frame) (calls : List Instruction) :
    (update frame calls).cells ≤ updateBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length (ArenaCost.historySize calls) := by
  have first := choose_cells frame calls
  have stored := choose_storage frame calls
  simp only [update]
  cases chosen : (choose frame calls).value with
  | none => simp only [updateBudget]; omega
  | some offer =>
      simp only [chosen,PortCost.offerSize] at stored
      have body : offer.body.code.size ≤ ArenaCost.historySize calls := by omega
      have changed := (PortCost.perform_cells frame offer).trans
        (PortCost.performBudget_mono _ _ _ _ _ _ _ _ le_rfl le_rfl le_rfl body)
      simp only [updateBudget]
      simp only [PortCost.offerSize]
      omega

theorem update_history (frame : Frame) (calls : List Instruction) :
    ArenaCost.historySize (update frame calls).value.binding ≤ frame.state.arena.code.size+ArenaCost.historySize calls+10 := by
  have stored := choose_storage frame calls
  simp only [update]
  cases chosen : (choose frame calls).value with
  | none => simp [ArenaCost.historySize]
  | some offer =>
      simp only [chosen,PortCost.offerSize] at stored
      have body : offer.body.code.size ≤ ArenaCost.historySize calls := by omega
      have size := PortEmbedding.append_size frame.state frame.ports offer.body
      have actual := ArenaAction.actualBody_size offer.emission.target.arena offer.emission.root
      rw [PortCost.perform_value]
      change (ArenaAction.actualBody offer.emission.target.arena offer.emission.root).code.size+9 ≤ _
      change offer.emission.target.arena.code.size ≤ _ at size
      omega

theorem update_size (frame : Frame) (calls : List Instruction) :
    (update frame calls).value.frame.state.arena.code.size ≤ frame.state.arena.code.size+ArenaCost.historySize calls+1 := by
  have stored := choose_storage frame calls
  simp only [update]
  cases chosen : (choose frame calls).value with
  | none => simp only; omega
  | some offer =>
      simp only [chosen,PortCost.offerSize] at stored
      have size := PortUpdate.perform_size frame offer
      rw [PortCost.perform_value]
      omega

attribute [local gcongr] PortCost.performBudget_mono callBudget_mono

theorem updateBudget_mono (n N p P c C s S : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) (hs : s ≤ S) :
    updateBudget n p c s ≤ updateBudget N P C S := by
  simp only [updateBudget,chooseBudget]
  gcongr

end SaturationMonoid.ComplexityProjection.SATSource.BranchCost

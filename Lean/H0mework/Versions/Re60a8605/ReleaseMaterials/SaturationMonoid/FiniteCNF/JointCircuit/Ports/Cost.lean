import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Cost.Source

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.PortCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)

def movePorts (mapping : Array Nat) : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | root::rest =>
      let found := ArenaCost.lookup mapping root
      let tail := movePorts mapping rest
      ⟨found.value::tail.value,found.cells+tail.cells+8*tail.value.length+16⟩

theorem movePorts_value (mapping : Array Nat) (roots : List Nat) :
    (movePorts mapping roots).value=roots.map (fun root => mapping.getD root 0) := by
  induction roots <;> simp_all only [movePorts,ArenaCost.lookup,List.map_nil,List.map_cons]

theorem movePorts_cells (mapping : Array Nat) (roots : List Nat) :
    (movePorts mapping roots).cells ≤ roots.length*(2*mapping.size+8*roots.length+20)+1 := by
  induction roots with
  | nil => simp [movePorts]
  | cons root rest ih => simp only [movePorts,ArenaCost.lookup,movePorts_value,List.length_map,List.length_cons]; nlinarith

def bind (frame : Frame) (address : Nat) (root : Fin frame.state.arena.code.size) : Counted Frame :=
  let action := ArenaCost.applyFrame frame.state.arena address root
  let changed := ArenaCost.next frame.state address root
  let ports := movePorts action.value.frame.mapping (frame.ports.toList.map Fin.val)
  ⟨PortEmbedding.bind frame address root,2*(action.cells+changed.cells+ports.cells)+
    32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+1)+48⟩

theorem bind_value (frame : Frame) (address : Nat) (root : Fin frame.state.arena.code.size) :
    (bind frame address root).value=PortEmbedding.bind frame address root := rfl

def bindBudget (n p c : Nat) : Nat :=
  2*(ArenaCost.applyBudget n+ArenaCost.nextBudget n c+p*(2*n+8*p+20)+1)+32*(n+c+p+1)+48

theorem bind_cells (frame : Frame) (address : Nat) (root : Fin frame.state.arena.code.size) :
    (bind frame address root).cells ≤ bindBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length := by
  have first := ArenaCost.applyFrame_cells frame.state.arena address root
  have second := ArenaCost.next_cells frame.state address root
  have ports := movePorts_cells (ArenaCost.applyFrame frame.state.arena address root).value.frame.mapping (frame.ports.toList.map Fin.val)
  rw [ArenaCost.applyFrame_mapping_size] at ports
  simp only [List.length_map,Array.length_toList] at ports
  simp only [bind,bindBudget]
  omega

def oldStep (frame : Frame) : Counted PortUpdate.Output :=
  let checked := JointCircuitCost.checked frame.state.arena.code.toList
  if checked.value then
    let source := JointCircuitCost.analyzed frame.state
    match source.value with
    | .contradiction => ⟨⟨frame,true,[],some source.value⟩,checked.cells+source.cells+32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+1)+48⟩
    | .basis basis =>
        let picked := JointCircuitCost.pick frame.state basis
        match picked.value with
        | none => ⟨⟨frame,false,[],some source.value⟩,checked.cells+source.cells+picked.cells+
            32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+AffineCarrier.cellSize basis+1)+48⟩
        | some item =>
            let changed := bind frame item.address item.relation.right
            let body := ArenaCost.Dependency.compact (ArenaAction.focus frame.state.arena.code item.relation.right)
            ⟨⟨changed.value,false,[ArenaSource.selected frame.state item],some source.value⟩,
              checked.cells+source.cells+picked.cells+changed.cells+2*body.cells+
                32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+AffineCarrier.cellSize basis+body.value.code.size+1)+48⟩
  else ⟨⟨frame,false,[],none⟩,checked.cells+32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+1)+48⟩

theorem oldStep_value (frame : Frame) : (oldStep frame).value=PortUpdate.oldStep frame := by
  simp only [oldStep,PortUpdate.oldStep,JointCircuitCost.checked_value,JointCircuit.noAdd,
    JointCircuitCost.analyzed_value,JointCircuitCost.pick_value,bind_value]
  split
  · split
    · simp_all
    · split <;> simp_all
  · simp_all

def oldStepBudget (n p c : Nat) : Nat := 4*n+1+JointCircuitCost.analysisBudget n c+JointCircuitCost.pickBudget n+
  bindBudget n p c+2*ArenaCost.Dependency.budget n+32*(n+c+p+AffineCarrier.Cost.cellBound n+n+1)+48

theorem oldStep_cells (frame : Frame) : (oldStep frame).cells ≤ oldStepBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length := by
  have checked := JointCircuitCost.checked_cells frame.state.arena.code.toList
  simp only [Array.length_toList] at checked
  have source := JointCircuitCost.analyzed_cells frame.state
  have valid := JointCircuitCost.analyzed_valid frame.state
  simp only [oldStep]
  split
  · cases result : (JointCircuitCost.analyzed frame.state).value with
    | contradiction => simp only [oldStepBudget]; omega
    | basis basis =>
        have vb : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis := by simpa only [result,Result.triangular,Result.within] using valid
        have stored := AffineCarrier.Cost.cell_size frame.state.arena.code.size basis vb.1 vb.2
        have picked := JointCircuitCost.pick_cells frame.state basis vb
        cases chosen : (JointCircuitCost.pick frame.state basis).value with
        | none => simp only [chosen,oldStepBudget]; omega
        | some item =>
            have changed := bind_cells frame item.address item.relation.right
            have body := ArenaCost.Dependency.compact_cells (ArenaAction.focus frame.state.arena.code item.relation.right)
            change _ ≤ ArenaCost.Dependency.budget frame.state.arena.code.size at body
            have size := ArenaAction.actualBody_size frame.state.arena item.relation.right
            rw [← ArenaCost.body_code] at size
            simp only [chosen,oldStepBudget]
            omega
  · simp only [oldStepBudget]; omega

def perform (frame : Frame) (offer : PortRelations.Offer frame) : Counted PortUpdate.Output :=
  let emitted := append frame offer.body
  let moved := movePorts emitted.value.mapping (frame.ports.toList.map Fin.val)
  let extended : Frame := ⟨emitted.value.target,frame.ports.map emitted.value.ref⟩
  let changed := bind extended offer.address emitted.value.root
  let item : ArenaSource.Labeled emitted.value.target.arena := ⟨offer.address,⟨emitted.value.ref offer.input,emitted.value.root⟩⟩
  let body := ArenaCost.Dependency.compact (ArenaAction.focus emitted.value.target.arena.code emitted.value.root)
  ⟨⟨changed.value,false,[ArenaSource.selected emitted.value.target item],none⟩,
    emitted.cells+2*moved.cells+changed.cells+2*body.cells+
      32*(emitted.value.target.arena.code.size+frame.state.relations.length+frame.ports.size+body.value.code.size+1)+48⟩

theorem perform_value (frame : Frame) (offer : PortRelations.Offer frame) : (perform frame offer).value=PortUpdate.perform frame offer := by
  simp only [perform,append_value,bind_value,PortUpdate.perform,PortEmbedding.extend,PortUpdate.selected,
    PortRelations.Offer.emission,PortRelations.Offer.item]

def performBudget (n p c b : Nat) : Nat :=
  appendBudget n p c b+2*(p*(2*(n+b)+8*p+20)+1)+bindBudget (n+b+1) p c+
    2*ArenaCost.Dependency.budget (n+b+1)+32*((n+b+1)+c+p+(n+b+1)+1)+48

theorem bindBudget_mono (n N p P c C : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) :
    bindBudget n p c ≤ bindBudget N P C := by
  simp only [bindBudget,ArenaCost.nextBudget,ArenaCost.applyBudget,ArenaCost.Dependency.budget,ArenaCost.inputsBudget,ArenaCost.Rewiring.budget]
  gcongr

theorem perform_cells (frame : Frame) (offer : PortRelations.Offer frame) :
    (perform frame offer).cells ≤ performBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length offer.body.code.size := by
  let emitted := append frame offer.body
  let extended : Frame := ⟨emitted.value.target,frame.ports.map emitted.value.ref⟩
  have first := append_cells frame offer.body
  have size := PortEmbedding.append_size frame.state frame.ports offer.body
  change emitted.value.target.arena.code.size ≤ _ at size
  have count := PortEmbedding.append_count frame.state frame.ports offer.body
  change emitted.value.target.relations.length=frame.state.relations.length at count
  have mapping : emitted.value.mapping.size=frame.state.arena.code.size+offer.body.code.size := by
    have same := ArenaCost.reduction_mapping_size (PortEmbedding.code frame.state frame.ports offer.body)
    rw [ArenaCost.Reduction.compact_value,PortEmbedding.code_size] at same
    exact same
  have ports := movePorts_cells emitted.value.mapping (frame.ports.toList.map Fin.val)
  simp only [List.length_map,Array.length_toList,mapping] at ports
  have extendedPorts : extended.ports.size=frame.ports.size := Array.size_map
  have changed := (bind_cells extended offer.address emitted.value.root).trans
    (bindBudget_mono _ _ _ _ _ _ size (by rw [extendedPorts]) (by rw [count]))
  have body := ArenaCost.Dependency.compact_cells (ArenaAction.focus emitted.value.target.arena.code emitted.value.root)
  change _ ≤ ArenaCost.Dependency.budget emitted.value.target.arena.code.size at body
  have bodyBound : (ArenaCost.Dependency.compact (ArenaAction.focus emitted.value.target.arena.code emitted.value.root)).cells ≤
      ArenaCost.Dependency.budget (frame.state.arena.code.size+offer.body.code.size+1) := body.trans (by unfold ArenaCost.Dependency.budget; gcongr)
  have bodySize := ArenaAction.actualBody_size emitted.value.target.arena emitted.value.root
  rw [← ArenaCost.body_code] at bodySize
  change emitted.cells+2*(movePorts emitted.value.mapping (frame.ports.toList.map Fin.val)).cells+
    (bind extended offer.address emitted.value.root).cells+
    2*(ArenaCost.Dependency.compact (ArenaAction.focus emitted.value.target.arena.code emitted.value.root)).cells+
      32*(emitted.value.target.arena.code.size+frame.state.relations.length+frame.ports.size+
        (ArenaCost.Dependency.compact (ArenaAction.focus emitted.value.target.arena.code emitted.value.root)).value.code.size+1)+48 ≤ _
  change emitted.cells ≤ _ at first
  unfold performBudget
  omega

def update (frame : Frame) : Counted PortUpdate.Output :=
  let previous := oldStep frame
  if JointRelationUpdate.usePrevious previous.value.value then
    ⟨previous.value,previous.cells+32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
      ArenaCost.historySize previous.value.binding+JointCircuitCost.jointStorage previous.value.joint+1)+48⟩
  else
    let fresh := generate frame
    match fresh.value with
    | none => ⟨previous.value,previous.cells+fresh.cells+32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
        ArenaCost.historySize previous.value.binding+JointCircuitCost.jointStorage previous.value.joint+1)+48⟩
    | some offer =>
        let changed := perform frame offer
        ⟨changed.value,previous.cells+fresh.cells+changed.cells+32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
          offer.body.code.size+ArenaCost.historySize previous.value.binding+JointCircuitCost.jointStorage previous.value.joint+1)+48⟩

theorem update_value (frame : Frame) : (update frame).value=PortUpdate.update frame := by
  simp only [update,oldStep_value,generate_value,perform_value,PortUpdate.update]
  split
  · simp_all
  · split <;> simp_all

theorem oldStep_history (frame : Frame) : ArenaCost.historySize (oldStep frame).value.binding ≤ frame.state.arena.code.size+9 := by
  have paid := JointCircuitCost.update_history frame.state
  rw [JointCircuitCost.update_value,← PortUpdate.oldStep_value] at paid
  rw [oldStep_value]
  exact paid

theorem oldStep_joint (frame : Frame) :
    JointCircuitCost.jointStorage (oldStep frame).value.joint ≤ AffineCarrier.Cost.cellBound frame.state.arena.code.size+2 := by
  have paid := JointCircuitCost.update_joint frame.state
  rw [JointCircuitCost.update_value,← PortUpdate.oldStep_value] at paid
  rw [oldStep_value]
  exact paid

def updateBudget (n p c : Nat) : Nat := oldStepBudget n p c+generateBudget n p c+performBudget n p c (2*p+1)+
  32*(n+c+p+(2*p+1)+(n+9)+AffineCarrier.Cost.cellBound n+3)+48

theorem performBudget_mono (n N p P c C b B : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) (hb : b ≤ B) :
    performBudget n p c b ≤ performBudget N P C B := by
  unfold performBudget appendBudget codeBudget ArenaCost.Reduction.budget ArenaCost.Dependency.budget
  gcongr
  exact bindBudget_mono _ _ _ _ _ _ (by omega) hp hc

theorem update_cells (frame : Frame) :
    (update frame).cells ≤ updateBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length := by
  have first := oldStep_cells frame
  have second := generate_cells frame
  have history := oldStep_history frame
  have joint := oldStep_joint frame
  simp only [update]
  split
  · simp only [updateBudget]; omega
  · cases found : (generate frame).value with
    | none => simp only [updateBudget]; omega
    | some offer =>
        have body := (PortRelations.generate_spec frame offer (by rw [← generate_value,found])).2.1
        have changed := (perform_cells frame offer).trans
          (performBudget_mono _ _ _ _ _ _ _ _ le_rfl le_rfl le_rfl body)
        simp only [updateBudget]
        omega

theorem update_history (frame : Frame) :
    ArenaCost.historySize (update frame).value.binding ≤ frame.state.arena.code.size+2*frame.ports.size+11 := by
  have old := oldStep_history frame
  simp only [update]
  split
  · simpa only using old.trans (by omega)
  · cases found : (generate frame).value with
    | none => simpa only using old.trans (by omega)
    | some offer =>
        have body := (PortRelations.generate_spec frame offer (by rw [← generate_value,found])).2.1
        have size := PortEmbedding.append_size frame.state frame.ports offer.body
        have selectedSize := ArenaAction.actualBody_size offer.emission.target.arena offer.emission.root
        rw [perform_value]
        change (ArenaSource.selected offer.emission.target offer.item).body.code.size+9 ≤ _
        change (ArenaAction.actualBody offer.emission.target.arena offer.emission.root).code.size+9 ≤ _
        change offer.emission.target.arena.code.size ≤ _ at size
        omega

theorem update_joint (frame : Frame) :
    JointCircuitCost.jointStorage (update frame).value.joint ≤ AffineCarrier.Cost.cellBound frame.state.arena.code.size+2 := by
  have old := oldStep_joint frame
  simp only [update]
  split
  · exact old
  · split
    · exact old
    · rw [perform_value]; simp [PortUpdate.perform,JointCircuitCost.jointStorage]

attribute [local gcongr] JointCircuitCost.jointBudget_mono JointCircuitCost.formulaStorage_mono
  eligibleBudget_mono bindBudget_mono performBudget_mono

theorem updateBudget_mono (n N p P c C : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) :
    updateBudget n p c ≤ updateBudget N P C := by
  simp only [updateBudget,oldStepBudget,generateBudget,scanBudget,inputBudget,independentBudget,rowsBudget,
    tableBudget,selectBudget,imageBudget,imageVisitsBudget,scanRowBudget,bodyBudget,allowedBudget,appendBudget,codeBudget,
    ConditionalCandidateCost.Code.compileBudget,JointCircuitCost.analysisBudget,JointCircuitCost.formulaBudget,
    JointCircuitCost.aliasRowBudget,JointCircuitCost.gatherBudget,JointCircuitCost.pickBudget,JointCircuitCost.rootBudget,
    JointCircuitCost.linkBudget,ArenaCost.Dependency.budget,ArenaCost.Reduction.budget,
    AffineForget.Cost.imageWorkspace,AffineCollect.Cost.coordinateBudget,AffineCarrier.Cost.cellBound,
    EliminateCost.reduceCellBudget,AtomImage.stepBudget]
  gcongr

def iterate : Nat → Frame → Counted PortUpdate.Output
  | 0,frame => ⟨⟨frame,false,[],none⟩,32*(frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+1)+48⟩
  | fuel+1,frame =>
      let first := update frame
      if JointIteration.done first.value.value then
        ⟨first.value,first.cells+32*(first.value.frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
          ArenaCost.historySize first.value.binding+JointCircuitCost.jointStorage first.value.joint+1)+48⟩
      else
        let tail := iterate fuel first.value.frame
        ⟨PortUpdate.combine first.value tail.value,first.cells+tail.cells+
          32*(tail.value.frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
            ArenaCost.historySize first.value.binding+ArenaCost.historySize tail.value.binding+JointCircuitCost.jointStorage tail.value.joint+1)+48⟩

theorem iterate_value (fuel : Nat) (frame : Frame) : (iterate fuel frame).value=PortUpdate.iterate fuel frame := by
  induction fuel generalizing frame with
  | zero => rfl
  | succ fuel ih => simp only [iterate,update_value,ih,PortUpdate.iterate]; split <;> rfl

theorem update_capacity (fuel limit : Nat) (frame : Frame)
    (capacity : frame.state.arena.code.size+(fuel+1)*(2*frame.ports.size+2) ≤ limit) :
    (update frame).value.frame.state.arena.code.size+fuel*(2*(update frame).value.frame.ports.size+2) ≤ limit := by
  have size := PortUpdate.update_size frame
  rw [update_value,PortUpdate.update_ports]
  nlinarith

theorem iterate_history (fuel limit : Nat) (frame : Frame)
    (capacity : frame.state.arena.code.size+fuel*(2*frame.ports.size+2) ≤ limit) :
    ArenaCost.historySize (iterate fuel frame).value.binding ≤ fuel*(limit+2*frame.ports.size+11)+1 := by
  induction fuel generalizing frame with
  | zero => simp [iterate,ArenaCost.historySize]
  | succ fuel ih =>
      have first := update_history frame
      have current : frame.state.arena.code.size ≤ limit := by omega
      have tail := ih (update frame).value.frame (update_capacity fuel limit frame capacity)
      have ports : (update frame).value.frame.ports.size=frame.ports.size := by rw [update_value,PortUpdate.update_ports]
      rw [ports] at tail
      have joined := JointCircuitCost.history_append (update frame).value.binding (iterate fuel (update frame).value.frame).value.binding
      simp only [iterate]
      split
      · nlinarith
      · change ArenaCost.historySize ((update frame).value.binding++(iterate fuel (update frame).value.frame).value.binding) ≤ _
        nlinarith

theorem iterate_joint (fuel limit : Nat) (frame : Frame)
    (capacity : frame.state.arena.code.size+fuel*(2*frame.ports.size+2) ≤ limit) :
    JointCircuitCost.jointStorage (iterate fuel frame).value.joint ≤ AffineCarrier.Cost.cellBound limit+2 := by
  induction fuel generalizing frame with
  | zero => simp [iterate,JointCircuitCost.jointStorage]
  | succ fuel ih =>
      have current : frame.state.arena.code.size ≤ limit := by omega
      have first := (update_joint frame).trans (show AffineCarrier.Cost.cellBound frame.state.arena.code.size+2 ≤
        AffineCarrier.Cost.cellBound limit+2 by unfold AffineCarrier.Cost.cellBound; gcongr)
      have tail := ih (update frame).value.frame (update_capacity fuel limit frame capacity)
      simp only [iterate]
      split
      · exact first
      · exact tail

def roundBudget (n p c rounds : Nat) : Nat :=
  updateBudget n p c+32*(n+c+p+(rounds+1)*(n+2*p+11)+AffineCarrier.Cost.cellBound n+5)+48

def iterateBudget (n p c rounds : Nat) : Nat := (rounds+1)*roundBudget n p c rounds

set_option maxRecDepth 2000 in
theorem iterate_cells_aux (fuel rounds limit : Nat) (frame : Frame) (enough : fuel ≤ rounds)
    (capacity : frame.state.arena.code.size+fuel*(2*frame.ports.size+2) ≤ limit) :
    (iterate fuel frame).cells ≤ (fuel+1)*roundBudget limit frame.ports.size frame.state.relations.length rounds := by
  induction fuel generalizing frame with
  | zero => simp only [iterate,roundBudget]; omega
  | succ fuel ih =>
      have current : frame.state.arena.code.size ≤ limit := by omega
      have first := (update_cells frame).trans (updateBudget_mono _ limit _ _ _ _ current le_rfl le_rfl)
      have history := update_history frame
      have joint := (update_joint frame).trans (show AffineCarrier.Cost.cellBound frame.state.arena.code.size+2 ≤
        AffineCarrier.Cost.cellBound limit+2 by unfold AffineCarrier.Cost.cellBound; gcongr)
      have nextCapacity := update_capacity fuel limit frame capacity
      have firstSize : (update frame).value.frame.state.arena.code.size ≤ limit := by omega
      have ports : (update frame).value.frame.ports.size=frame.ports.size := by rw [update_value,PortUpdate.update_ports]
      have count : (update frame).value.frame.state.relations.length=frame.state.relations.length := by rw [update_value,PortUpdate.update_count]
      have later := ih (update frame).value.frame (by omega) nextCapacity
      rw [ports,count] at later
      have tailSize := PortUpdate.iterate_size fuel (update frame).value.frame
      rw [← iterate_value] at tailSize
      have lastSize : (iterate fuel (update frame).value.frame).value.frame.state.arena.code.size ≤ limit := tailSize.trans nextCapacity
      have tailHistory := iterate_history fuel limit (update frame).value.frame nextCapacity
      rw [ports] at tailHistory
      have kept : ArenaCost.historySize (iterate fuel (update frame).value.frame).value.binding ≤ rounds*(limit+2*frame.ports.size+11)+1 :=
        tailHistory.trans (by gcongr; omega)
      have tailJoint := iterate_joint fuel limit (update frame).value.frame nextCapacity
      simp only [iterate]
      split
      · have this : (update frame).cells+32*((update frame).value.frame.state.arena.code.size+frame.state.relations.length+frame.ports.size+
            ArenaCost.historySize (update frame).value.binding+JointCircuitCost.jointStorage (update frame).value.joint+1)+48 ≤
              roundBudget limit frame.ports.size frame.state.relations.length rounds := by
          unfold roundBudget
          nlinarith only [first,history,joint,current,firstSize]
        exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
      · simp only [roundBudget] at later ⊢
        nlinarith only [first,history,later,kept,tailJoint,current,lastSize]

def capacity (n : Nat) : Nat := 2*n*n+3*n

theorem initial_capacity (state : ArenaSource.State) :
    (PortEmbedding.initial state).state.arena.code.size+state.arena.code.size*(2*(PortEmbedding.initial state).ports.size+2) ≤ capacity state.arena.code.size := by
  simp only [PortEmbedding.initial,Array.size_ofFn,capacity]
  nlinarith

def run (state : ArenaSource.State) : Counted PortUpdate.Output :=
  let output := iterate state.arena.code.size (PortEmbedding.initial state)
  ⟨output.value,output.cells+16*state.arena.code.size+16+
    32*(output.value.frame.state.arena.code.size+state.relations.length+state.arena.code.size+
      ArenaCost.historySize output.value.binding+JointCircuitCost.jointStorage output.value.joint+1)+48⟩

theorem run_value (state : ArenaSource.State) : (run state).value=PortUpdate.run state := by
  simp only [run,iterate_value,PortUpdate.run]

def runBudget (n c : Nat) : Nat := iterateBudget (capacity n) n c n+16*n+16+
  32*(capacity n+c+n+n*(capacity n+2*n+11)+AffineCarrier.Cost.cellBound (capacity n)+4)+48

theorem run_cells (state : ArenaSource.State) : (run state).cells ≤ runBudget state.arena.code.size state.relations.length := by
  have work := iterate_cells_aux state.arena.code.size state.arena.code.size (capacity state.arena.code.size)
    (PortEmbedding.initial state) le_rfl (initial_capacity state)
  have history := iterate_history state.arena.code.size (capacity state.arena.code.size) (PortEmbedding.initial state) (initial_capacity state)
  have joint := iterate_joint state.arena.code.size (capacity state.arena.code.size) (PortEmbedding.initial state) (initial_capacity state)
  have size := PortUpdate.run_size state
  rw [← run_value] at size
  simp only [PortEmbedding.initial_size] at work history
  change (iterate state.arena.code.size (PortEmbedding.initial state)).cells ≤
    (state.arena.code.size+1)*roundBudget (capacity state.arena.code.size) state.arena.code.size state.relations.length state.arena.code.size at work
  change (iterate state.arena.code.size (PortEmbedding.initial state)).value.frame.state.arena.code.size ≤ _ at size
  change _ ≤ capacity state.arena.code.size at size
  simp only [run,runBudget,iterateBudget]
  omega

attribute [local gcongr] updateBudget_mono

theorem runBudget_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : runBudget n c ≤ runBudget N C := by
  simp only [runBudget,iterateBudget,roundBudget,capacity,AffineCarrier.Cost.cellBound]
  gcongr

def continueFrom (previous : JointCircuit.Update) : Counted PortUpdate.Output :=
  if previous.rejected then
    ⟨⟨PortEmbedding.initial previous.state,true,previous.binding,previous.joint⟩,
      32*(2*previous.state.arena.code.size+previous.state.relations.length+
        ArenaCost.historySize previous.binding+JointCircuitCost.jointStorage previous.joint+1)+64⟩
  else
    let next := run previous.state
    ⟨⟨next.value.frame,next.value.rejected,previous.binding++next.value.binding,next.value.joint⟩,
      next.cells+32*(next.value.frame.state.arena.code.size+previous.state.relations.length+previous.state.arena.code.size+
        ArenaCost.historySize previous.binding+ArenaCost.historySize next.value.binding+JointCircuitCost.jointStorage next.value.joint+1)+64⟩

theorem continueFrom_value (previous : JointCircuit.Update) : (continueFrom previous).value=PortUpdate.continueFrom previous := by
  simp only [continueFrom,run_value,PortUpdate.continueFrom]
  split <;> rfl

def continueBudget (n c history joint : Nat) : Nat := runBudget n c+
  32*(capacity n+c+n+history+n*(capacity n+2*n+11)+AffineCarrier.Cost.cellBound (capacity n)+joint+4)+64

theorem continueFrom_cells (previous : JointCircuit.Update) :
    (continueFrom previous).cells ≤ continueBudget previous.state.arena.code.size previous.state.relations.length
      (ArenaCost.historySize previous.binding) (JointCircuitCost.jointStorage previous.joint) := by
  have work := run_cells previous.state
  have history := iterate_history previous.state.arena.code.size (capacity previous.state.arena.code.size)
    (PortEmbedding.initial previous.state) (initial_capacity previous.state)
  have joint := iterate_joint previous.state.arena.code.size (capacity previous.state.arena.code.size)
    (PortEmbedding.initial previous.state) (initial_capacity previous.state)
  have size := PortUpdate.run_size previous.state
  rw [← run_value] at size
  change (run previous.state).value.frame.state.arena.code.size ≤ capacity previous.state.arena.code.size at size
  simp only [PortEmbedding.initial_size] at history
  change ArenaCost.historySize (run previous.state).value.binding ≤ _ at history
  change JointCircuitCost.jointStorage (run previous.state).value.joint ≤ _ at joint
  have sourceSize : previous.state.arena.code.size ≤ capacity previous.state.arena.code.size := by unfold capacity; nlinarith
  simp only [continueFrom,continueBudget]
  split <;> simp only <;> omega

theorem continueBudget_mono (n N c C h H j J : Nat) (hn : n ≤ N) (hc : c ≤ C) (hh : h ≤ H) (hj : j ≤ J) :
    continueBudget n c h j ≤ continueBudget N C H J := by
  simp only [continueBudget,capacity,AffineCarrier.Cost.cellBound]
  gcongr
  exact runBudget_mono _ _ _ _ hn hc

theorem prepared_history_cells {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    ArenaCost.historySize (JointRelationCost.compile formula basis).value.binding ≤ (JointRelationCost.compile formula basis).cells+1 := by
  let source := ArenaTotal.Cost.compile formula basis
  let generated := JointRelationCost.run source.value.state
  have joined := JointCircuitCost.history_append source.value.instructions generated.value.binding
  change ArenaCost.historySize (source.value.instructions++generated.value.binding) ≤ source.cells+generated.cells+
    32*(source.value.state.arena.code.size+source.value.state.relations.length+
      ArenaCost.historySize source.value.instructions+ArenaCost.historySize generated.value.binding+JointCircuitCost.jointStorage generated.value.joint+1)+48+1
  omega

theorem prepared_joint_cells {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    JointCircuitCost.jointStorage (JointRelationCost.compile formula basis).value.joint ≤ (JointRelationCost.compile formula basis).cells+1 := by
  simp only [JointRelationCost.compile]
  omega

theorem prepared_count {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (JointRelationCost.compile formula basis).value.state.relations.length ≤ 3*formula.length+n*n := by
  rw [JointRelationCost.compile_value]
  change (JointRelationUpdate.iterate (ArenaTotal.Cost.compile formula basis).value.state.arena.code.size
    (ArenaTotal.Cost.compile formula basis).value.state).state.relations.length ≤ _
  rw [JointRelationUpdate.iterate_count,ArenaTotal.Cost.compile_count]
  exact ForcedBranches.Cost.generate_length formula basis

def compile {n : Nat} (formula : CNFFormula n) (basis : List Row) : Counted PortUpdate.Output :=
  let previous := JointRelationCost.compile formula basis
  let generated := continueFrom previous.value
  ⟨generated.value,previous.cells+generated.cells⟩

theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Row) :
    (compile formula basis).value=PortUpdate.compile formula basis := by
  simp only [compile,continueFrom_value,PortUpdate.compile]

def compileBudget (n clauses literals basisSize : Nat) : Nat :=
  let nodes := capacity (ArenaSource.sourceBound n clauses literals)
  let previous := JointRelationCost.compileBudget n clauses literals basisSize
  previous+continueBudget nodes (3*clauses+n*n) (previous+1) (previous+1)

theorem compile_cells {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) :
    (compile formula basis).cells ≤ compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  let previous := JointRelationCost.compile formula basis
  let nodes := capacity (ArenaSource.sourceBound n formula.length (Extract.literalCount formula))
  let budget := JointRelationCost.compileBudget n formula.length (Extract.literalCount formula) (AffineCarrier.cellSize basis)
  have first := JointRelationCost.compile_cells formula basis valid
  change previous.cells ≤ budget at first
  have size : previous.value.state.arena.code.size ≤ nodes := by
    rw [JointRelationCost.compile_value]
    exact JointRelationUpdate.compile_size formula basis valid
  have count := prepared_count formula basis
  have history := prepared_history_cells formula basis
  have joint := prepared_joint_cells formula basis
  change ArenaCost.historySize previous.value.binding ≤ previous.cells+1 at history
  change JointCircuitCost.jointStorage previous.value.joint ≤ previous.cells+1 at joint
  have second := (continueFrom_cells previous.value).trans
    (continueBudget_mono _ nodes _ (3*formula.length+n*n) _ (budget+1) _ (budget+1) size count (by omega) (by omega))
  change previous.cells+(continueFrom previous.value).cells ≤ budget+continueBudget nodes (3*formula.length+n*n) (budget+1) (budget+1)
  omega

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin n basis) (point : Nat → Bool) :
    (compile formula basis).value.value.read point=CNFFormula.eval formula (Gates.coordinate (Table.coordinates n basis) point) := by
  rw [compile_value]
  exact PortUpdate.compile_read formula basis valid point

theorem compile_settled {n : Nat} (formula : CNFFormula n) (basis : List Row) : PortUpdate.Settled (compile formula basis).value := by
  rw [compile_value]
  exact PortUpdate.compile_settled formula basis

end SaturationMonoid.ComplexityProjection.SATSource.PortCost

import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Arena.Cost.Cone

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ArenaCost
open InterferenceProgram
open FunctionalSubstitution (Instruction)

theorem inputsBudget_mono (a b : Nat) (bounded : a ≤ b) : inputsBudget a ≤ inputsBudget b := by
  have square := Nat.mul_self_le_mul_self bounded
  unfold inputsBudget
  nlinarith

def free (address : Nat) (code : Array Node) : Counted Bool :=
  let found := inputs code
  let member := has address found.value
  ⟨!member.value,found.cells+member.cells+2*found.value.length+8⟩

theorem free_value (address : Nat) (code : Array Node) :
    (free address code).value=decide (address ∉ FunctionalSubstitution.inputs code) := by
  simp only [free,has,AffineClauseProduct.Cost.member_value,inputs_value]
  by_cases member : address ∈ FunctionalSubstitution.inputs code <;> simp [member]

theorem free_cells (address : Nat) (code : Array Node) :
    (free address code).cells ≤ inputsBudget code.size+4*code.size+9 := by
  have first := inputs_cells code
  have count := inputs_length code
  have member := has_cells address (inputs code).value
  simp only [free]
  omega

theorem body_code (arena : ArenaAction.Arena) (root : Fin arena.code.size) :
    (Dependency.compact (ArenaAction.focus arena.code root)).value.code=(ArenaAction.actualBody arena root).code := by
  rw [Dependency.compact_value]
  rfl

def eligible (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena) : Counted Bool :=
  if state.arena.code.getD item.relation.left.val (.constant 0)=.input item.address then
    let body := Dependency.compact (ArenaAction.focus state.arena.code item.relation.right)
    let allowed := free item.address body.value.code
    ⟨allowed.value,body.cells+allowed.cells+20*state.arena.code.size+60⟩
  else ⟨false,8*state.arena.code.size+20⟩

theorem eligible_value (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena) :
    (eligible state item).value=ArenaSource.eligible state item := by
  simp only [eligible,ArenaSource.eligible]
  split <;> simp_all only [decide_true,Bool.true_and,decide_false,Bool.false_and,free_value,body_code]

def eligibleBudget (nodes : Nat) : Nat := Dependency.budget nodes+inputsBudget nodes+24*nodes+69

theorem eligible_cells (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena) :
    (eligible state item).cells ≤ eligibleBudget state.arena.code.size := by
  have body := Dependency.compact_cells (ArenaAction.focus state.arena.code item.relation.right)
  have freeWork := free_cells item.address (Dependency.compact (ArenaAction.focus state.arena.code item.relation.right)).value.code
  rw [body_code] at freeWork
  have size := ArenaAction.actualBody_size state.arena item.relation.right
  have bound := inputsBudget_mono _ _ size
  dsimp only [eligible]
  split
  · dsimp only
    change _ ≤ Dependency.budget state.arena.code.size at body
    rw [body_code]
    unfold eligibleBudget
    omega
  · dsimp only
    unfold eligibleBudget
    omega

def chooseFrom (state : ArenaSource.State) : List (ArenaSource.Labeled state.arena) → Counted (Option (ArenaSource.Labeled state.arena))
  | [] => ⟨none,1⟩
  | item::rest =>
      let first := eligible state item
      if first.value then ⟨some item,first.cells+10⟩ else
        let tail := chooseFrom state rest
        ⟨tail.value,first.cells+tail.cells+10⟩

theorem chooseFrom_value (state : ArenaSource.State) (items : List (ArenaSource.Labeled state.arena)) :
    (chooseFrom state items).value=items.find? (ArenaSource.eligible state) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
      simp only [chooseFrom,eligible_value,List.find?_cons]
      split <;> simp_all

theorem chooseFrom_cells (state : ArenaSource.State) (items : List (ArenaSource.Labeled state.arena)) :
    (chooseFrom state items).cells ≤ items.length*(eligibleBudget state.arena.code.size+10)+1 := by
  induction items with
  | nil => simp [chooseFrom]
  | cons item rest ih =>
      have first := eligible_cells state item
      simp only [chooseFrom,List.length_cons]
      split <;> simp only <;> nlinarith

def choose (state : ArenaSource.State) : Counted (Option (ArenaSource.Labeled state.arena)) := chooseFrom state state.relations

theorem choose_value (state : ArenaSource.State) : (choose state).value=ArenaSource.choose state :=
  chooseFrom_value state state.relations

structure Applied where
  frame : Cone.Frame
  performed : Bool

def applyFrame (arena : ArenaAction.Arena) (address : Nat) (root : Fin arena.code.size) : Counted Applied :=
  let body := Dependency.compact (ArenaAction.focus arena.code root)
  let allowed := free address body.value.code
  if allowed.value then
    let output := Rewiring.rebuild arena.code root address
    ⟨⟨output.value,true⟩,body.cells+allowed.cells+output.cells+8*Dependency.size output.value+20⟩
  else
    let output : Cone.Frame := ⟨arena.code,(List.range arena.code.size).toArray⟩
    ⟨⟨output,false⟩,body.cells+allowed.cells+8*Dependency.size output+4*arena.code.size+20⟩

theorem applyFrame_code (arena : ArenaAction.Arena) (address : Nat) (root : Fin arena.code.size) :
    (applyFrame arena address root).value.frame.code=(ArenaAction.apply arena address root).arena.code := by
  simp only [applyFrame,free_value,body_code]
  by_cases free : address ∉ FunctionalSubstitution.inputs (ArenaAction.actualBody arena root).code
  · simp [free,Rewiring.rebuild_value,ArenaAction.apply]
  · simp [free,ArenaAction.apply]

theorem applyFrame_mapping (arena : ArenaAction.Arena) (address : Nat) (root : Fin arena.code.size) :
    (applyFrame arena address root).value.frame.mapping=(ArenaAction.apply arena address root).mapping := by
  simp only [applyFrame,free_value,body_code]
  by_cases free : address ∉ FunctionalSubstitution.inputs (ArenaAction.actualBody arena root).code
  · simp [free,Rewiring.rebuild_value,ArenaAction.apply]
  · simp [free,ArenaAction.apply]

theorem applyFrame_performed (arena : ArenaAction.Arena) (address : Nat) (root : Fin arena.code.size) :
    (applyFrame arena address root).value.performed=(ArenaAction.apply arena address root).performed := by
  simp only [applyFrame,free_value,body_code]
  by_cases free : address ∉ FunctionalSubstitution.inputs (ArenaAction.actualBody arena root).code
  · simp [free,ArenaAction.apply]
  · simp [free,ArenaAction.apply]

def applyBudget (nodes : Nat) : Nat := Dependency.budget nodes+inputsBudget nodes+Rewiring.budget nodes+28*nodes+50

theorem applyFrame_cells (arena : ArenaAction.Arena) (address : Nat) (root : Fin arena.code.size) :
    (applyFrame arena address root).cells ≤ applyBudget arena.code.size := by
  have body := Dependency.compact_cells (ArenaAction.focus arena.code root)
  have bodySize := ArenaAction.actualBody_size arena root
  have checked := free_cells address (Dependency.compact (ArenaAction.focus arena.code root)).value.code
  rw [body_code] at checked
  have bounded := inputsBudget_mono _ _ bodySize
  have rebuilt := Rewiring.rebuild_cells arena.code root address
  have codeSize := ArenaAction.rebuild_size arena.code root address
  have mapSize : (ArenaAction.rebuild arena.code root address).mapping.size=arena.code.size := by
    have keep : ∀ (offset : Nat) (frame : Cone.Frame) (nodes : List Node) (needed : List Nat) (body : Nat),
        (ArenaAction.finish needed address body offset frame nodes).mapping.size=frame.mapping.size := by
      intro offset frame nodes
      induction nodes generalizing offset frame with
      | nil => intros; rfl
      | cons node rest ih =>
          intro needed body
          rw [ArenaAction.finish,ih]
          simp only [ArenaAction.step]
          split <;> simp only [ArenaAction.mapPut_size]
    rw [ArenaAction.rebuild,keep]
    exact (Cone.compact_represents (ArenaAction.focus arena.code root) arena.forward (fun _ => false)).2.1.trans
      (run_size _ _)
  dsimp only [applyFrame]
  split
  · dsimp only
    rw [Rewiring.rebuild_value,body_code]
    change _ ≤ Dependency.budget arena.code.size at body
    unfold applyBudget Dependency.size
    rw [codeSize,mapSize]
    omega
  · change _ ≤ Dependency.budget arena.code.size at body
    dsimp only
    simp only [Dependency.size,List.size_toArray,List.length_range,body_code]
    unfold applyBudget
    omega

def remap (mapping : Array Nat) : List ArenaSource.RawRelation → Counted (List ArenaSource.RawRelation)
  | [] => ⟨[],1⟩
  | item::rest =>
      let left := lookup mapping item.left
      let right := lookup mapping item.right
      let tail := remap mapping rest
      ⟨⟨item.address,left.value,right.value⟩::tail.value,left.cells+right.cells+tail.cells+6*tail.value.length+16⟩

theorem remap_value (mapping : Array Nat) (items : List ArenaSource.RawRelation) :
    (remap mapping items).value=items.map (fun item => ⟨item.address,mapping.getD item.left 0,mapping.getD item.right 0⟩) := by
  induction items <;> simp_all [remap,lookup]

theorem remap_cells (mapping : Array Nat) (items : List ArenaSource.RawRelation) :
    (remap mapping items).cells ≤ items.length*(4*mapping.size+6*items.length+24)+1 := by
  induction items with
  | nil => simp [remap]
  | cons item rest ih =>
      simp only [remap,lookup,remap_value,List.length_map,List.length_cons]
      nlinarith

def rawRelations (state : ArenaSource.State) : List ArenaSource.RawRelation :=
  state.relations.map (fun item => ⟨item.address,item.relation.left.val,item.relation.right.val⟩)

theorem applyFrame_mapping_size (arena : ArenaAction.Arena) (address : Nat) (root : Fin arena.code.size) :
    (applyFrame arena address root).value.frame.mapping.size=arena.code.size := by
  have keep : ∀ (offset : Nat) (frame : Cone.Frame) (nodes : List Node) (needed : List Nat) (body : Nat),
      (ArenaAction.finish needed address body offset frame nodes).mapping.size=frame.mapping.size := by
    intro offset frame nodes
    induction nodes generalizing offset frame with
    | nil => intros; rfl
    | cons node rest ih =>
        intro needed body
        rw [ArenaAction.finish,ih]
        simp only [ArenaAction.step]
        split <;> simp only [ArenaAction.mapPut_size]
  rw [applyFrame_mapping]
  dsimp only [ArenaAction.apply]
  split
  · dsimp only
    rw [ArenaAction.rebuild,keep]
    exact (Cone.compact_represents (ArenaAction.focus arena.code root) arena.forward (fun _ => false)).2.1.trans
      (run_size _ _)
  · simp

/-- The sealed source constructor executes its own update. The ledger pays both
the paired construction and that same source execution, including all root reads. -/
def next (state : ArenaSource.State) (address : Nat) (root : Fin state.arena.code.size) : Counted ArenaSource.State :=
  let update := applyFrame state.arena address root
  let relations := remap update.value.frame.mapping (rawRelations state)
  let weight := lookup update.value.frame.mapping state.program.weight.val
  let phase := lookup update.value.frame.mapping state.program.phase.val
  let output := ArenaSource.next state address root
  ⟨output,2*(update.cells+relations.cells+weight.cells+phase.cells)+
    16*(state.arena.code.size+state.relations.length+1)+24⟩

theorem next_value (state : ArenaSource.State) (address : Nat) (root : Fin state.arena.code.size) :
    (next state address root).value=ArenaSource.next state address root := rfl

def nextBudget (nodes count : Nat) : Nat :=
  2*(applyBudget nodes+count*(4*nodes+6*count+24)+4*nodes+9)+16*(nodes+count+1)+24

theorem next_cells (state : ArenaSource.State) (address : Nat) (root : Fin state.arena.code.size) :
    (next state address root).cells ≤ nextBudget state.arena.code.size state.relations.length := by
  have update := applyFrame_cells state.arena address root
  have relations := remap_cells (applyFrame state.arena address root).value.frame.mapping (rawRelations state)
  rw [applyFrame_mapping_size] at relations
  have count : (rawRelations state).length=state.relations.length := by simp only [rawRelations,List.length_map]
  rw [count] at relations
  simp only [next,lookup,applyFrame_mapping_size,nextBudget]
  omega

def historySize (instructions : List Instruction) : Nat := FunctionalSchedule.Cost.inputSize instructions

def drive : Nat → ArenaSource.State → Counted ArenaSource.Run
  | 0,state => ⟨⟨state,[]⟩,8*(state.arena.code.size+state.relations.length+1)+8⟩
  | fuel+1,state =>
      let chosen := choose state
      match chosen.value with
      | none => ⟨⟨state,[]⟩,chosen.cells+8*(state.arena.code.size+state.relations.length+1)+8⟩
      | some item =>
          let updated := next state item.address item.relation.right
          let tail := drive fuel updated.value
          let body := Dependency.compact (ArenaAction.focus state.arena.code item.relation.right)
          let instruction := ArenaSource.selected state item
          ⟨⟨tail.value.state,instruction::tail.value.instructions⟩,
            chosen.cells+updated.cells+tail.cells+2*body.cells+
              16*(state.arena.code.size+state.relations.length+historySize tail.value.instructions+1)+32⟩

theorem drive_value (fuel : Nat) (state : ArenaSource.State) : (drive fuel state).value=ArenaSource.drive fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [drive,choose_value,ArenaSource.drive]
      split <;> simp_all only [next_value]

theorem drive_history (fuel : Nat) (state : ArenaSource.State) :
    historySize (drive fuel state).value.instructions ≤ fuel*(state.arena.code.size+8)+1 := by
  rw [drive_value]
  have lengths := ArenaSource.drive_length fuel state
  have nodes := ArenaSource.drive_inventory fuel state
  have sum : ∀ calls : List Instruction,
      (calls.map FunctionalSchedule.Cost.instructionSize).sum=
        (calls.map (fun call => call.body.code.size)).sum+8*calls.length := by
    intro calls
    induction calls with
    | nil => rfl
    | cons call rest ih => simp only [List.map_cons,List.sum_cons,ih,FunctionalSchedule.Cost.instructionSize,List.length_cons]; omega
  simp only [historySize,FunctionalSchedule.Cost.inputSize,sum]
  nlinarith

def roundBudget (nodes count fuel : Nat) : Nat :=
  count*(eligibleBudget nodes+10)+1+nextBudget nodes count+2*Dependency.budget nodes+
    16*(nodes+count+fuel*(nodes+8)+2)+40

def driveBudget (nodes count fuel : Nat) : Nat := (fuel+1)*roundBudget nodes count fuel

theorem drive_cells_aux (fuel rounds : Nat) (state : ArenaSource.State) (bounded : fuel ≤ rounds) :
    (drive fuel state).cells ≤ (fuel+1)*roundBudget state.arena.code.size state.relations.length rounds := by
  induction fuel generalizing state with
  | zero =>
      simp only [drive]
      unfold roundBudget
      omega
  | succ fuel ih =>
      have choice := chooseFrom_cells state state.relations
      change (choose state).cells ≤ _ at choice
      simp only [drive]
      split
      · dsimp only
        have bound : (choose state).cells+8*(state.arena.code.size+state.relations.length+1)+8 ≤
            roundBudget state.arena.code.size state.relations.length rounds := by unfold roundBudget; omega
        exact bound.trans (Nat.le_mul_of_pos_left _ (by omega))
      · rename_i item found
        have update := next_cells state item.address item.relation.right
        have codeSize : (next state item.address item.relation.right).value.arena.code.size=state.arena.code.size :=
          ArenaSource.next_size state item.address item.relation.right
        have count : (next state item.address item.relation.right).value.relations.length=state.relations.length :=
          ArenaSource.next_count state item.address item.relation.right
        have later := ih (next state item.address item.relation.right).value (by omega)
        rw [codeSize,count] at later
        have history := drive_history fuel (next state item.address item.relation.right).value
        rw [codeSize] at history
        have body := Dependency.compact_cells (ArenaAction.focus state.arena.code item.relation.right)
        change _ ≤ Dependency.budget state.arena.code.size at body
        have historyBound : historySize (drive fuel (next state item.address item.relation.right).value).value.instructions ≤
            rounds*(state.arena.code.size+8)+1 := history.trans (by nlinarith)
        dsimp only
        unfold roundBudget at later ⊢
        nlinarith only [choice,update,later,body,historyBound]

theorem drive_cells (fuel : Nat) (state : ArenaSource.State) :
    (drive fuel state).cells ≤ driveBudget state.arena.code.size state.relations.length fuel :=
  drive_cells_aux fuel fuel state le_rfl

def extend (code : Array Node) (instruction : Instruction) : Counted (Array Node) :=
  let shifted := shifts code.size instruction.body.code.toList
  let output := (code++shifted.value.toArray).push (.input instruction.address)
  ⟨output,shifted.cells+8*(code.size+instruction.body.code.size+output.size)+16⟩

theorem extend_value (code : Array Node) (instruction : Instruction) :
    (extend code instruction).value=ArenaSource.extend code instruction := by
  apply Array.toList_inj.mp
  simp [extend,shifts_value,ArenaSource.extend]

theorem extend_cells (code : Array Node) (instruction : Instruction) :
    (extend code instruction).cells ≤
      8*instruction.body.code.size*instruction.body.code.size+32*instruction.body.code.size+16*code.size+25 := by
  have work := shifts_cells code.size instruction.body.code.toList
  simp only [Array.length_toList] at work
  simp only [extend,shifts_value,Array.size_push,Array.size_append,List.size_toArray,List.length_map,Array.length_toList]
  nlinarith

def inventory (code : Array Node) (source : List Instruction) : Nat :=
  code.size+(source.map (fun call => call.body.code.size+1)).sum+source.length+1

theorem inventory_cons (code : Array Node) (instruction : Instruction) (rest : List Instruction) :
    inventory (ArenaSource.extend code instruction) rest+1=inventory code (instruction::rest) := by
  simp only [inventory,ArenaSource.extend_size,List.map_cons,List.sum_cons,List.length_cons]
  omega

theorem inventory_code (code : Array Node) (source : List Instruction) : code.size ≤ inventory code source := by
  unfold inventory
  omega

theorem inventory_length (code : Array Node) (source : List Instruction) : source.length ≤ inventory code source := by
  unfold inventory
  omega

def gather : Array Node → List Instruction → Counted ArenaSource.Raw
  | code,[] => ⟨⟨code,[]⟩,8*(code.size+1)+1⟩
  | code,instruction::rest =>
      let first := extend code instruction
      let tail := gather first.value rest
      let output : ArenaSource.Raw := ⟨tail.value.code,ArenaSource.entry code instruction::tail.value.relations⟩
      ⟨output,first.cells+tail.cells+8*(output.code.size+output.relations.length+1)+16⟩

theorem gather_value (code : Array Node) (source : List Instruction) : (gather code source).value=ArenaSource.gather code source := by
  induction source generalizing code <;> simp_all [gather,ArenaSource.gather,extend_value]

theorem gather_storage (code : Array Node) (source : List Instruction) :
    (gather code source).value.code.size+(gather code source).value.relations.length+1=inventory code source := by
  rw [gather_value,ArenaSource.gather_size,ArenaSource.gather_length]
  rfl

def gatherBudget (count size : Nat) : Nat := (count+1)*(100*size*size+100)

theorem gather_cells (code : Array Node) (source : List Instruction) :
    (gather code source).cells ≤ gatherBudget source.length (inventory code source) := by
  induction source generalizing code with
  | nil => simp only [gather,gatherBudget,inventory,List.length_nil,List.map_nil,List.sum_nil,Nat.add_zero]; nlinarith
  | cons instruction rest ih =>
      have first := extend_cells code instruction
      have later := ih (extend code instruction).value
      rw [extend_value] at later
      have growth := inventory_cons code instruction rest
      have output := gather_storage (extend code instruction).value rest
      rw [extend_value] at output
      have codeBound : code.size ≤ inventory code (instruction::rest) := inventory_code _ _
      have bodyBound : instruction.body.code.size ≤ inventory code (instruction::rest) := by
        simp only [inventory,List.map_cons,List.sum_cons,List.length_cons]
        omega
      have square := Nat.mul_self_le_mul_self bodyBound
      have tailBound := later.trans (Nat.mul_le_mul_left (rest.length+1)
        (show 100*inventory (ArenaSource.extend code instruction) rest*inventory (ArenaSource.extend code instruction) rest+100 ≤
          100*inventory code (instruction::rest)*inventory code (instruction::rest)+100 by
          have square := Nat.mul_self_le_mul_self (show inventory (ArenaSource.extend code instruction) rest ≤ inventory code (instruction::rest) by omega)
          nlinarith))
      rw [← extend_value] at tailBound output growth
      simp only [gather,gatherBudget,List.length_cons]
      have positive : 1 ≤ inventory code (instruction::rest) := by unfold inventory; omega
      nlinarith only [first,growth,output,codeBound,bodyBound,square,tailBound,positive]

/-- The sealed `build` repeats this actual measured constructor. Both executions
and both copies of every root are included; the strong source frontend is shared. -/
def build (program : Program) (source : List Instruction) : Counted ArenaSource.State :=
  let raw := gather program.code source
  let loaded := Reduction.compact raw.value.code
  let relations := remap loaded.value.mapping raw.value.relations
  let weight := lookup loaded.value.mapping program.weight.val
  let phase := lookup loaded.value.mapping program.phase.val
  ⟨ArenaSource.build program source,2*(raw.cells+loaded.cells+relations.cells+weight.cells+phase.cells)+
    16*(raw.value.code.size+source.length+1)+24⟩

theorem build_value (program : Program) (source : List Instruction) : (build program source).value=ArenaSource.build program source := rfl

theorem reduction_mapping_size (code : Array Node) : (Reduction.compact code).value.mapping.size=code.size := by
  rw [Reduction.compact_value]
  exact (Reduce.compact_represents code (fun _ => false)).2.2.1.trans (run_size _ _)

theorem reductionBudget_mono (a b : Nat) (bounded : a ≤ b) : Reduction.budget a ≤ Reduction.budget b :=
  Nat.mul_le_mul (by omega) (by omega)

def buildBudget (count size : Nat) : Nat :=
  2*(gatherBudget count size+Reduction.budget size+count*(4*size+6*count+24)+4*size+9)+16*(size+count+1)+24

theorem build_cells (program : Program) (source : List Instruction) :
    (build program source).cells ≤ buildBudget source.length (inventory program.code source) := by
  let raw := gather program.code source
  have generated := gather_cells program.code source
  have storage := gather_storage program.code source
  have codeSize : raw.value.code.size ≤ inventory program.code source := by change raw.value.code.size+raw.value.relations.length+1=_ at storage; omega
  have count : raw.value.relations.length=source.length := by
    rw [gather_value,ArenaSource.gather_length]
  have loaded := (Reduction.compact_cells raw.value.code).trans (reductionBudget_mono _ _ codeSize)
  have mapped := remap_cells (Reduction.compact raw.value.code).value.mapping raw.value.relations
  rw [reduction_mapping_size,count] at mapped
  have remapBound := mapped.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left source.length (show 4*raw.value.code.size+6*source.length+24 ≤
      4*inventory program.code source+6*source.length+24 by omega)) 1)
  change raw.cells ≤ _ at generated
  change 2*(raw.cells+(Reduction.compact raw.value.code).cells+
    (remap (Reduction.compact raw.value.code).value.mapping raw.value.relations).cells+
    (lookup (Reduction.compact raw.value.code).value.mapping program.weight.val).cells+
    (lookup (Reduction.compact raw.value.code).value.mapping program.phase.val).cells)+16*(raw.value.code.size+source.length+1)+24 ≤ _
  simp only [lookup,reduction_mapping_size,buildBudget]
  omega

theorem build_nodes (program : Program) (source : List Instruction) :
    (build program source).value.arena.code.size ≤ inventory program.code source := by
  have size := ArenaSource.build_size program source
  unfold inventory
  exact size.trans (by omega)

theorem buildBudget_mono (c d a b : Nat) (count : c ≤ d) (size : a ≤ b) : buildBudget c a ≤ buildBudget d b := by
  unfold buildBudget gatherBudget Reduction.budget
  gcongr

theorem driveBudget_mono (a b c d fuel : Nat) (nodes : a ≤ b) (count : c ≤ d) :
    driveBudget a c fuel ≤ driveBudget b d fuel := by
  unfold driveBudget roundBudget nextBudget applyBudget eligibleBudget Dependency.budget Rewiring.budget inputsBudget
  gcongr

def compile {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) (fuel : Nat) : Counted ArenaSource.Run :=
  let source := ArenaSource.front formula basis
  let initial := build source.initial source.candidates
  let result := drive fuel initial.value
  ⟨result.value,source.cells+initial.cells+result.cells+
    16*(AffineCollect.tableSize source.table+FunctionalSchedule.Cost.inputSize source.candidates+
      source.initial.code.size+result.value.state.arena.code.size+result.value.state.relations.length+
      historySize result.value.instructions+1)+24⟩

theorem compile_value {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) (fuel : Nat) :
    (compile formula basis fuel).value=ArenaSource.compile formula basis fuel := by
  simp only [compile,drive_value,build_value,ArenaSource.compile]

theorem source_inventory {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) :
    inventory (ArenaSource.front formula basis).initial.code (ArenaSource.front formula basis).candidates ≤
      ArenaSource.sourceBound n formula.length (Affine.Extract.literalCount formula) := by
  have size := ForcedBranches.Cost.initial_size formula basis
  have candidates := ForcedBranches.Cost.generate_storage formula basis valid
  have source : ∀ calls : List Instruction,
      (calls.map (fun call => call.body.code.size+1)).sum+calls.length+1 ≤ FunctionalSchedule.Cost.inputSize calls := by
    intro calls
    induction calls with
    | nil => simp [FunctionalSchedule.Cost.inputSize]
    | cons call rest ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,FunctionalSchedule.Cost.inputSize_cons,
          FunctionalSchedule.Cost.instructionSize]
        omega
  have records := source (ArenaSource.front formula basis).candidates
  change (ArenaSource.front formula basis).initial.code.size ≤ _ at size
  change FunctionalSchedule.Cost.inputSize (ArenaSource.front formula basis).candidates ≤ _ at candidates
  unfold inventory ArenaSource.sourceBound
  omega

def compileBudget (n clauses literals basisSize fuel : Nat) : Nat :=
  let nodes := ArenaSource.sourceBound n clauses literals
  let count := 3*clauses+n*n
  ArenaSource.frontBudget n clauses literals basisSize+buildBudget count nodes+driveBudget nodes count fuel+
    16*(AffineCarrier.Cost.cellBound n+ForcedBranches.Cost.outputStorage n clauses+
      2*nodes+count+fuel*(nodes+8)+2)+24

theorem compile_cells {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (fuel : Nat) :
    (compile formula basis fuel).cells ≤
      compileBudget n formula.length (Affine.Extract.literalCount formula) (AffineCarrier.cellSize basis) fuel := by
  let source := ArenaSource.front formula basis
  let initial := build source.initial source.candidates
  let result := drive fuel initial.value
  let size := ArenaSource.sourceBound n formula.length (Affine.Extract.literalCount formula)
  let count := 3*formula.length+n*n
  have frontWork := ArenaSource.front_cells formula basis valid
  have inventorySize := source_inventory formula basis valid
  have candidates := ForcedBranches.Cost.generate_length formula basis
  change source.candidates.length ≤ count at candidates
  have initialWork := (build_cells source.initial source.candidates).trans
    (buildBudget_mono _ count _ size candidates inventorySize)
  have nodes := (build_nodes source.initial source.candidates).trans inventorySize
  change initial.value.arena.code.size ≤ size at nodes
  have relationCount : initial.value.relations.length=source.candidates.length := ArenaSource.build_count _ _
  have runWork := (drive_cells fuel initial.value).trans (driveBudget_mono _ size _ count fuel nodes (relationCount ▸ candidates))
  have outputNodes : result.value.state.arena.code.size=initial.value.arena.code.size := by
    dsimp only [result]
    rw [drive_value,ArenaSource.drive_size]
  have outputCount : result.value.state.relations.length=source.candidates.length := by
    dsimp only [result]
    rw [drive_value,ArenaSource.drive_count,relationCount]
  have history := (drive_history fuel initial.value).trans (Nat.add_le_add_right (Nat.mul_le_mul_left fuel (Nat.add_le_add_right nodes 8)) 1)
  have table := AffineCollect.Cost.coordinate_size n basis
  have storage := ForcedBranches.Cost.generate_storage formula basis valid
  have original : source.initial.code.size ≤ size := (inventory_code source.initial.code source.candidates).trans inventorySize
  change AffineCollect.tableSize source.table ≤ _ at table
  change FunctionalSchedule.Cost.inputSize source.candidates ≤ _ at storage
  change source.cells ≤ _ at frontWork
  change initial.cells ≤ _ at initialWork
  change result.cells ≤ _ at runWork
  change historySize result.value.instructions ≤ fuel*(size+8)+1 at history
  change source.cells+initial.cells+result.cells+
    16*(AffineCollect.tableSize source.table+FunctionalSchedule.Cost.inputSize source.candidates+
      source.initial.code.size+result.value.state.arena.code.size+result.value.state.relations.length+
      historySize result.value.instructions+1)+24 ≤ _
  rw [outputNodes,outputCount]
  change _ ≤ ArenaSource.frontBudget n formula.length (Affine.Extract.literalCount formula) (AffineCarrier.cellSize basis)+
    buildBudget count size+driveBudget size count fuel+
    16*(AffineCarrier.Cost.cellBound n+ForcedBranches.Cost.outputStorage n formula.length+2*size+count+fuel*(size+8)+2)+24
  omega

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (fuel : Nat) (environment : Nat → Bool) :
    (FunctionalAffine.legal (compile formula basis fuel).value.instructions environment &&
      truth ((compile formula basis fuel).value.state.program.program.eval environment))=
      CNFFormula.eval formula (Affine.Gates.coordinate (Affine.Table.coordinates n basis) environment) := by
  rw [compile_value]
  exact ArenaSource.compile_read formula basis valid fuel environment

theorem compile_correct {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (fuel : Nat) :
    FunctionalSubstitution.decideProgram (compile formula basis fuel).value.state.program.program=true ↔
      ∃ environment, CNFFormula.eval formula (Affine.Gates.coordinate (Affine.Table.coordinates n basis) environment)=true := by
  rw [compile_value]
  exact ArenaSource.compile_correct formula basis valid fuel

end SaturationMonoid.ComplexityProjection.SATSource.ArenaCost

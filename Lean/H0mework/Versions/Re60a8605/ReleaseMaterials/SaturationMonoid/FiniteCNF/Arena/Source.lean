import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Arena.Action
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.ForcedBranches.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ArenaSource
open InterferenceProgram
open FunctionalSubstitution (Instruction)
open ArenaAction (Arena View Relation)

structure RawRelation where
  address : Nat
  left : Nat
  right : Nat
  deriving Repr

def extend (code : Array Node) (instruction : Instruction) : Array Node :=
  (code++instruction.body.code.map (Node.shift code.size)).push (.input instruction.address)

def entry (code : Array Node) (instruction : Instruction) : RawRelation :=
  ⟨instruction.address,code.size+instruction.body.code.size,code.size+instruction.body.output.val⟩

theorem extend_size (code : Array Node) (instruction : Instruction) :
    (extend code instruction).size=code.size+instruction.body.code.size+1 := by simp [extend,Nat.add_assoc]

theorem entry_bounds (code : Array Node) (instruction : Instruction) :
    (entry code instruction).left < (extend code instruction).size ∧
      (entry code instruction).right < (extend code instruction).size := by
  have size := instruction.body.output.isLt
  simp only [entry,extend_size]
  omega

theorem extend_old (code : Array Node) (instruction : Instruction) (environment : Nat → Bool) (i : Nat) (bound : i < code.size) :
    (run environment (extend code instruction)).getD i 0=(run environment code).getD i 0 := by
  unfold extend
  rw [run_push,getD_push_old _ _ _ (by simp only [run_size,Array.size_append,Array.size_map]; omega),run_join]
  exact getD_append_left _ _ _ (by simpa only [run_size] using bound)

theorem extend_left (code : Array Node) (instruction : Instruction) (environment : Nat → Bool) :
    (run environment (extend code instruction)).getD (entry code instruction).left 0=bit (environment instruction.address) := by
  simp only [extend,entry,run_push]
  have size : (run environment (code++instruction.body.code.map (Node.shift code.size))).size=code.size+instruction.body.code.size := by
    simp [run_size]
  rw [← size,getD_push_last]
  rfl

theorem extend_right (code : Array Node) (instruction : Instruction) (environment : Nat → Bool) :
    (run environment (extend code instruction)).getD (entry code instruction).right 0=instruction.body.eval environment := by
  simp only [extend,entry,run_push]
  rw [getD_push_old _ _ _ (by simp only [run_size,Array.size_append,Array.size_map]; exact Nat.add_lt_add_left instruction.body.output.isLt _),run_join]
  rw [← run_size environment code,getD_append_right]
  rfl

structure Raw where
  code : Array Node
  relations : List RawRelation
  deriving Repr

def gather : Array Node → List Instruction → Raw
  | code,[] => ⟨code,[]⟩
  | code,instruction::rest =>
      let next := extend code instruction
      let generated := gather next rest
      ⟨generated.code,entry code instruction::generated.relations⟩

theorem gather_size (code : Array Node) (source : List Instruction) :
    (gather code source).code.size=code.size+(source.map (fun instruction => instruction.body.code.size+1)).sum := by
  induction source generalizing code with
  | nil => simp [gather]
  | cons instruction rest ih => simp only [gather,ih,extend_size,List.map_cons,List.sum_cons]; omega

theorem gather_growth (code : Array Node) (source : List Instruction) : code.size ≤ (gather code source).code.size := by
  rw [gather_size]
  omega

theorem gather_old (code : Array Node) (source : List Instruction) (environment : Nat → Bool)
    (i : Nat) (bound : i < code.size) :
    (run environment (gather code source).code).getD i 0=(run environment code).getD i 0 := by
  induction source generalizing code with
  | nil => rfl
  | cons instruction rest ih =>
      rw [gather,ih _ (by rw [extend_size]; omega),extend_old code instruction environment i bound]

theorem gather_length (code : Array Node) (source : List Instruction) : (gather code source).relations.length=source.length := by
  induction source generalizing code <;> simp_all [gather]

theorem gather_bounds (code : Array Node) (source : List Instruction) :
    ∀ relation ∈ (gather code source).relations, relation.left < (gather code source).code.size ∧
      relation.right < (gather code source).code.size := by
  induction source generalizing code with
  | nil => simp [gather]
  | cons instruction rest ih =>
      intro relation member
      simp only [gather,List.mem_cons] at member
      rcases member with rfl | member
      · have bounds := entry_bounds code instruction
        have more := gather_growth (extend code instruction) rest
        exact ⟨bounds.1.trans_le more,bounds.2.trans_le more⟩
      · exact ih _ relation member

def Describes (code : Array Node) (instruction : Instruction) (relation : RawRelation) : Prop :=
  relation.address=instruction.address ∧ ∀ environment,
    (run environment code).getD relation.left 0=bit (environment instruction.address) ∧
      (run environment code).getD relation.right 0=instruction.body.eval environment

theorem gather_describes (code : Array Node) (source : List Instruction) :
    List.Forall₂ (Describes (gather code source).code) source (gather code source).relations := by
  induction source generalizing code with
  | nil => exact List.Forall₂.nil
  | cons instruction rest ih =>
      refine List.Forall₂.cons ?_ (ih (extend code instruction))
      refine ⟨rfl,?_⟩
      intro environment
      have bounds := entry_bounds code instruction
      change (run environment (gather (extend code instruction) rest).code).getD (entry code instruction).left 0=_ ∧
        (run environment (gather (extend code instruction) rest).code).getD (entry code instruction).right 0=_
      rw [gather_old _ _ environment _ bounds.1,gather_old _ _ environment _ bounds.2,extend_left,extend_right]
      exact ⟨rfl,rfl⟩

structure Labeled (arena : Arena) where
  address : Nat
  relation : Relation arena

structure State where
  private mk ::
  arena : Arena
  program : View arena
  relations : List (Labeled arena)

def loadRelation (loaded : ArenaAction.Loaded) (relation : RawRelation) : Labeled loaded.arena :=
  ⟨relation.address,⟨loaded.ref relation.left,loaded.ref relation.right⟩⟩

def build (program : Program) (source : List Instruction) : State :=
  let raw := gather program.code source
  let loaded := ArenaAction.load raw.code
  ⟨loaded.arena,⟨loaded.ref program.weight.val,loaded.ref program.phase.val⟩,raw.relations.map (loadRelation loaded)⟩

theorem build_program (program : Program) (source : List Instruction) (environment : Nat → Bool) :
    (build program source).program.program.eval environment=program.eval environment := by
  have a := ArenaAction.load_read (gather program.code source).code program.weight.val environment
  have b := ArenaAction.load_read (gather program.code source).code program.phase.val environment
  rw [gather_old program.code source environment _ program.weight.isLt] at a
  rw [gather_old program.code source environment _ program.phase.isLt] at b
  exact congrArg₂ (fun weight phase => weight*sign phase) a b

theorem build_count (program : Program) (source : List Instruction) : (build program source).relations.length=source.length := by
  simp only [build,List.length_map,gather_length]

theorem build_size (program : Program) (source : List Instruction) :
    (build program source).arena.code.size ≤
      program.code.size+(source.map (fun call => call.body.code.size+1)).sum+1 := by
  have size := Reduce.compact_code_size (gather program.code source).code
  rw [gather_size] at size
  exact size

theorem build_relations (program : Program) (source : List Instruction) (environment : Nat → Bool) :
    (build program source).relations.all (fun item => item.relation.read environment)=
      FunctionalAffine.legal source environment := by
  have described := gather_describes program.code source
  have generated : ∀ (original : List Instruction) (relations : List RawRelation),
      List.Forall₂ (Describes (gather program.code source).code) original relations →
      (relations.map (loadRelation (ArenaAction.load (gather program.code source).code))).all
        (fun item => item.relation.read environment)=FunctionalAffine.legal original environment := by
    intro original relations matching
    induction matching with
    | nil => rfl
    | @cons call relation calls relations first rest ih =>
        simp only [List.map_cons,List.all_cons,FunctionalAffine.legal] at ih ⊢
        rw [ih]
        congr 1
        simp only [loadRelation,ArenaAction.Relation.read,ArenaAction.load_read,
          (first.2 environment).1,(first.2 environment).2,truth_bit]
  exact generated source _ described

def Valid (state : State) : Prop := ∀ environment,
  truth (state.program.program.eval environment)=true →
    state.relations.all (fun item => item.relation.read environment)=true

theorem build_valid (program : Program) (source : List Instruction)
    (entails : ∀ environment, truth (program.eval environment)=true →
      ∀ instruction ∈ source, instruction.bind environment=environment) : Valid (build program source) := by
  intro environment accepted
  rw [build_program] at accepted
  rw [build_relations]
  exact FunctionalAffine.legal_of_fixed source environment (entails environment accepted)

def next (state : State) (address : Nat) (root : Fin state.arena.code.size) : State :=
  let action := ArenaAction.apply state.arena address root
  ⟨action.arena,action.view state.program,state.relations.map (fun item => ⟨item.address,action.relation item.relation⟩)⟩

theorem next_size (state : State) (address : Nat) (root : Fin state.arena.code.size) :
    (next state address root).arena.code.size=state.arena.code.size :=
  ArenaAction.apply_size state.arena address root

theorem next_count (state : State) (address : Nat) (root : Fin state.arena.code.size) :
    (next state address root).relations.length=state.relations.length := by simp only [next,List.length_map]

theorem next_program (state : State) (address : Nat) (root : Fin state.arena.code.size) (environment : Nat → Bool) :
    (next state address root).program.program.eval environment=
      state.program.program.eval (ArenaAction.Action.environment state.arena address root environment) :=
  ArenaAction.apply_view state.arena address root state.program environment

def readRelations (state : State) (environment : Nat → Bool) : Bool := state.relations.all (fun item => item.relation.read environment)

theorem next_relations (state : State) (address : Nat) (root : Fin state.arena.code.size) (environment : Nat → Bool) :
    readRelations (next state address root) environment=
      readRelations state (ArenaAction.Action.environment state.arena address root environment) := by
  simp only [readRelations,next,List.all_map,Function.comp_def,ArenaAction.apply_relation]

theorem next_valid (state : State) (valid : Valid state) (address : Nat) (root : Fin state.arena.code.size) :
    Valid (next state address root) := by
  intro environment accepted
  rw [next_program] at accepted
  exact (next_relations state address root environment).trans (valid _ accepted)

/-- A source-generated body is shared by every old input occurrence. All old
relation roots follow the same prefix and the same reduction map. -/
def substitute (state : State) (instruction : Instruction) : State :=
  let program := FunctionalSubstitution.substitute state.program.program instruction.address instruction.body
  let loaded := ArenaAction.load program.code
  let ref := fun (i : Fin state.arena.code.size) => loaded.ref (instruction.body.code.size+i.val)
  ⟨loaded.arena,⟨ref state.program.weight,ref state.program.phase⟩,
    state.relations.map (fun item => ⟨item.address,⟨ref item.relation.left,ref item.relation.right⟩⟩)⟩

theorem substitute_slot (state : State) (instruction : Instruction) (i : Fin state.arena.code.size) (environment : Nat → Bool) :
    let code := (FunctionalSubstitution.substitute state.program.program instruction.address instruction.body).code
    (run environment (ArenaAction.load code).arena.code).getD
      ((ArenaAction.load code).ref (instruction.body.code.size+i.val)).val 0=
        (run (instruction.bind environment) state.arena.code).getD i.val 0 := by
  dsimp only
  rw [ArenaAction.load_read,FunctionalSubstitution.run_substitute,← run_size environment instruction.body.code,getD_append_right]
  rfl

theorem substitute_program (state : State) (instruction : Instruction) (environment : Nat → Bool) :
    (substitute state instruction).program.program.eval environment=state.program.program.eval (instruction.bind environment) := by
  exact congrArg₂ (fun weight phase => weight*sign phase)
    (substitute_slot state instruction state.program.weight environment)
    (substitute_slot state instruction state.program.phase environment)

theorem substitute_relations (state : State) (instruction : Instruction) (environment : Nat → Bool) :
    readRelations (substitute state instruction) environment=readRelations state (instruction.bind environment) := by
  simp only [readRelations,substitute,List.all_map,Function.comp_def,ArenaAction.Relation.read,substitute_slot]

theorem substitute_valid (state : State) (valid : Valid state) (instruction : Instruction) : Valid (substitute state instruction) := by
  intro environment accepted
  rw [substitute_program] at accepted
  exact (substitute_relations state instruction environment).trans (valid _ accepted)

theorem substitute_count (state : State) (instruction : Instruction) :
    (substitute state instruction).relations.length=state.relations.length := by simp only [substitute,List.length_map]

theorem substitute_size (state : State) (instruction : Instruction) :
    (substitute state instruction).arena.code.size ≤ state.arena.code.size+instruction.body.code.size+1 := by
  have size := Reduce.compact_code_size (FunctionalSubstitution.substitute state.program.program instruction.address instruction.body).code
  rw [FunctionalSubstitution.substitute_size] at size
  change (substitute state instruction).arena.code.size ≤ instruction.body.code.size+state.arena.code.size+1 at size
  omega

/-- Reload one generated code image while keeping every original relation root
on the same offset and the same actual reduction map. -/
def reload (state : State) (code : Array Node) (offset : Nat) : State :=
  let loaded := ArenaAction.load code
  let ref := fun (i : Fin state.arena.code.size) => loaded.ref (offset+i.val)
  ⟨loaded.arena,⟨ref state.program.weight,ref state.program.phase⟩,
    state.relations.map (fun item => ⟨item.address,⟨ref item.relation.left,ref item.relation.right⟩⟩)⟩

theorem reload_program (state : State) (code : Array Node) (offset : Nat) (environment : Nat → Bool) :
    (reload state code offset).program.program.eval environment=
      (run environment code).getD (offset+state.program.weight.val) 0*
        sign ((run environment code).getD (offset+state.program.phase.val) 0) :=
  congrArg₂ (fun weight phase => weight*sign phase)
    (ArenaAction.load_read code (offset+state.program.weight.val) environment)
    (ArenaAction.load_read code (offset+state.program.phase.val) environment)

theorem reload_relations (state : State) (code : Array Node) (offset : Nat) (environment : Nat → Bool) :
    readRelations (reload state code offset) environment=state.relations.all (fun item =>
      truth ((run environment code).getD (offset+item.relation.left.val) 0)==
        truth ((run environment code).getD (offset+item.relation.right.val) 0)) := by
  simp only [readRelations,reload,List.all_map,Function.comp_def,ArenaAction.Relation.read,ArenaAction.load_read]

theorem reload_count (state : State) (code : Array Node) (offset : Nat) :
    (reload state code offset).relations.length=state.relations.length := by simp only [reload,List.length_map]

theorem reload_size (state : State) (code : Array Node) (offset : Nat) :
    (reload state code offset).arena.code.size ≤ code.size+1 := Reduce.compact_code_size code

def eligible (state : State) (item : Labeled state.arena) : Bool :=
  decide (state.arena.code.getD item.relation.left.val (.constant 0)=.input item.address) &&
    decide (item.address ∉ FunctionalSubstitution.inputs (ArenaAction.actualBody state.arena item.relation.right).code)

def choose (state : State) : Option (Labeled state.arena) := state.relations.find? (eligible state)

theorem choose_member (state : State) (item : Labeled state.arena) (found : choose state=some item) :
    item ∈ state.relations := List.mem_of_find?_eq_some found

theorem choose_eligible (state : State) (item : Labeled state.arena) (found : choose state=some item) :
    eligible state item=true := List.find?_some found

theorem eligible_fixed (state : State) (item : Labeled state.arena) (allowed : eligible state item=true)
    (environment : Nat → Bool) (accepted : item.relation.read environment=true) :
    ArenaAction.Action.environment state.arena item.address item.relation.right environment=environment := by
  have properties :
      state.arena.code.getD item.relation.left.val (.constant 0)=.input item.address ∧
      item.address ∉ FunctionalSubstitution.inputs (ArenaAction.actualBody state.arena item.relation.right).code := by
    simpa only [eligible,Bool.and_eq_true,decide_eq_true_eq] using allowed
  have node := properties.1
  have free := properties.2
  have left := ArenaAction.run_equation state.arena.code state.arena.forward environment
    item.relation.left.val item.relation.left.isLt
  rw [node] at left
  have body := ArenaAction.body_read state.arena.code state.arena.forward item.relation.right environment
  have relation : environment item.address=truth ((ArenaAction.actualBody state.arena item.relation.right).eval environment) := by
    unfold ArenaAction.Relation.read at accepted
    rw [left] at accepted
    simp only [Node.run,truth_bit] at accepted
    exact (beq_iff_eq.mp accepted).trans (congrArg truth body).symm
  have performed := (ArenaAction.apply_performed state.arena item.address item.relation.right).mpr free
  simp only [ArenaAction.Action.environment,performed,if_true]
  exact FunctionalSubstitution.bind_fixes _ _ _ relation

def step (state : State) : State :=
  match choose state with
  | none => state
  | some item => next state item.address item.relation.right

def stepEnvironment (state : State) (environment : Nat → Bool) : Nat → Bool :=
  match choose state with
  | none => environment
  | some item => ArenaAction.Action.environment state.arena item.address item.relation.right environment

theorem step_program (state : State) (environment : Nat → Bool) :
    (step state).program.program.eval environment=state.program.program.eval (stepEnvironment state environment) := by
  unfold step
  cases found : choose state
  · simp only [stepEnvironment,found]
  · simp only [stepEnvironment,found,next_program]

theorem step_size (state : State) : (step state).arena.code.size=state.arena.code.size := by
  unfold step
  cases choose state <;> simp only [next_size]

theorem step_count (state : State) : (step state).relations.length=state.relations.length := by
  unfold step
  cases choose state <;> simp only [next_count]

theorem step_valid (state : State) (valid : Valid state) : Valid (step state) := by
  unfold step
  cases choose state with
  | none => exact valid
  | some item => exact next_valid state valid item.address item.relation.right

theorem step_fixed (state : State) (valid : Valid state) (environment : Nat → Bool)
    (accepted : truth (state.program.program.eval environment)=true) : stepEnvironment state environment=environment := by
  cases found : choose state with
  | none => simp only [stepEnvironment,found]
  | some item =>
      simp only [stepEnvironment,found]
      exact eligible_fixed state item (choose_eligible state item found) environment
        (List.all_eq_true.mp (valid environment accepted) item (choose_member state item found))

theorem step_correct (state : State) (valid : Valid state) :
    (∃ environment, truth ((step state).program.program.eval environment)=true) ↔
      ∃ environment, truth (state.program.program.eval environment)=true := by
  constructor
  · rintro ⟨environment,accepted⟩
    exact ⟨stepEnvironment state environment,by simpa only [step_program] using accepted⟩
  · rintro ⟨environment,accepted⟩
    refine ⟨environment,?_⟩
    rw [step_program,step_fixed state valid environment accepted]
    exact accepted

def selected (state : State) (item : Labeled state.arena) : Instruction :=
  ⟨item.address,ArenaAction.actualBody state.arena item.relation.right⟩

theorem selected_environment (state : State) (item : Labeled state.arena) (allowed : eligible state item=true)
    (environment : Nat → Bool) :
    ArenaAction.Action.environment state.arena item.address item.relation.right environment=(selected state item).bind environment := by
  have free : item.address ∉ FunctionalSubstitution.inputs (ArenaAction.actualBody state.arena item.relation.right).code := by
    simp only [eligible,Bool.and_eq_true,decide_eq_true_eq] at allowed
    exact allowed.2
  simp only [ArenaAction.Action.environment,(ArenaAction.apply_performed _ _ _).mpr free,if_true,selected,Instruction.bind]

structure Run where
  state : State
  instructions : List Instruction

def drive : Nat → State → Run
  | 0,state => ⟨state,[]⟩
  | fuel+1,state =>
      match choose state with
      | none => ⟨state,[]⟩
      | some item =>
          let generated := drive fuel (next state item.address item.relation.right)
          ⟨generated.state,selected state item::generated.instructions⟩

theorem drive_none (fuel : Nat) (state : State) (found : choose state=none) :
    drive (fuel+1) state=⟨state,[]⟩ := by rw [drive,found]

theorem drive_some (fuel : Nat) (state : State) (item : Labeled state.arena) (found : choose state=some item) :
    drive (fuel+1) state=
      ⟨(drive fuel (next state item.address item.relation.right)).state,
        selected state item::(drive fuel (next state item.address item.relation.right)).instructions⟩ := by rw [drive,found]

theorem drive_size (fuel : Nat) (state : State) :
    (drive fuel state).state.arena.code.size=state.arena.code.size := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      unfold drive
      split
      · rfl
      · exact (ih _).trans (next_size _ _ _)

theorem drive_count (fuel : Nat) (state : State) :
    (drive fuel state).state.relations.length=state.relations.length := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases found : choose state with
      | none => rw [drive_none fuel state found]
      | some item =>
          rw [drive_some fuel state item found]
          exact (ih _).trans (next_count _ _ _)

theorem drive_length (fuel : Nat) (state : State) : (drive fuel state).instructions.length ≤ fuel := by
  induction fuel generalizing state with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
      unfold drive
      split
      · simp
      · simpa only [List.length_cons] using Nat.succ_le_succ (ih _)

theorem drive_inventory (fuel : Nat) (state : State) :
    ((drive fuel state).instructions.map (fun call => call.body.code.size)).sum ≤ fuel*state.arena.code.size := by
  induction fuel generalizing state with
  | zero => simp [drive]
  | succ fuel ih =>
      cases found : choose state with
      | none => rw [drive_none fuel state found]; simp
      | some item =>
          rw [drive_some fuel state item found]
          simp only [List.map_cons,List.sum_cons,selected]
          have tail := ih (next state item.address item.relation.right)
          rw [next_size] at tail
          have first := ArenaAction.actualBody_size state.arena item.relation.right
          nlinarith only [tail,first]

theorem drive_valid (fuel : Nat) (state : State) (valid : Valid state) : Valid (drive fuel state).state := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      unfold drive
      split
      · exact valid
      · exact ih _ (next_valid _ valid _ _)

theorem drive_program (fuel : Nat) (state : State) (environment : Nat → Bool) :
    (drive fuel state).state.program.program.eval environment=
      state.program.program.eval (FunctionalSubstitution.fill (drive fuel state).instructions environment) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases found : choose state with
      | none => rw [drive_none fuel state found]; rfl
      | some item =>
          rw [drive_some fuel state item found]
          change (drive fuel (next state item.address item.relation.right)).state.program.program.eval environment=_
          rw [ih,next_program,selected_environment state item (choose_eligible state item found)]
          rfl

theorem drive_fixed (fuel : Nat) (state : State) (valid : Valid state) (environment : Nat → Bool)
    (accepted : truth (state.program.program.eval environment)=true) :
    ∀ instruction ∈ (drive fuel state).instructions, instruction.bind environment=environment := by
  induction fuel generalizing state with
  | zero => simp [drive]
  | succ fuel ih =>
      unfold drive
      split
      · simp
      · rename_i item found
        have allowed := choose_eligible state item found
        have fixed := eligible_fixed state item allowed environment
          (List.all_eq_true.mp (valid environment accepted) item (choose_member state item found))
        intro instruction member
        rcases List.mem_cons.mp member with rfl | member
        · exact (selected_environment state item allowed environment).symm.trans fixed
        · apply ih _ (next_valid _ valid _ _) (by rw [next_program,fixed]; exact accepted) instruction member

theorem drive_read (fuel : Nat) (state : State) (valid : Valid state) (environment : Nat → Bool) :
    (FunctionalAffine.legal (drive fuel state).instructions environment &&
      truth ((drive fuel state).state.program.program.eval environment))=truth (state.program.program.eval environment) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨legal,accepted⟩
    rw [drive_program,FunctionalAffine.legal_fixed _ _ legal] at accepted
    exact accepted
  · intro accepted
    have fixed := drive_fixed fuel state valid environment accepted
    refine ⟨FunctionalAffine.legal_of_fixed _ _ fixed,?_⟩
    rw [drive_program,FunctionalSubstitution.fill_fixes _ _ fixed]
    exact accepted

theorem drive_correct (fuel : Nat) (state : State) (valid : Valid state) :
    FunctionalSubstitution.decideProgram (drive fuel state).state.program.program=true ↔
      ∃ environment, truth (state.program.program.eval environment)=true := by
  rw [FunctionalSubstitution.decideProgram_correct]
  constructor
  · rintro ⟨environment,accepted⟩
    refine ⟨FunctionalSubstitution.fill (drive fuel state).instructions environment,?_⟩
    simpa only [drive_program] using accepted
  · rintro ⟨environment,accepted⟩
    refine ⟨environment,?_⟩
    rw [drive_program,FunctionalSubstitution.fill_fixes _ _ (drive_fixed fuel state valid environment accepted)]
    exact accepted

structure Front where
  private mk ::
  table : Array Affine.Row
  candidates : List Instruction
  initial : Program
  cells : Nat

def front {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) : Front :=
  let table := ConditionalCandidateCost.coordinates n basis
  let free := ConditionalCandidateCost.width n basis
  let prior := ConditionalCandidateCost.Functional.candidates table.value formula
  let conditional := ForcedBranches.branches formula basis table.value free.value (List.finRange n)
  let calls := prior.value++conditional.value
  let generatedCells := table.cells+free.cells+prior.cells+conditional.cells+
    2*(AffineCollect.tableSize table.value+FunctionalSchedule.Cost.inputSize prior.value+
      FunctionalSchedule.Cost.inputSize conditional.value)+2*n+20
  let initial := FunctionalSourceCost.Initial.compile table.value formula
  ⟨table.value,calls,initial.value,generatedCells+initial.cells+
    2*(AffineCollect.tableSize table.value+FunctionalSchedule.Cost.inputSize calls+initial.value.code.size)+12⟩

theorem front_candidates {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) :
    (front formula basis).candidates=(ForcedBranches.generate formula basis).value := rfl

theorem front_table {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) :
    (front formula basis).table=Affine.Table.coordinates n basis := rfl

theorem front_initial {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) :
    (front formula basis).initial=Affine.Acceptance.compile (front formula basis).table formula :=
  FunctionalSourceCost.Initial.compile_value _ _

theorem front_counter {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) :
    (front formula basis).cells=(ForcedBranches.generate formula basis).cells+
      (FunctionalSourceCost.Initial.compile (Affine.Table.coordinates n basis) formula).cells+
      2*(AffineCollect.tableSize (front formula basis).table+
        FunctionalSchedule.Cost.inputSize (front formula basis).candidates+(front formula basis).initial.code.size)+12 := rfl

theorem front_entails {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (environment : Nat → Bool)
    (accepted : truth ((front formula basis).initial.eval environment)=true)
    (call : Instruction) (present : call ∈ (front formula basis).candidates) : call.bind environment=environment := by
  rw [front_initial,front_table] at accepted
  exact ForcedBranches.generate_entails formula basis valid environment accepted call present

def compile {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) (fuel : Nat) : Run :=
  let source := front formula basis
  drive fuel (build source.initial source.candidates)

theorem compile_read {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (fuel : Nat) (environment : Nat → Bool) :
    (FunctionalAffine.legal (compile formula basis fuel).instructions environment &&
      truth ((compile formula basis fuel).state.program.program.eval environment))=
      CNFFormula.eval formula (Affine.Gates.coordinate (Affine.Table.coordinates n basis) environment) := by
  rw [compile,drive_read _ _ (build_valid _ _ (front_entails formula basis valid)),
    build_program,front_initial,Affine.Acceptance.eval_compile,truth_bit]
  rfl

theorem compile_program {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (fuel : Nat) (environment : Nat → Bool) :
    (compile formula basis fuel).state.program.program.eval environment=bit
      (CNFFormula.eval formula (Affine.Gates.coordinate (Affine.Table.coordinates n basis)
        (FunctionalSubstitution.fill (compile formula basis fuel).instructions environment))) := by
  rw [compile,drive_program,build_program,front_initial,Affine.Acceptance.eval_compile]
  rfl

theorem compile_count {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) (fuel : Nat) :
    (compile formula basis fuel).state.relations.length=(ForcedBranches.generate formula basis).value.length := by
  rw [compile,drive_count,build_count,front_candidates]

theorem compile_correct {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (fuel : Nat) :
    FunctionalSubstitution.decideProgram (compile formula basis fuel).state.program.program=true ↔
      ∃ environment, CNFFormula.eval formula (Affine.Gates.coordinate (Affine.Table.coordinates n basis) environment)=true := by
  rw [compile,drive_correct _ _ (build_valid _ _ (front_entails formula basis valid))]
  simp only [build_program,front_initial,Affine.Acceptance.eval_compile,front_table,truth_bit]

def sourceBound (n clauses literals : Nat) : Nat :=
  FunctionalSourceCost.initialBound n clauses literals+ForcedBranches.Cost.outputStorage n clauses+1

theorem compile_size {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) (fuel : Nat) :
    (compile formula basis fuel).state.arena.code.size ≤ sourceBound n formula.length (Affine.Extract.literalCount formula) := by
  rw [compile,drive_size]
  have sum_le : ∀ calls : List Instruction,
      (calls.map (fun call => call.body.code.size+1)).sum ≤ FunctionalSchedule.Cost.inputSize calls := by
    intro calls
    induction calls with
    | nil => simp [FunctionalSchedule.Cost.inputSize]
    | cons call rest ih =>
        simp only [List.map_cons,List.sum_cons,FunctionalSchedule.Cost.inputSize,
          FunctionalSchedule.Cost.instructionSize] at ih ⊢
        omega
  have bound := build_size (front formula basis).initial (front formula basis).candidates
  have original := ForcedBranches.Cost.initial_size formula basis
  have added := ForcedBranches.Cost.generate_storage formula basis valid
  have records := sum_le (front formula basis).candidates
  change (front formula basis).initial.code.size ≤ _ at original
  change FunctionalSchedule.Cost.inputSize (front formula basis).candidates ≤ _ at added
  unfold sourceBound
  omega

def frontBudget (n clauses literals basisSize : Nat) : Nat :=
  ForcedBranches.Cost.generateBudget n clauses literals basisSize+
    FunctionalSourceCost.Initial.compileBudget (AffineCarrier.Cost.cellBound n) clauses literals+
    2*(AffineCarrier.Cost.cellBound n+ForcedBranches.Cost.outputStorage n clauses+
      FunctionalSourceCost.initialBound n clauses literals)+12

theorem front_cells {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row)
    (valid : Affine.Triangular basis ∧ Affine.RowsWithin n basis) :
    (front formula basis).cells ≤ frontBudget n formula.length (Affine.Extract.literalCount formula) (AffineCarrier.cellSize basis) := by
  have generated := ForcedBranches.Cost.generate_cells formula basis valid
  have table := AffineCollect.Cost.coordinate_size n basis
  have initial := FunctionalSourceCost.Initial.compile_cells (Affine.Table.coordinates n basis) formula _ table
  have size := ForcedBranches.Cost.initial_size formula basis
  have calls := ForcedBranches.Cost.generate_storage formula basis valid
  rw [front_counter,front_table,front_candidates]
  change (front formula basis).initial.code.size ≤ _ at size
  unfold frontBudget
  omega

end SaturationMonoid.ComplexityProjection.SATSource.ArenaSource

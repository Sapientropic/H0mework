import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Effects.Relations.Cost

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.EffectMemory
open InterferenceProgram

/-- A request contains the actual primitive arguments, independently of their addresses. -/
inductive Request where
  | value : Int → Request
  | input : Bool → Request
  | add : Int → Int → Request
  | mul : Int → Int → Request
  | neg : Int → Request
  | band : Bool → Bool → Request
  | bxor : Bool → Bool → Request
  | bnot : Bool → Request
  | phase : Int → Request
  | select : Int → Int → Int → Request
  deriving DecidableEq, Repr

def Request.eval : Request → Int
  | .value z => z
  | .input b => bit b
  | .add a b => a+b
  | .mul a b => a*b
  | .neg a => -a
  | .band a b => bit (a&&b)
  | .bxor a b => bit (a^^b)
  | .bnot a => bit (!a)
  | .phase a => sign a
  | .select c a b => if c=0 then a else b

def request (point : Nat → Bool) (read : Nat → Int) : Node → Request
  | .constant z => .value z
  | .input i => .input (point i)
  | .add a b => .add (read a) (read b)
  | .mul a b => .mul (read a) (read b)
  | .neg a => .neg (read a)
  | .band a b => .band (truth (read a)) (truth (read b))
  | .bxor a b => .bxor (truth (read a)) (truth (read b))
  | .bnot a => .bnot (truth (read a))
  | .phase a => .phase (read a)
  | .select c a b => .select (read c) (read a) (read b)

theorem request_eval (point : Nat → Bool) (values : Array Int) (node : Node) :
    (request point (fun i => values.getD i 0) node).eval=node.run point values := by
  cases node <;> rfl

structure Entry where
  key : Request
  value : Int
  sound : value=key.eval
  deriving Repr

def entry (key : Request) : Entry := ⟨key,key.eval,rfl⟩
def emptyEntry : Entry := entry (.value 0)
abbrev Memory := Array Entry

def read (memory : Memory) (i : Nat) : Int := (memory.getD i emptyEntry).value
def prefixRead (memory : Memory) (cursor i : Nat) : Int := if i < cursor then read memory i else 0

def put (memory : Memory) (cursor : Nat) (value : Entry) : Memory :=
  if cursor < memory.size then memory.setIfInBounds cursor value else memory.push value

theorem put_size (memory : Memory) (cursor : Nat) (value : Entry) :
    (put memory cursor value).size ≤ memory.size+1 := by
  unfold put
  split <;> simp

theorem put_get (memory : Memory) (cursor : Nat) (value : Entry) (inside : cursor ≤ memory.size) (i : Nat) :
    (put memory cursor value).getD i emptyEntry=if i=cursor then value else memory.getD i emptyEntry := by
  unfold put
  split
  · rename_i old
    simp only [Array.getD_eq_getD_getElem?,Array.getElem?_setIfInBounds]
    by_cases hit : i=cursor
    · simp [hit,old]
    · simp [hit,Ne.symm hit]
  · rename_i fresh
    have last : cursor=memory.size := by omega
    subst cursor
    simp only [Array.getD_eq_getD_getElem?,Array.getElem?_push]
    by_cases hit : i=memory.size <;> simp [hit]

structure Step where
  memory : Memory
  computed : Nat
  cells : Nat
  deriving Repr

/-- A hit returns the retained array itself; neither the node result nor the value table is rebuilt. -/
def update (memory : Memory) (cursor : Nat) (key : Request) : Step :=
  if cursor < memory.size ∧ (memory.getD cursor emptyEntry).key=key then
    ⟨memory,0,16*(memory.size+1)+16⟩
  else ⟨put memory cursor (entry key),1,32*(memory.size+1)+32⟩

theorem update_read (memory : Memory) (cursor : Nat) (key : Request) (inside : cursor ≤ memory.size) (i : Nat) :
    read (update memory cursor key).memory i=if i=cursor then key.eval else read memory i := by
  unfold update
  split
  · rename_i hit
    by_cases same : i=cursor
    · subst i
      simpa only [read,ite_true,hit.2] using (memory.getD cursor emptyEntry).sound
    · simp only [if_neg same]
  · simp only [read,put_get memory cursor (entry key) inside i]
    split <;> rfl

theorem update_size (memory : Memory) (cursor : Nat) (key : Request) (inside : cursor ≤ memory.size) :
    cursor+1 ≤ (update memory cursor key).memory.size ∧
      (update memory cursor key).memory.size ≤ memory.size+1 := by
  unfold update
  split
  · rename_i hit
    exact ⟨by dsimp only; omega,by dsimp only; omega⟩
  · dsimp only
    refine ⟨?_,put_size _ _ _⟩
    unfold put
    split <;> simp_all

theorem update_computed (memory : Memory) (cursor : Nat) (key : Request) : (update memory cursor key).computed ≤ 1 := by
  unfold update
  split <;> simp

theorem update_cells (memory : Memory) (cursor : Nat) (key : Request) :
    (update memory cursor key).cells ≤ 32*(memory.size+1)+32 := by
  unfold update
  split <;> dsimp only <;> omega

theorem update_entry (memory : Memory) (cursor : Nat) (key : Request) (inside : cursor ≤ memory.size) :
    ((update memory cursor key).memory.getD cursor emptyEntry).key=key := by
  unfold update
  split
  · rename_i hit
    exact hit.2
  · change ((put memory cursor (entry key)).getD cursor emptyEntry).key=key
    rw [put_get memory cursor (entry key) inside cursor,if_pos rfl]
    rfl

theorem update_before (memory : Memory) (cursor : Nat) (key : Request) (inside : cursor ≤ memory.size)
    (i : Nat) (earlier : i < cursor) :
    (update memory cursor key).memory.getD i emptyEntry=memory.getD i emptyEntry := by
  unfold update
  split
  · rfl
  · rw [put_get memory cursor (entry key) inside i,if_neg (by omega)]

theorem update_hit (memory : Memory) (cursor : Nat) (key : Request)
    (hit : cursor < memory.size ∧ (memory.getD cursor emptyEntry).key=key) :
    (update memory cursor key).memory=memory ∧ (update memory cursor key).computed=0 := by
  simp only [update,if_pos hit,and_self]

def run (point : Nat → Bool) : Nat → Memory → List Node → Step
  | _,memory,[] => ⟨memory,0,1⟩
  | cursor,memory,node::rest =>
      let next := update memory cursor (request point (prefixRead memory cursor) node)
      let tail := run point (cursor+1) next.memory rest
      ⟨tail.memory,next.computed+tail.computed,next.cells+tail.cells+8⟩

def Agrees (memory : Memory) (values : Array Int) : Prop :=
  values.size ≤ memory.size ∧ ∀ i, prefixRead memory values.size i=values.getD i 0

theorem agrees_empty (memory : Memory) : Agrees memory #[] := by
  simp [Agrees,prefixRead]

theorem agrees_update (point : Nat → Bool) (memory : Memory) (values : Array Int) (agrees : Agrees memory values) (node : Node) :
    Agrees (update memory values.size (request point (prefixRead memory values.size) node)).memory
      (values.push (node.run point values)) := by
  have keys : request point (prefixRead memory values.size) node=request point (fun i => values.getD i 0) node :=
    congrArg (fun read => request point read node) (funext agrees.2)
  refine ⟨by simpa only [Array.size_push] using (update_size memory values.size _ agrees.1).1,?_⟩
  intro i
  rw [Array.size_push,prefixRead,getD_push_any]
  by_cases last : i=values.size
  · simp only [last,Nat.lt_succ_self,ite_true,update_read memory values.size _ agrees.1,keys,request_eval]
  · rw [if_neg last]
    by_cases before : i < values.size
    · rw [if_pos (by omega),update_read memory values.size _ agrees.1,if_neg last]
      simpa only [prefixRead,if_pos before] using agrees.2 i
    · rw [if_neg (by omega)]
      simpa only [prefixRead,if_neg before] using agrees.2 i

theorem run_agrees (point : Nat → Bool) (memory : Memory) (values : Array Int) (code : List Node)
    (agrees : Agrees memory values) :
    Agrees (run point values.size memory code).memory (runCode point values code) := by
  induction code generalizing values memory with
  | nil => exact agrees
  | cons node rest ih =>
      simpa only [run,runCode,Array.size_push] using
        ih _ _ (agrees_update point memory values agrees node)

theorem run_size (point : Nat → Bool) (memory : Memory) (cursor : Nat) (code : List Node)
    (inside : cursor ≤ memory.size) : (run point cursor memory code).memory.size ≤ memory.size+code.length := by
  induction code generalizing cursor memory with
  | nil => simp [run]
  | cons node rest ih =>
      have size := update_size memory cursor (request point (prefixRead memory cursor) node) inside
      have tail := ih _ _ size.1
      simp only [run,List.length_cons]
      omega

theorem run_computed (point : Nat → Bool) (memory : Memory) (cursor : Nat) (code : List Node) :
    (run point cursor memory code).computed ≤ code.length := by
  induction code generalizing cursor memory with
  | nil => simp [run]
  | cons node rest ih =>
      have first := update_computed memory cursor (request point (prefixRead memory cursor) node)
      have tail := ih (update memory cursor (request point (prefixRead memory cursor) node)).memory (cursor+1)
      simp only [run,List.length_cons]
      omega

theorem run_cells (point : Nat → Bool) (memory : Memory) (cursor : Nat) (code : List Node)
    (inside : cursor ≤ memory.size) :
    (run point cursor memory code).cells ≤ code.length*(32*(memory.size+code.length+1)+40)+1 := by
  induction code generalizing cursor memory with
  | nil => simp [run]
  | cons node rest ih =>
      let key := request point (prefixRead memory cursor) node
      have size := update_size memory cursor key inside
      have first := update_cells memory cursor key
      have tail := ih _ _ size.1
      have mono : rest.length*(32*((update memory cursor key).memory.size+rest.length+1)+40) ≤
          rest.length*(32*(memory.size+(rest.length+1)+1)+40) := Nat.mul_le_mul_left _ (by omega)
      change (update memory cursor key).cells+(run point (cursor+1) (update memory cursor key).memory rest).cells+8 ≤ _
      simp only [List.length_cons]
      nlinarith

theorem run_before (point : Nat → Bool) (memory : Memory) (cursor : Nat) (code : List Node)
    (inside : cursor ≤ memory.size) (i : Nat) (earlier : i < cursor) :
    (run point cursor memory code).memory.getD i emptyEntry=memory.getD i emptyEntry := by
  induction code generalizing cursor memory with
  | nil => rfl
  | cons node rest ih =>
      let key := request point (prefixRead memory cursor) node
      change (run point (cursor+1) (update memory cursor key).memory rest).memory.getD i emptyEntry=_
      rw [ih _ _ (update_size memory cursor key inside).1 (by omega),update_before memory cursor key inside i earlier]

theorem update_size_mono (memory : Memory) (cursor : Nat) (key : Request) :
    memory.size ≤ (update memory cursor key).memory.size := by
  unfold update
  split
  · exact le_rfl
  · dsimp only
    unfold put
    split <;> simp

theorem run_size_mono (point : Nat → Bool) (memory : Memory) (cursor : Nat) (code : List Node) :
    memory.size ≤ (run point cursor memory code).memory.size := by
  induction code generalizing cursor memory with
  | nil => exact le_rfl
  | cons node rest ih =>
      exact (update_size_mono memory cursor _).trans (ih _ _)

def Ready (point : Nat → Bool) : Nat → Memory → List Node → Prop
  | _,_,[] => True
  | cursor,memory,node::rest =>
      (cursor < memory.size ∧ (memory.getD cursor emptyEntry).key=request point (prefixRead memory cursor) node) ∧
      Ready point (cursor+1) memory rest

theorem run_ready (point : Nat → Bool) (memory : Memory) (cursor : Nat) (code : List Node)
    (inside : cursor ≤ memory.size) : Ready point cursor (run point cursor memory code).memory code := by
  induction code generalizing memory cursor with
  | nil => trivial
  | cons node rest ih =>
      let key := request point (prefixRead memory cursor) node
      let next := update memory cursor key
      let tail := run point (cursor+1) next.memory rest
      have nextSize := update_size memory cursor key inside
      have atRoot := run_before point next.memory (cursor+1) rest nextSize.1 cursor (by omega)
      have nextKey := update_entry memory cursor key inside
      have prefixSame : prefixRead tail.memory cursor=prefixRead memory cursor := by
        funext i
        unfold prefixRead
        split
        · rename_i earlier
          unfold read
          rw [run_before point next.memory (cursor+1) rest nextSize.1 i (by omega),update_before memory cursor key inside i earlier]
        · rfl
      have sizeMono := run_size_mono point next.memory (cursor+1) rest
      change ((cursor < tail.memory.size ∧ (tail.memory.getD cursor emptyEntry).key=request point (prefixRead tail.memory cursor) node) ∧
        Ready point (cursor+1) tail.memory rest)
      refine ⟨⟨(Nat.lt_of_lt_of_le (Nat.lt_succ_self cursor) nextSize.1).trans_le sizeMono,?_⟩,
        ih next.memory (cursor+1) nextSize.1⟩
      rw [prefixSame,atRoot]
      exact nextKey

theorem run_reuse (point : Nat → Bool) (memory : Memory) (cursor : Nat) (code : List Node)
    (ready : Ready point cursor memory code) :
    (run point cursor memory code).memory=memory ∧ (run point cursor memory code).computed=0 := by
  induction code generalizing cursor memory with
  | nil => exact ⟨rfl,rfl⟩
  | cons node rest ih =>
      have hit := update_hit memory cursor (request point (prefixRead memory cursor) node) ready.1
      have tail := ih memory (cursor+1) ready.2
      simp only [run,hit.1,hit.2,Nat.zero_add,tail.1,tail.2,and_self]

def observe (program : Program) (point : Nat → Bool) (memory : Memory) : Step :=
  run point 0 memory program.code.toList

def amplitude (program : Program) (memory : Memory) : Int :=
  read memory program.weight.val * sign (read memory program.phase.val)

theorem observe_read (program : Program) (point : Nat → Bool) (memory : Memory) :
    amplitude program (observe program point memory).memory=program.eval point := by
  have values := run_agrees point memory #[] program.code.toList (agrees_empty memory)
  change Agrees (observe program point memory).memory (InterferenceProgram.run point program.code) at values
  have weight := values.2 program.weight.val
  have phase := values.2 program.phase.val
  simp only [InterferenceProgram.run_size,prefixRead,program.weight.isLt,program.phase.isLt,ite_true] at weight phase
  exact congrArg₂ (fun w p => w*sign p) weight phase

theorem observe_reuse (program : Program) (point : Nat → Bool) (memory : Memory) :
    let retained := (observe program point memory).memory
    (observe program point retained).memory=retained ∧ (observe program point retained).computed=0 :=
  run_reuse point _ 0 _ (run_ready point memory 0 _ (Nat.zero_le _))

theorem update_capacity (memory : Memory) (cursor : Nat) (key : Request) :
    (update memory cursor key).memory.size ≤ max memory.size (cursor+1) := by
  unfold update
  split
  · exact Nat.le_max_left _ _
  · dsimp only
    unfold put
    split <;> simp_all

theorem run_capacity (point : Nat → Bool) (memory : Memory) (cursor : Nat) (code : List Node) :
    (run point cursor memory code).memory.size ≤ max memory.size (cursor+code.length) := by
  induction code generalizing cursor memory with
  | nil => exact Nat.le_max_left _ _
  | cons node rest ih =>
      have first := update_capacity memory cursor (request point (prefixRead memory cursor) node)
      have tail := ih (update memory cursor (request point (prefixRead memory cursor) node)).memory (cursor+1)
      simp only [run,List.length_cons]
      omega

theorem observe_capacity (program : Program) (point : Nat → Bool) (memory : Memory) :
    (observe program point memory).memory.size ≤ max memory.size program.code.size := by
  simpa only [observe,Array.length_toList,Nat.zero_add] using run_capacity point memory 0 program.code.toList

structure Sample where
  memory : Memory
  value : Nat
  leaves : Nat
  computed : Nat
  cells : Nat
  deriving Repr

def leaf (cap : Nat) (program : Program) (point : Nat → Bool) (memory : Memory) : Sample :=
  let next := observe program point memory
  ⟨next.memory,(if truth (amplitude program next.memory) then cap else 1),1,next.computed,
    next.cells+32*(next.memory.size+1)+32⟩

def collect (cap : Nat) (program : Program) : List Nat → (Nat → Bool) → Memory → Sample
  | [],point,memory =>
      let result := leaf cap program point memory
      {result with value:=min cap result.value}
  | i::rest,point,memory =>
      let first := collect cap program rest (Function.update point i false) memory
      if first.value=cap then {first with cells:=first.cells+16} else
        let second := collect cap program rest (Function.update point i true) first.memory
        ⟨second.memory,min cap (first.value+second.value),first.leaves+second.leaves,
          first.computed+second.computed,first.cells+second.cells+16⟩

theorem collect_original (cap : Nat) (program : Program) (indices : List Nat) (point : Nat → Bool) (memory : Memory) :
    (collect cap program indices point memory).value=
      (EffectReading.collect cap indices (EffectReading.observe program cap) point).value ∧
    (collect cap program indices point memory).leaves=
      (EffectReading.collect cap indices (EffectReading.observe program cap) point).leaves := by
  induction indices generalizing point memory with
  | nil =>
      simp only [collect,leaf,observe_read,EffectReading.collect,EffectReading.observe_value]
      exact ⟨trivial,rfl⟩
  | cons i rest ih =>
      have first := ih (Function.update point i false) memory
      have second := ih (Function.update point i true) (collect cap program rest (Function.update point i false) memory).memory
      simp only [collect,EffectReading.collect,first.1]
      split <;> simp_all

theorem collect_capacity (cap : Nat) (program : Program) (indices : List Nat) (point : Nat → Bool) (memory : Memory) :
    (collect cap program indices point memory).memory.size ≤ max memory.size program.code.size := by
  induction indices generalizing point memory with
  | nil => exact observe_capacity program point memory
  | cons i rest ih =>
      have first := ih (Function.update point i false) memory
      have second := ih (Function.update point i true) (collect cap program rest (Function.update point i false) memory).memory
      simp only [collect]
      split <;> dsimp only <;> omega

theorem collect_leaves_pos (cap : Nat) (program : Program) (indices : List Nat) (point : Nat → Bool) (memory : Memory) :
    0 < (collect cap program indices point memory).leaves := by
  rw [(collect_original cap program indices point memory).2]
  exact EffectReading.collect_leaves_pos _ _ _ (fun _ => Nat.zero_lt_one) _

theorem collect_computed (cap : Nat) (program : Program) (indices : List Nat) (point : Nat → Bool) (memory : Memory) :
    (collect cap program indices point memory).computed ≤ program.code.size*(collect cap program indices point memory).leaves := by
  induction indices generalizing point memory with
  | nil => simpa only [collect,leaf,observe,Array.length_toList,Nat.mul_one] using run_computed point memory 0 program.code.toList
  | cons i rest ih =>
      have first := ih (Function.update point i false) memory
      have second := ih (Function.update point i true) (collect cap program rest (Function.update point i false) memory).memory
      simp only [collect]
      split
      · exact first
      · dsimp only
        rw [Nat.mul_add]
        exact Nat.add_le_add first second

def leafBudget (capacity nodes : Nat) : Nat := nodes*(32*(capacity+nodes+1)+40)+32*(capacity+1)+33

theorem leaf_cells (cap : Nat) (program : Program) (point : Nat → Bool) (memory : Memory) (capacity : Nat)
    (old : memory.size ≤ capacity) (code : program.code.size ≤ capacity) :
    (leaf cap program point memory).cells ≤ leafBudget capacity program.code.size := by
  have execution := run_cells point memory 0 program.code.toList (Nat.zero_le _)
  have size := observe_capacity program point memory
  have mono : program.code.size*(32*(memory.size+program.code.size+1)+40) ≤
      program.code.size*(32*(capacity+program.code.size+1)+40) := Nat.mul_le_mul_left _ (by omega)
  simp only [Array.length_toList] at execution
  change (observe program point memory).cells+32*((observe program point memory).memory.size+1)+32 ≤ _
  unfold leafBudget
  change (observe program point memory).cells ≤ _ at execution
  omega

theorem collect_cells (cap : Nat) (program : Program) (indices : List Nat) (point : Nat → Bool) (memory : Memory)
    (capacity : Nat) (old : memory.size ≤ capacity) (code : program.code.size ≤ capacity) :
    (collect cap program indices point memory).cells ≤
      (collect cap program indices point memory).leaves*(leafBudget capacity program.code.size+16*indices.length) := by
  induction indices generalizing point memory with
  | nil => simpa only [collect,leaf,List.length_nil,Nat.mul_zero,Nat.add_zero,Nat.one_mul] using leaf_cells cap program point memory capacity old code
  | cons i rest ih =>
      have first := ih (Function.update point i false) memory old
      have kept := collect_capacity cap program rest (Function.update point i false) memory
      have second := ih (Function.update point i true) (collect cap program rest (Function.update point i false) memory).memory (by omega)
      have positive := collect_leaves_pos cap program rest (Function.update point i false) memory
      simp only [collect,List.length_cons]
      split <;> dsimp only <;> nlinarith

def sample (program : Program) : Sample :=
  let support := ArenaCost.inputs program.code
  let result := collect (ForgettingScalar.boost support.value.length) program support.value InterferenceDecision.zeroEnvironment #[]
  {result with cells:=support.cells+result.cells+32*(program.code.size+support.value.length+1)+32}

theorem sample_value (program : Program) : (sample program).value=ForgettingScalar.programSignal program := by
  simp only [sample,ArenaCost.inputs_value]
  exact (collect_original _ _ _ _ _).1.trans (EffectReading.sample_value program)

theorem sample_capacity (program : Program) : (sample program).memory.size ≤ program.code.size := by
  simp only [sample,ArenaCost.inputs_value]
  simpa only [ForgettingScalar.programCapacity,Array.size_empty,Nat.zero_max] using collect_capacity (ForgettingScalar.programCapacity program) program (FunctionalSubstitution.inputs program.code) InterferenceDecision.zeroEnvironment #[]

theorem sample_computed (program : Program) : (sample program).computed ≤ program.code.size*(sample program).leaves := by
  simp only [sample,ArenaCost.inputs_value]
  exact collect_computed _ _ _ _ _

theorem sample_cells (program : Program) : (sample program).cells ≤
    ArenaCost.inputsBudget program.code.size+(sample program).leaves*
      (leafBudget program.code.size program.code.size+16*program.code.size)+32*(2*program.code.size+1)+32 := by
  have source := ArenaCost.inputs_cells program.code
  have support := FunctionalSubstitution.inputs_size program.code
  have work := collect_cells (ForgettingScalar.programCapacity program) program (FunctionalSubstitution.inputs program.code)
    InterferenceDecision.zeroEnvironment #[] program.code.size (Nat.zero_le _) le_rfl
  have mono : (collect (ForgettingScalar.programCapacity program) program (FunctionalSubstitution.inputs program.code) InterferenceDecision.zeroEnvironment #[]).leaves*
      (leafBudget program.code.size program.code.size+16*(FunctionalSubstitution.inputs program.code).length) ≤
    (collect (ForgettingScalar.programCapacity program) program (FunctionalSubstitution.inputs program.code) InterferenceDecision.zeroEnvironment #[]).leaves*
      (leafBudget program.code.size program.code.size+16*program.code.size) := Nat.mul_le_mul_left _ (by omega)
  simp only [ForgettingScalar.programCapacity] at work mono
  simp only [sample,ArenaCost.inputs_value]
  omega

def decideProgram (program : Program) : Bool :=
  let source := sample program
  let bucket := 4*source.value/ForgettingScalar.programCapacity program
  ForgettingScalar.adcRead ⟨bucket,by
    have bound := ForgettingScalar.programBucket_bound program
    change 4*(sample program).value/ForgettingScalar.programCapacity program < 5
    rw [sample_value]
    exact Nat.lt_succ_of_le bound⟩

theorem decideProgram_correct (program : Program) : decideProgram program=true ↔ ∃ point, truth (program.eval point)=true := by
  have same : decideProgram program=ForgettingScalar.programRead program := by
    simp only [decideProgram,sample_value,ForgettingScalar.programRead,ForgettingScalar.programBucket]
  rw [same,ForgettingScalar.programRead_correct]

def readOutput (source : PortUpdate.Output) : Bool :=
  if source.rejected then false else decideProgram (EffectRelationsCost.normalize (EffectConsumer.step source.frame.state.program.program)).value

theorem readOutput_original (source : PortUpdate.Output) : readOutput source=true ↔ PortUpdate.stateDecision source.frame.state source.rejected=true := by
  cases rejected : source.rejected <;>
    simp only [readOutput,rejected,Bool.false_eq_true,if_false,if_true,PortUpdate.stateDecision,Bool.not_false,Bool.not_true,
      Bool.true_and,Bool.false_and,decideProgram_correct,FunctionalSubstitution.decideProgram_correct,
      EffectRelationsCost.normalize_value,EffectRelations.normalize_correct,EffectConsumer.step_correct]

def decide {n : Nat} (formula : CNFFormula n) (basis : List Affine.Row) : Bool :=
  readOutput (ProductClosureCost.compile formula basis).value

theorem decide_original {n : Nat} (formula : CNFFormula n) : decide formula []=true ↔ CNFSatisfiable formula := by
  have same := (readOutput_original (ProductClosureCost.compile formula []).value).trans
    (ProductClosureCost.compile_decision formula [] ⟨Affine.triangular_nil,by simp [Affine.RowsWithin]⟩)
  simpa only [decide,FunctionalMessage.empty_formula,CNFSatisfiable] using same

theorem decide_original_no {n : Nat} (formula : CNFFormula n) : decide formula []=false ↔ ¬ CNFSatisfiable formula := by
  rw [Bool.eq_false_iff]
  exact not_congr (decide_original formula)

end SaturationMonoid.ComplexityProjection.SATSource.EffectMemory

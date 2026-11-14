import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FunctionalFeedback.Cost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ArenaAction
open InterferenceProgram

private theorem array_induction {α : Type} (motive : Array α → Prop) (empty : motive #[])
    (step : ∀ code node, motive code → motive (code.push node)) (code : Array α) : motive code := by
  cases code with
  | mk items =>
      induction items using List.reverseRecOn with
      | nil => exact empty
      | append_singleton items node ih => simpa using step items.toArray node ih

theorem run_equation (code : Array Node) (forward : Reduce.Forward code) (environment : Nat → Bool)
    (i : Nat) (bound : i < code.size) :
    (run environment code).getD i 0=(code.getD i (.constant 0)).run environment (run environment code) := by
  induction code using array_induction generalizing i with
  | empty => simp at bound
  | @step code node ih =>
      have before : Reduce.Forward code := by
        intro j member
        simpa only [Array.getElem_push_lt member] using forward j (by simp; omega)
      by_cases old : i < code.size
      · have nodeOld : (code.push node).getD i (.constant 0)=code.getD i (.constant 0) := by
          simp [Array.getD,old,show i < code.size+1 from by omega,Array.getElem_push_lt old]
        rw [nodeOld,run_push,getD_push_old _ _ i (by simpa only [run_size] using old),ih before i old]
        apply Reduce.node_congr
        intro j member
        have inside : Reduce.Within i (code.getD i (.constant 0)) := by
          simpa [Array.getD,old] using before i old
        exact (getD_push_old _ _ j (by rw [run_size]; exact (inside j member).trans old)).symm
      · have last : i=code.size := by simp only [Array.size_push] at bound; omega
        subst i
        have nodeLast : (code.push node).getD code.size (.constant 0)=node := by simp [Array.getD]
        rw [nodeLast,run_push]
        have inside : Reduce.Within code.size node := by
          simpa only [Array.getElem_push_eq] using forward code.size (by simp)
        rw [← run_size environment code,getD_push_last]
        exact (Reduce.node_push environment (run environment code) node (node.run environment (run environment code))
          (by simpa only [run_size] using inside)).symm

def mapPut (mapping : Array Nat) (index value : Nat) : Array Nat :=
  mapping.modify index (fun _ => value)

theorem mapPut_size (mapping : Array Nat) (index value : Nat) : (mapPut mapping index value).size=mapping.size := by
  simp [mapPut]

theorem mapPut_read (mapping : Array Nat) (index value query : Nat) (inside : index < mapping.size) :
    (mapPut mapping index value).getD query 0=if query=index then value else mapping.getD query 0 := by
  by_cases hit : query=index
  · subst query
    simp [mapPut,Array.getD,inside,Array.getElem_modify]
  · by_cases before : query < mapping.size
    · simp [mapPut,Array.getD,before,hit,Ne.symm hit,Array.getElem_modify]
    · simp [Array.getD,mapPut_size,before,hit]

def rewrite (address body : Nat) (mapping : Array Nat) : Node → Node
  | .input i => if i=address then .band body body else .input i
  | node => node.mapRefs (fun i => mapping.getD i 0)

theorem rewrite_value (address body : Nat) (mapping : Array Nat) (node : Node)
    (environment : Nat → Bool) (value : Bool) (source target : Array ℤ)
    (binding : truth (target.getD body 0)=value)
    (reads : ∀ i ∈ node.refs, target.getD (mapping.getD i 0) 0=source.getD i 0) :
    (rewrite address body mapping node).run environment target=
      node.run (Function.update environment address value) source := by
  cases node
  case input i =>
    by_cases same : i=address
    · subst i
      simp only [rewrite,ite_true,Node.run,Function.update_self,Bool.and_self]
      exact congrArg bit binding
    · simp [rewrite,same,Node.run,Function.update]
  all_goals simp_all [rewrite,Node.mapRefs,Node.run,Node.refs]

def step (needed : List Nat) (address body index : Nat) (frame : Cone.Frame) (node : Node) : Cone.Frame :=
  if Cone.has index needed then frame else
    ⟨frame.code.push (rewrite address body frame.mapping node),mapPut frame.mapping index frame.code.size⟩

def finish (needed : List Nat) (address body : Nat) : Nat → Cone.Frame → List Node → Cone.Frame
  | _,frame,[] => frame
  | index,frame,node::rest => finish needed address body (index+1) (step needed address body index frame node) rest

theorem rewrite_free (address body : Nat) (mapping : Array Nat) (node : Node) :
    FunctionalSubstitution.Node.Free address (rewrite address body mapping node) := by
  cases node <;> try trivial
  rename_i i
  by_cases same : i=address <;> simp [rewrite,same,FunctionalSubstitution.Node.Free]

theorem step_free (needed : List Nat) (address body index : Nat) (frame : Cone.Frame) (node : Node)
    (free : FunctionalSubstitution.Free address frame.code) :
    FunctionalSubstitution.Free address (step needed address body index frame node).code := by
  unfold step
  split
  · exact free
  · intro other member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with previous | rfl
    · exact free other previous
    · exact rewrite_free address body frame.mapping node

theorem finish_free (needed : List Nat) (address body offset : Nat) (frame : Cone.Frame) (code : List Node)
    (free : FunctionalSubstitution.Free address frame.code) :
    FunctionalSubstitution.Free address (finish needed address body offset frame code).code := by
  induction code generalizing offset frame with
  | nil => exact free
  | cons node rest ih => exact ih _ _ (step_free needed address body offset frame node free)

def Ready (needed : List Nat) (offset body : Nat) (environment : Nat → Bool) (value : Bool)
    (source : Array ℤ) (frame : Cone.Frame) : Prop :=
  Reduce.Forward frame.code ∧ frame.mapping.size=source.size ∧
    body < frame.code.size ∧ truth ((run environment frame.code).getD body 0)=value ∧
      ∀ i, i < source.size → i ∈ needed ∨ i < offset →
        frame.mapping.getD i 0 < frame.code.size ∧
          (run environment frame.code).getD (frame.mapping.getD i 0) 0=source.getD i 0

theorem step_ready (needed : List Nat) (address body index : Nat) (frame : Cone.Frame) (node : Node)
    (environment : Nat → Bool) (value : Bool) (source : Array ℤ)
    (ready : Ready needed index body environment value source frame)
    (bound : index < source.size) (inside : Reduce.Within index node)
    (equation : source.getD index 0=node.run (Function.update environment address value) source) :
    Ready needed (index+1) body environment value source (step needed address body index frame node) := by
  obtain ⟨forward,size,bodyBound,binding,reads⟩ := ready
  by_cases selected : index ∈ needed
  · have unchanged : step needed address body index frame node=frame := by
      simp [step,(Cone.has_true_iff index needed).mpr selected]
    rw [unchanged]
    refine ⟨forward,size,bodyBound,binding,?_⟩
    intro i bounded retained
    apply reads i bounded
    rcases retained with actual | earlier
    · exact Or.inl actual
    · by_cases same : i=index
      · exact Or.inl (same ▸ selected)
      · exact Or.inr (by omega)
  · have absent : Cone.has index needed=false := Bool.eq_false_iff.mpr (fun h => selected ((Cone.has_true_iff _ _).mp h))
    have dependencies (i : Nat) (member : i ∈ node.refs) := reads i ((inside i member).trans bound) (Or.inr (inside i member))
    have translated : Reduce.Within frame.code.size (rewrite address body frame.mapping node) := by
      cases node
      case input i =>
        by_cases same : i=address <;> simp [rewrite,same,Reduce.Within,Node.refs,bodyBound]
      all_goals simp_all [rewrite,Reduce.Within,Node.refs,Node.mapRefs]
    have result := rewrite_value address body frame.mapping node environment value source (run environment frame.code)
      binding (fun i member => (dependencies i member).2)
    simp only [step,absent,Bool.false_eq_true,if_false]
    refine ⟨Reduce.append_forward ⟨frame.code,[]⟩ forward _ translated,?_,?_,?_,?_⟩
    · rw [mapPut_size,size]
    · simp only [Array.size_push]; omega
    · rw [run_push,getD_push_old _ _ _ (by simpa only [run_size] using bodyBound)]
      exact binding
    · intro i bounded retained
      rw [mapPut_read frame.mapping index frame.code.size i (by omega)]
      by_cases current : i=index
      · subst i
        simp only [if_true,Array.size_push]
        refine ⟨by omega,?_⟩
        rw [run_push,← run_size environment frame.code,getD_push_last,result]
        exact equation.symm
      · simp only [if_neg current,Array.size_push]
        have previous : i ∈ needed ∨ i < index := by rcases retained with kept | earlier; exact Or.inl kept; exact Or.inr (by omega)
        have old := reads i bounded previous
        refine ⟨by omega,?_⟩
        rw [run_push,getD_push_old _ _ _ (by simpa only [run_size] using old.1)]
        exact old.2

theorem finish_ready (needed : List Nat) (address body offset : Nat) (frame : Cone.Frame) (code : List Node)
    (environment : Nat → Bool) (value : Bool) (source : Array ℤ)
    (ready : Ready needed offset body environment value source frame)
    (bound : offset+code.length ≤ source.size) (forward : Cone.ForwardFrom offset code)
    (equations : ∀ i (inside : i < code.length), source.getD (offset+i) 0=
      code[i].run (Function.update environment address value) source) :
    Ready needed (offset+code.length) body environment value source (finish needed address body offset frame code) := by
  induction code generalizing offset frame with
  | nil => simpa only [finish,List.length_nil,Nat.add_zero] using ready
  | cons node rest ih =>
      have within := forward 0 (by simp)
      change Reduce.Within offset node at within
      have equation := equations 0 (by simp)
      change source.getD offset 0=node.run (Function.update environment address value) source at equation
      have next := step_ready needed address body offset frame node environment value source ready
        (by simp only [List.length_cons] at bound; omega) within equation
      have generated := ih (offset+1) (step needed address body offset frame node) next
        (by simp only [List.length_cons] at bound; omega)
        (by
          intro i member
          have remaining := forward (i+1) (by simp only [List.length_cons]; omega)
          change Reduce.Within (offset+(i+1)) rest[i] at remaining
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using remaining)
        (by
          intro i member
          have remaining := equations (i+1) (by simp only [List.length_cons]; omega)
          change source.getD (offset+(i+1)) 0=rest[i].run (Function.update environment address value) source at remaining
          simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using remaining)
      simpa only [finish,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using generated

theorem finish_size (needed : List Nat) (address body offset : Nat) (frame : Cone.Frame) (code : List Node) :
    (finish needed address body offset frame code).code.size+Cone.kept needed offset code=frame.code.size+code.length := by
  induction code generalizing offset frame with
  | nil => simp [finish,Cone.kept]
  | cons node rest ih =>
      have tail := ih (offset+1) (step needed address body offset frame node)
      cases selected : Cone.has offset needed <;> simp only [finish,Cone.kept,selected,step,if_false,if_true,
        Bool.false_eq_true,Array.size_push,List.length_cons] at tail ⊢ <;> omega

def focus (code : Array Node) (root : Fin code.size) : Program := ⟨code,root,root⟩

def body (code : Array Node) (forward : Reduce.Forward code) (root : Fin code.size) : Fragment :=
  let front := Cone.compact (focus code root)
  let generated := Cone.compact_represents (focus code root) forward (fun _ => false)
  ⟨front.code,⟨front.mapping.getD root.val 0,
    (generated.2.2 root.val (Cone.marked_roots (focus code root)).1 (by simp [focus])).1⟩⟩

theorem body_read (code : Array Node) (forward : Reduce.Forward code) (root : Fin code.size) (environment : Nat → Bool) :
    (body code forward root).eval environment=(run environment code).getD root.val 0 := by
  exact (Cone.compact_represents (focus code root) forward environment).2.2 root.val
    (Cone.marked_roots (focus code root)).1 (by simp [focus]) |>.2

def rebuild (code : Array Node) (root : Fin code.size) (address : Nat) : Cone.Frame :=
  let front := Cone.compact (focus code root)
  finish (Cone.marked (focus code root)) address (front.mapping.getD root.val 0) 0 front code.toList

theorem rebuild_size (code : Array Node) (root : Fin code.size) (address : Nat) :
    (rebuild code root address).code.size=code.size := by
  have kept := Cone.fold_code_size (Cone.marked (focus code root)) Cone.empty code.toList
  have after := finish_size (Cone.marked (focus code root)) address
    ((Cone.compact (focus code root)).mapping.getD root.val 0) 0 (Cone.compact (focus code root)) code.toList
  change (Cone.compact (focus code root)).code.size=0+Cone.kept (Cone.marked (focus code root)) 0 code.toList at kept
  simp only [rebuild,Array.length_toList] at after ⊢
  omega

theorem rebuild_reads (code : Array Node) (forward : Reduce.Forward code) (root : Fin code.size) (address : Nat)
    (free : FunctionalSubstitution.Free address (body code forward root).code) (environment : Nat → Bool) :
    Reduce.Forward (rebuild code root address).code ∧
      ∀ i, i < code.size → (rebuild code root address).mapping.getD i 0 < (rebuild code root address).code.size ∧
        (run environment (rebuild code root address).code).getD ((rebuild code root address).mapping.getD i 0) 0=
          (run (FunctionalSubstitution.bind address (body code forward root) environment) code).getD i 0 := by
  let front := Cone.compact (focus code root)
  let selected := body code forward root
  let value := truth (selected.eval environment)
  let source := run (Function.update environment address value) code
  have first := Cone.compact_represents (focus code root) forward (Function.update environment address value)
  have prefixFree : FunctionalSubstitution.Free address front.code := free
  have same := FunctionalSubstitution.run_free_update address front.code prefixFree environment value
  have firstReads : ∀ i, i < source.size → i ∈ Cone.marked (focus code root) →
      front.mapping.getD i 0 < front.code.size ∧
        (run environment front.code).getD (front.mapping.getD i 0) 0=source.getD i 0 := by
    intro i bounded member
    have generated := first.2.2 i member bounded
    rw [same] at generated
    exact generated
  have bodyBound : front.mapping.getD root.val 0 < front.code.size := selected.output.isLt
  have initial : Ready (Cone.marked (focus code root)) 0 (front.mapping.getD root.val 0) environment value source front := by
    refine ⟨first.1,first.2.1,bodyBound,rfl,?_⟩
    intro i bounded retained
    exact firstReads i bounded (retained.resolve_right (by omega))
  have final := finish_ready (Cone.marked (focus code root)) address (front.mapping.getD root.val 0) 0 front code.toList
    environment value source initial (by simp [source])
    (by intro i bound; simpa only [Nat.zero_add,Array.getElem_toList] using forward i (by simpa using bound))
    (by
      intro i bound
      have bounded : i < code.size := by simpa using bound
      have law := run_equation code forward (Function.update environment address value) i bounded
      change source.getD i 0=(code.getD i (.constant 0)).run (Function.update environment address value) source at law
      have lookup : code.getD i (.constant 0)=code[i] := by simp [Array.getD,bounded]
      rw [lookup] at law
      simpa only [Nat.zero_add,Array.getElem_toList] using law)
  refine ⟨final.1,?_⟩
  intro i bounded
  exact final.2.2.2.2 i (by simpa only [source,run_size] using bounded) (Or.inr (by simpa using bounded))

structure Arena where
  private mk ::
  code : Array Node
  forward : Reduce.Forward code

structure Loaded where
  private mk ::
  arena : Arena
  mapping : Array Nat
  bounded : ∀ i, mapping.getD i 0 < arena.code.size

def load (code : Array Node) : Loaded :=
  let generated := Reduce.compact code
  ⟨⟨generated.state.code,Reduce.compact_forward code⟩,generated.mapping,
    (Reduce.compact_represents code (fun _ => false)).2.2.2.1⟩

def Loaded.ref (loaded : Loaded) (original : Nat) : Fin loaded.arena.code.size :=
  ⟨loaded.mapping.getD original 0,loaded.bounded original⟩

theorem load_read (code : Array Node) (original : Nat) (environment : Nat → Bool) :
    (run environment (load code).arena.code).getD ((load code).ref original).val 0=(run environment code).getD original 0 :=
  Reduce.compact_reads code environment original

structure Action (original : Arena) where
  private mk ::
  arena : Arena
  mapping : Array Nat
  performed : Bool
  bounded : ∀ i, i < original.code.size → mapping.getD i 0 < arena.code.size

def Action.ref {arena : Arena} (action : Action arena) (original : Fin arena.code.size) : Fin action.arena.code.size :=
  ⟨action.mapping.getD original.val 0,action.bounded original.val original.isLt⟩

def actualBody (arena : Arena) (root : Fin arena.code.size) : Fragment := body arena.code arena.forward root

theorem actualBody_size (arena : Arena) (root : Fin arena.code.size) :
    (actualBody arena root).code.size ≤ arena.code.size := Cone.trim_size_le (focus arena.code root) arena.forward

def apply (arena : Arena) (address : Nat) (root : Fin arena.code.size) : Action arena :=
  let selected := actualBody arena root
  if free : address ∉ FunctionalSubstitution.inputs selected.code then
    let produced := rebuild arena.code root address
    let certified := rebuild_reads arena.code arena.forward root address
      ((FunctionalSubstitution.free_iff _ _).mpr free) (fun _ => false)
    ⟨⟨produced.code,certified.1⟩,produced.mapping,true,fun i bound => (certified.2 i bound).1⟩
  else
    ⟨arena,(List.range arena.code.size).toArray,false,by
      intro i bounded
      simp [Array.getD,bounded]⟩

theorem apply_size (arena : Arena) (address : Nat) (root : Fin arena.code.size) :
    (apply arena address root).arena.code.size=arena.code.size := by
  dsimp only [apply]
  split
  · exact rebuild_size arena.code root address
  · rfl

theorem apply_performed (arena : Arena) (address : Nat) (root : Fin arena.code.size) :
    (apply arena address root).performed=true ↔ address ∉ FunctionalSubstitution.inputs (actualBody arena root).code := by
  dsimp only [apply]
  split <;> simp_all

theorem apply_free (arena : Arena) (address : Nat) (root : Fin arena.code.size)
    (performed : (apply arena address root).performed=true) :
    FunctionalSubstitution.Free address (apply arena address root).arena.code := by
  have free := (apply_performed arena address root).mp performed
  simp only [apply,dif_pos free]
  exact finish_free _ address _ _ _ _ ((FunctionalSubstitution.free_iff _ _).mpr free)

def Action.environment (arena : Arena) (address : Nat) (root : Fin arena.code.size) (environment : Nat → Bool) : Nat → Bool :=
  if (apply arena address root).performed then FunctionalSubstitution.bind address (actualBody arena root) environment else environment

theorem apply_read (arena : Arena) (address : Nat) (root original : Fin arena.code.size) (environment : Nat → Bool) :
    (run environment (apply arena address root).arena.code).getD ((apply arena address root).ref original).val 0=
      (run (Action.environment arena address root environment) arena.code).getD original.val 0 := by
  by_cases free : address ∉ FunctionalSubstitution.inputs (actualBody arena root).code
  · simp only [Action.environment,apply,dif_pos free,Action.ref,if_true]
    exact (rebuild_reads arena.code arena.forward root address ((FunctionalSubstitution.free_iff _ _).mpr free)
      environment).2 original.val original.isLt |>.2
  · simp [Action.environment,apply,free,Action.ref,Array.getD,original.isLt]

structure View (arena : Arena) where
  weight : Fin arena.code.size
  phase : Fin arena.code.size

def View.program {arena : Arena} (view : View arena) : Program := ⟨arena.code,view.weight,view.phase⟩

def Action.view {arena : Arena} (action : Action arena) (view : View arena) : View action.arena :=
  ⟨action.ref view.weight,action.ref view.phase⟩

theorem apply_view (arena : Arena) (address : Nat) (root : Fin arena.code.size) (view : View arena) (environment : Nat → Bool) :
    ((apply arena address root).view view).program.eval environment=
      view.program.eval (Action.environment arena address root environment) := by
  exact congrArg₂ (fun weight phase => weight*sign phase)
    (apply_read arena address root view.weight environment) (apply_read arena address root view.phase environment)

structure Relation (arena : Arena) where
  left : Fin arena.code.size
  right : Fin arena.code.size

def Relation.read {arena : Arena} (relation : Relation arena) (environment : Nat → Bool) : Bool :=
  truth ((run environment arena.code).getD relation.left.val 0)==truth ((run environment arena.code).getD relation.right.val 0)

def Action.relation {arena : Arena} (action : Action arena) (relation : Relation arena) : Relation action.arena :=
  ⟨action.ref relation.left,action.ref relation.right⟩

theorem apply_relation (arena : Arena) (address : Nat) (root : Fin arena.code.size) (relation : Relation arena) (environment : Nat → Bool) :
    ((apply arena address root).relation relation).read environment=relation.read (Action.environment arena address root environment) := by
  exact congrArg₂ (fun left right : ℤ => truth left==truth right)
    (apply_read arena address root relation.left environment) (apply_read arena address root relation.right environment)

end SaturationMonoid.ComplexityProjection.SATSource.ArenaAction

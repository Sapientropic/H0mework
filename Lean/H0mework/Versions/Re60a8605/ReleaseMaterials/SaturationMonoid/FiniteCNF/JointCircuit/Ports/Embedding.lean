import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.RelationCost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.PortEmbedding
open InterferenceProgram

def ref (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (i : Nat) : Fin state.arena.code.size :=
  roots.getD i state.program.weight

def read (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (point : Nat → Bool) : Nat → Bool :=
  fun i => truth ((run point state.arena.code).getD (ref state roots i).val 0)

/-- New inputs denote the already generated gate ports, not fresh source bits. -/
def embed (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) : Node → Node
  | .input i => .band (ref state roots i).val (ref state roots i).val
  | node => node.shift state.arena.code.size

def code (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) : Array Node :=
  state.arena.code++body.code.map (embed state roots)

theorem node_read (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (point : Nat → Bool)
    (values : Array ℤ) (node : Node) :
    (embed state roots node).run point (run point state.arena.code++values)=node.run (read state roots point) values := by
  cases node <;> simp only [embed]
  case input i =>
    have root := getD_append_left (run point state.arena.code) values (ref state roots i).val
      (by simpa only [run_size] using (ref state roots i).isLt)
    simp only [Node.run,root,Bool.and_self,read]
  all_goals
    rw [← run_size point state.arena.code,Node.run_shift]
    rfl

theorem runCode_read (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (point : Nat → Bool)
    (values : Array ℤ) (body : List Node) :
    runCode point (run point state.arena.code++values) (body.map (embed state roots))=
      run point state.arena.code++runCode (read state roots point) values body := by
  induction body generalizing values with
  | nil => rfl
  | cons node rest ih =>
      simp only [List.map_cons,runCode,node_read,push_append]
      exact ih _

theorem run_read (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (point : Nat → Bool) (body : Fragment) :
    run point (code state roots body)=run point state.arena.code++run (read state roots point) body.code := by
  simp only [code,run,Array.toList_append,Array.toList_map,runCode_append]
  simpa only [Array.append_empty,run] using runCode_read state roots point #[] body.code.toList

theorem old_read (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (point : Nat → Bool)
    (body : Fragment) (i : Fin state.arena.code.size) :
    (run point (code state roots body)).getD i.val 0=(run point state.arena.code).getD i.val 0 := by
  rw [run_read]
  exact getD_append_left _ _ _ (by simpa only [run_size] using i.isLt)

theorem body_read (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (point : Nat → Bool) (body : Fragment) :
    (run point (code state roots body)).getD (state.arena.code.size+body.output.val) 0=body.eval (read state roots point) := by
  rw [run_read,← run_size point state.arena.code,getD_append_right]
  rfl

theorem code_size (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) :
    (code state roots body).size=state.arena.code.size+body.code.size := by simp only [code,Array.size_append,Array.size_map]

theorem embed_input (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (node : Node) :
    FunctionalSubstitution.inputOf (embed state roots node)=none := by cases node <;> rfl

/-- This is the direct input inventory. Dependency of a new root on an old
input is still checked through the actual ancestor cone before any binding. -/
theorem code_inputs (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) :
    FunctionalSubstitution.inputs (code state roots body)=FunctionalSubstitution.inputs state.arena.code := by
  have empty : body.code.toList.filterMap (fun node => FunctionalSubstitution.inputOf (embed state roots node))=[] := by
    simp [embed_input]
  simp only [FunctionalSubstitution.inputs,code,Array.toList_append,Array.toList_map,List.filterMap_append,List.filterMap_map,Function.comp_def,empty,List.append_nil]


structure Emission (original : ArenaSource.State) where
  target : ArenaSource.State
  mapping : Array Nat
  bounded : ∀ i, mapping.getD i 0 < target.arena.code.size
  root : Fin target.arena.code.size

def Emission.ref {original : ArenaSource.State} (output : Emission original) (i : Fin original.arena.code.size) :
    Fin output.target.arena.code.size := ⟨output.mapping.getD i.val 0,output.bounded i.val⟩

def append (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) : Emission state :=
  let generated := code state roots body
  let loaded := ArenaAction.load generated
  let target := ArenaSource.reload state generated 0
  ⟨target,loaded.mapping,loaded.bounded,loaded.ref (state.arena.code.size+body.output.val)⟩

theorem append_old (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment)
    (point : Nat → Bool) (i : Fin state.arena.code.size) :
    (run point (append state roots body).target.arena.code).getD ((append state roots body).ref i).val 0=
      (run point state.arena.code).getD i.val 0 := by
  exact (ArenaAction.load_read (code state roots body) i.val point).trans (old_read state roots point body i)

theorem append_root (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) (point : Nat → Bool) :
    (run point (append state roots body).target.arena.code).getD (append state roots body).root.val 0=body.eval (read state roots point) :=
  (ArenaAction.load_read (code state roots body) (state.arena.code.size+body.output.val) point).trans (body_read state roots point body)

theorem append_program (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) (point : Nat → Bool) :
    (append state roots body).target.program.program.eval point=state.program.program.eval point := by
  simp only [append,ArenaSource.reload_program,Nat.zero_add,old_read]
  rfl

theorem append_relations (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) (point : Nat → Bool) :
    ArenaSource.readRelations (append state roots body).target point=ArenaSource.readRelations state point := by
  change ArenaSource.readRelations (ArenaSource.reload state (code state roots body) 0) point=_
  rw [ArenaSource.reload_relations]
  simp only [Nat.zero_add,old_read,ArenaSource.readRelations,ArenaAction.Relation.read]

theorem append_read (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) (point : Nat → Bool) :
    JointCircuit.read (append state roots body).target point=JointCircuit.read state point := by
  simp only [JointCircuit.read,append_program,append_relations]

theorem append_count (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) :
    (append state roots body).target.relations.length=state.relations.length := ArenaSource.reload_count _ _ _

theorem append_size (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) :
    (append state roots body).target.arena.code.size ≤ state.arena.code.size+body.code.size+1 := by
  have bound := ArenaSource.reload_size state (code state roots body) 0
  rwa [code_size] at bound

theorem append_inputs (state : ArenaSource.State) (roots : Array (Fin state.arena.code.size)) (body : Fragment) :
    FunctionalSubstitution.inputs (append state roots body).target.arena.code ⊆ FunctionalSubstitution.inputs state.arena.code := by
  intro i member
  by_contra absent
  have free := (FunctionalSubstitution.free_iff (code state roots body) i).mpr (by rw [code_inputs]; exact absent)
  have kept := JointRelationUpdate.load_free i (code state roots body) free
  exact FunctionalSubstitution.inputs_free _ i kept member

structure Frame where
  state : ArenaSource.State
  ports : Array (Fin state.arena.code.size)

def initial (state : ArenaSource.State) : Frame := ⟨state,Array.ofFn id⟩

def Frame.read (frame : Frame) (point : Nat → Bool) : Nat → Bool := PortEmbedding.read frame.state frame.ports point

def extend (frame : Frame) (body : Fragment) : Frame :=
  let produced := append frame.state frame.ports body
  ⟨produced.target,frame.ports.map produced.ref⟩

theorem extend_size (frame : Frame) (body : Fragment) : (extend frame body).ports.size=frame.ports.size := by
  simp only [extend,Array.size_map]

theorem extend_read (frame : Frame) (body : Fragment) (point : Nat → Bool) (i : Nat) (inside : i < frame.ports.size) :
    (extend frame body).read point i=frame.read point i := by
  simp only [Frame.read,read,ref,extend]
  have first : (frame.ports.map (append frame.state frame.ports body).ref).getD i (append frame.state frame.ports body).target.program.weight=
      (append frame.state frame.ports body).ref (frame.ports.getD i frame.state.program.weight) := by
    simp [Array.getD,inside]
  rw [first,append_old]


theorem initial_size (state : ArenaSource.State) : (initial state).ports.size=state.arena.code.size := by
  simp only [initial,Array.size_ofFn]

def bind (frame : Frame) (address : Nat) (root : Fin frame.state.arena.code.size) : Frame :=
  let action := ArenaAction.apply frame.state.arena address root
  let target := ArenaSource.next frame.state address root
  ⟨target,frame.ports.map action.ref⟩

theorem bind_size (frame : Frame) (address : Nat) (root : Fin frame.state.arena.code.size) :
    (bind frame address root).ports.size=frame.ports.size := by
  change (frame.ports.map (ArenaAction.apply frame.state.arena address root).ref).size=frame.ports.size
  exact Array.size_map

theorem bind_read (frame : Frame) (address : Nat) (root : Fin frame.state.arena.code.size) (point : Nat → Bool)
    (i : Nat) (inside : i < frame.ports.size) :
    (bind frame address root).read point i=
      frame.read (ArenaAction.Action.environment frame.state.arena address root point) i := by
  let action := ArenaAction.apply frame.state.arena address root
  change truth ((run point action.arena.code).getD
    ((frame.ports.map action.ref).getD i (action.ref frame.state.program.weight)).val 0)=
      truth ((run (ArenaAction.Action.environment frame.state.arena address root point) frame.state.arena.code).getD
        (frame.ports.getD i frame.state.program.weight).val 0)
  have mapped : (frame.ports.map action.ref).getD i (action.ref frame.state.program.weight)=
      action.ref (frame.ports.getD i frame.state.program.weight) := by simp [Array.getD,inside]
  rw [mapped]
  exact congrArg truth (ArenaAction.apply_read frame.state.arena address root (frame.ports.getD i frame.state.program.weight) point)

end SaturationMonoid.ComplexityProjection.SATSource.PortEmbedding

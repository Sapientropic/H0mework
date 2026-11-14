import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Core

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductBatch
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)

def node (frame : Frame) (pair : Nat × Nat) : Node :=
  .band (PortEmbedding.ref frame.state frame.ports pair.1).val (PortEmbedding.ref frame.state frame.ports pair.2).val

def product (frame : Frame) (point : Nat → Bool) (pair : Nat × Nat) : ℤ :=
  bit (frame.read point pair.1 && frame.read point pair.2)

theorem node_read (frame : Frame) (point : Nat → Bool) (values : Array ℤ) (pair : Nat × Nat) :
    (node frame pair).run point (run point frame.state.arena.code++values)=product frame point pair := by
  have left := getD_append_left (run point frame.state.arena.code) values
    (PortEmbedding.ref frame.state frame.ports pair.1).val (by simpa only [run_size] using (PortEmbedding.ref frame.state frame.ports pair.1).isLt)
  have right := getD_append_left (run point frame.state.arena.code) values
    (PortEmbedding.ref frame.state frame.ports pair.2).val (by simpa only [run_size] using (PortEmbedding.ref frame.state frame.ports pair.2).isLt)
  simp only [node,Node.run,left,right,product,PortEmbedding.Frame.read,PortEmbedding.read]

def values (frame : Frame) (point : Nat → Bool) (pairs : List (Nat × Nat)) : Array ℤ :=
  (pairs.map (product frame point)).toArray

theorem runCode_read (frame : Frame) (point : Nat → Bool) (extra : Array ℤ) (pairs : List (Nat × Nat)) :
    runCode point (run point frame.state.arena.code++extra) (pairs.map (node frame))=
      run point frame.state.arena.code++(extra++values frame point pairs) := by
  induction pairs generalizing extra with
  | nil => simp [runCode,values]
  | cons pair rest ih =>
      simp only [List.map_cons,runCode,node_read,push_append,ih]
      congr 1
      apply Array.toList_inj.mp
      simp [values]

def code (frame : Frame) : Array Node :=
  frame.state.arena.code++((ProductSource.pairs frame.ports.size).map (node frame)).toArray

theorem code_size (frame : Frame) : (code frame).size=frame.state.arena.code.size+frame.ports.size*frame.ports.size := by
  simp only [code,Array.size_append,List.size_toArray,List.length_map,ProductSource.pairs_length]

theorem code_read (frame : Frame) (point : Nat → Bool) :
    run point (code frame)=run point frame.state.arena.code++values frame point (ProductSource.pairs frame.ports.size) := by
  simp only [code,run,Array.toList_append,runCode_append]
  have equality := runCode_read frame point #[] (ProductSource.pairs frame.ports.size)
  simpa only [Array.append_empty,Array.empty_append,run] using equality

theorem code_old (frame : Frame) (point : Nat → Bool) (root : Fin frame.state.arena.code.size) :
    (run point (code frame)).getD root.val 0=(run point frame.state.arena.code).getD root.val 0 := by
  rw [code_read]
  exact getD_append_left _ _ _ (by simpa only [run_size] using root.isLt)

theorem code_product (frame : Frame) (point : Nat → Bool) (k : Nat) (inside : k < (ProductSource.pairs frame.ports.size).length) :
    (run point (code frame)).getD (frame.state.arena.code.size+k) 0=
      product frame point (ProductSource.pairs frame.ports.size)[k] := by
  rw [code_read]
  have lookup := getD_append_right (run point frame.state.arena.code) (values frame point (ProductSource.pairs frame.ports.size)) k
  simp only [run_size] at lookup
  rw [lookup]
  simp [values,Array.getD,inside]

def generate (frame : Frame) : Frame :=
  let loaded := ArenaAction.load (code frame)
  let target := ArenaSource.reload frame.state (code frame) 0
  let ref : Nat → Fin target.arena.code.size := fun raw => ⟨loaded.mapping.getD raw 0,loaded.bounded raw⟩
  ⟨target,(frame.ports.map (fun old => ref old.val))++
    Array.ofFn (fun i : Fin (ProductSource.pairs frame.ports.size).length => ref (frame.state.arena.code.size+i.val))⟩

theorem generate_state (frame : Frame) : (generate frame).state=ArenaSource.reload frame.state (code frame) 0 := by
  rfl

theorem generate_ports (frame : Frame) : (generate frame).ports.size=frame.ports.size+frame.ports.size*frame.ports.size := by
  simp only [generate,Array.size_append,Array.size_map,Array.size_ofFn,ProductSource.pairs_length]

theorem generate_size (frame : Frame) :
    (generate frame).state.arena.code.size ≤ frame.state.arena.code.size+frame.ports.size*frame.ports.size+1 := by
  have bound := ArenaSource.reload_size frame.state (code frame) 0
  rw [generate_state]
  rwa [code_size] at bound

theorem generate_read (frame : Frame) (point : Nat → Bool) :
    JointCircuit.read (generate frame).state point=JointCircuit.read frame.state point := by
  rw [generate_state]
  have program := ArenaSource.reload_program frame.state (code frame) 0 point
  have relations := ArenaSource.reload_relations frame.state (code frame) 0 point
  simp only [Nat.zero_add,code_old] at program relations
  change (truth ((ArenaSource.reload frame.state (code frame) 0).program.program.eval point) &&
    ArenaSource.readRelations (ArenaSource.reload frame.state (code frame) 0) point)=_
  rw [program,relations]
  rfl

theorem generate_program (frame : Frame) (point : Nat → Bool) :
    (generate frame).state.program.program.eval point=frame.state.program.program.eval point := by
  rw [generate_state,ArenaSource.reload_program]
  simp only [Nat.zero_add,code_old]
  rfl

theorem generate_relations (frame : Frame) (point : Nat → Bool) :
    ArenaSource.readRelations (generate frame).state point=ArenaSource.readRelations frame.state point := by
  rw [generate_state,ArenaSource.reload_relations]
  simp only [Nat.zero_add,code_old,ArenaSource.readRelations,ArenaAction.Relation.read]

theorem generate_count (frame : Frame) : (generate frame).state.relations.length=frame.state.relations.length := by
  rw [generate_state,ArenaSource.reload_count]

theorem generate_valid (frame : Frame) (valid : ArenaSource.Valid frame.state) : ArenaSource.Valid (generate frame).state := by
  intro point accepted
  rw [generate_program] at accepted
  exact (generate_relations frame point).trans (valid point accepted)

theorem generate_old (frame : Frame) (point : Nat → Bool) (i : Nat) (inside : i < frame.ports.size) :
    (generate frame).read point i=frame.read point i := by
  let loaded := ArenaAction.load (code frame)
  have source : (generate frame).ports.getD i (generate frame).state.program.weight=
      loaded.ref (PortEmbedding.ref frame.state frame.ports i).val := by
    simp [generate,PortEmbedding.ref,loaded,Array.getD,inside,ArenaAction.Loaded.ref,
      show i < frame.ports.size+(ProductSource.pairs frame.ports.size).length by omega]
    apply Fin.ext
    rfl
  change truth ((run point loaded.arena.code).getD ((generate frame).ports.getD i (generate frame).state.program.weight).val 0)=_
  rw [source,ArenaAction.load_read,code_old]
  rfl

theorem generate_product (frame : Frame) (point : Nat → Bool) (i j : Nat)
    (hi : i < frame.ports.size) (hj : j < frame.ports.size) :
    (generate frame).read point (ProductSource.index frame i j)=(frame.read point i && frame.read point j) := by
  let pairs := ProductSource.pairs frame.ports.size
  let k := pairs.idxOf (i,j)
  have member := (ProductSource.pairs_mem frame.ports.size i j).mpr ⟨hi,hj⟩
  have inside : k < pairs.length := List.idxOf_lt_length_of_mem member
  change k < (ProductSource.pairs frame.ports.size).length at inside
  let loaded := ArenaAction.load (code frame)
  have source : (generate frame).ports.getD (frame.ports.size+k) (generate frame).state.program.weight=
      loaded.ref (frame.state.arena.code.size+k) := by
    simp [generate,loaded,Array.getD,inside,ArenaAction.Loaded.ref]
    apply Fin.ext
    rfl
  change truth ((run point loaded.arena.code).getD
    ((generate frame).ports.getD (frame.ports.size+k) (generate frame).state.program.weight).val 0)=_
  rw [source,ArenaAction.load_read,code_product frame point k inside]
  simp only [product,show (ProductSource.pairs frame.ports.size)[k]=(i,j) from List.getElem_idxOf inside,truth_bit]

end SaturationMonoid.ComplexityProjection.SATSource.ProductBatch

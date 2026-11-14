import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Arena.Cost.Primitives

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ArenaCost
open InterferenceProgram

def has (index : Nat) (indices : List Nat) : Counted Bool :=
  let result := AffineClauseProduct.Cost.member index indices
  ⟨result.value,result.visits⟩

theorem has_value (index : Nat) (indices : List Nat) : (has index indices).value=Cone.has index indices := by
  apply Bool.eq_iff_iff.mpr
  simp only [has,AffineClauseProduct.Cost.member_value,decide_eq_true_eq,Cone.has_true_iff]

theorem has_cells (index : Nat) (indices : List Nat) : (has index indices).cells ≤ 2*indices.length+1 :=
  AffineClauseProduct.Cost.member_visits index indices

namespace Dependency

def add (index : Nat) (indices : List Nat) : Counted (List Nat) :=
  let found := has index indices
  let output := if found.value then indices else index::indices
  ⟨output,found.cells+2*output.length+4⟩

theorem add_value (index : Nat) (indices : List Nat) : (add index indices).value=Cone.addIndex index indices := by
  simp only [add,has_value,Cone.addIndex]

theorem add_cells (index : Nat) (indices : List Nat) : (add index indices).cells ≤ 4*indices.length+7 := by
  have first := has_cells index indices
  have length := Cone.addIndex_length index indices
  rw [← add_value] at length
  simp only [add] at length ⊢
  omega

def pull (index : Nat) : List Nat → List Nat → Counted (List Nat)
  | [],needed => ⟨needed,2*needed.length+1⟩
  | ref::refs,needed =>
      let first := if ref < index then add ref needed else ⟨needed,2⟩
      let tail := pull index refs first.value
      ⟨tail.value,first.cells+tail.cells+2*tail.value.length+6⟩

theorem pull_value (index : Nat) (refs needed : List Nat) : (pull index refs needed).value=Cone.pullRefs index refs needed := by
  induction refs generalizing needed with
  | nil => rfl
  | cons ref refs ih =>
      simp only [pull,ih,Cone.pullRefs]
      split <;> simp only [add_value]

theorem pull_length (index : Nat) (refs needed : List Nat) :
    (pull index refs needed).value.length ≤ needed.length+refs.length := by
  induction refs generalizing needed with
  | nil => simp [pull]
  | cons ref refs ih =>
      have longer := Cone.addIndex_length ref needed
      rw [← add_value] at longer
      simp only [pull,List.length_cons]
      split
      · have tail := ih (add ref needed).value
        omega
      · have tail := ih needed
        exact tail.trans (by omega)

theorem pull_cells (index : Nat) (refs needed : List Nat) :
    (pull index refs needed).cells ≤ (refs.length+1)*(8*(needed.length+refs.length)+16) := by
  induction refs generalizing needed with
  | nil => simp [pull]; omega
  | cons ref refs ih =>
      simp only [pull,List.length_cons]
      split
      · have first := add_cells ref needed
        have growth := Cone.addIndex_length ref needed
        rw [← add_value] at growth
        have tail := ih (add ref needed).value
        have length := pull_length index refs (add ref needed).value
        have later := tail.trans (Nat.mul_le_mul_left (refs.length+1)
          (show 8*((add ref needed).value.length+refs.length)+16 ≤
            8*(needed.length+(refs.length+1))+16 by omega))
        nlinarith only [first,growth,length,later]
      · have tail := ih needed
        have length := pull_length index refs needed
        nlinarith only [tail,length]

def mark (offset : Nat) : List Node → List Nat → Counted (List Nat)
  | [],roots => ⟨roots,2*roots.length+1⟩
  | node::rest,roots =>
      let later := mark (offset+1) rest roots
      let found := has offset later.value
      let current := if found.value then pull offset node.refs later.value else ⟨later.value,2*later.value.length+1⟩
      ⟨current.value,later.cells+found.cells+current.cells+2*current.value.length+12⟩

theorem mark_value (offset : Nat) (code : List Node) (roots : List Nat) :
    (mark offset code roots).value=Cone.markFrom offset code roots := by
  induction code generalizing offset with
  | nil => rfl
  | cons node rest ih =>
      simp only [mark,ih,has_value,Cone.markFrom,Cone.pull]
      split <;> simp only [pull_value]

theorem mark_length (offset : Nat) (code : List Node) (roots : List Nat) :
    (mark offset code roots).value.length ≤ roots.length+3*code.length := by
  rw [mark_value]
  exact Cone.mark_length offset code roots

theorem mark_cells (offset : Nat) (code : List Node) (roots : List Nat) :
    (mark offset code roots).cells ≤ (code.length+1)*(200*(roots.length+3*code.length+4)) := by
  induction code generalizing offset with
  | nil => simp [mark]; omega
  | cons node rest ih =>
      have earlier := ih (offset+1)
      have nodes := mark_length (offset+1) rest roots
      have found := has_cells offset (mark (offset+1) rest roots).value
      have refs := Cone.refs_length node
      have pulled := pull_cells offset node.refs (mark (offset+1) rest roots).value
      have output := pull_length offset node.refs (mark (offset+1) rest roots).value
      have pullBound := pulled.trans (Nat.mul_le_mul (by omega : node.refs.length+1 ≤ 4)
        (show 8*((mark (offset+1) rest roots).value.length+node.refs.length)+16 ≤
          8*(roots.length+3*rest.length+3)+16 by omega))
      simp only [mark,List.length_cons]
      split
      · nlinarith only [earlier,nodes,found,refs,output,pullBound]
      · nlinarith only [earlier,nodes,found]

def size (frame : Cone.Frame) : Nat := frame.code.size+frame.mapping.size+1

def emit (needed : List Nat) (frame : Cone.Frame) (node : Node) : Counted Cone.Frame :=
  let found := has frame.mapping.size needed
  if found.value then
    let translated := mapRefs frame.mapping node
    let output : Cone.Frame := ⟨frame.code.push translated.value,frame.mapping.push frame.code.size⟩
    ⟨output,found.cells+translated.cells+8*size output+8⟩
  else
    let output : Cone.Frame := ⟨frame.code,frame.mapping.push 0⟩
    ⟨output,found.cells+8*size output+8⟩

theorem emit_value (needed : List Nat) (frame : Cone.Frame) (node : Node) :
    (emit needed frame node).value=Cone.emit needed frame node := by
  simp only [emit,has_value,Cone.emit]
  split <;> simp only [mapRefs_value]

theorem emit_size (needed : List Nat) (frame : Cone.Frame) (node : Node) :
    size (emit needed frame node).value ≤ size frame+2 := by
  simp only [emit_value,Cone.emit]
  split <;> simp only [size,Array.size_push] <;> omega

theorem emit_cells (needed : List Nat) (frame : Cone.Frame) (node : Node) :
    (emit needed frame node).cells ≤ 20*size frame+2*needed.length+50 := by
  have first := has_cells frame.mapping.size needed
  have translated := mapRefs_cells frame.mapping node
  simp only [emit]
  split <;> simp only [size,Array.size_push] <;> omega

def fold (needed : List Nat) : Cone.Frame → List Node → Counted Cone.Frame
  | frame,[] => ⟨frame,8*size frame+1⟩
  | frame,node::rest =>
      let first := emit needed frame node
      let tail := fold needed first.value rest
      ⟨tail.value,first.cells+tail.cells+8*size tail.value+8⟩

theorem fold_value (needed : List Nat) (frame : Cone.Frame) (code : List Node) :
    (fold needed frame code).value=Cone.fold needed frame code := by
  induction code generalizing frame <;> simp_all [fold,Cone.fold,emit_value]

theorem fold_size (needed : List Nat) (frame : Cone.Frame) (code : List Node) :
    size (fold needed frame code).value ≤ size frame+2*code.length := by
  induction code generalizing frame with
  | nil => simp [fold]
  | cons node rest ih =>
      have first := emit_size needed frame node
      have later := ih (emit needed frame node).value
      simp only [fold,List.length_cons]
      omega

theorem fold_cells (needed : List Nat) (frame : Cone.Frame) (code : List Node) :
    (fold needed frame code).cells ≤ (code.length+1)*(50*(size frame+2*code.length+needed.length+1)+50) := by
  induction code generalizing frame with
  | nil => simp only [fold,List.length_nil,Nat.zero_add,Nat.mul_zero,Nat.add_zero,Nat.one_mul]; omega
  | cons node rest ih =>
      have first := emit_cells needed frame node
      have growth := emit_size needed frame node
      have later := ih (emit needed frame node).value
      have output := fold_size needed (emit needed frame node).value rest
      have tail := later.trans (Nat.mul_le_mul_left (rest.length+1)
        (show 50*(size (emit needed frame node).value+2*rest.length+needed.length+1)+50 ≤
          50*(size frame+2*(rest.length+1)+needed.length+1)+50 by omega))
      simp only [fold,List.length_cons]
      nlinarith only [first,growth,output,tail]

def compact (program : Program) : Counted Cone.Frame :=
  let needed := mark 0 program.code.toList (Cone.roots program)
  let output := fold needed.value Cone.empty program.code.toList
  ⟨output.value,needed.cells+output.cells+8*(program.code.size+size output.value)+2*needed.value.length+16⟩

theorem compact_value (program : Program) : (compact program).value=Cone.compact program := by
  simp only [compact,fold_value,mark_value,Cone.compact]

theorem compact_size (program : Program) : size (compact program).value ≤ 2*program.code.size+1 := by
  have size := fold_size (mark 0 program.code.toList (Cone.roots program)).value Cone.empty program.code.toList
  simpa only [compact,Dependency.size,Cone.empty,Array.size_empty,Nat.zero_add,Array.length_toList,Nat.add_comm] using size

def budget (nodes : Nat) : Nat := (nodes+2)*(1200*nodes+2400)

theorem compact_cells (program : Program) : (compact program).cells ≤ budget program.code.size := by
  have marked := mark_cells 0 program.code.toList (Cone.roots program)
  have needed := mark_length 0 program.code.toList (Cone.roots program)
  have copied := fold_cells (mark 0 program.code.toList (Cone.roots program)).value Cone.empty program.code.toList
  have output := fold_size (mark 0 program.code.toList (Cone.roots program)).value Cone.empty program.code.toList
  have emptySize : size Cone.empty=1 := rfl
  have rootsSize : (Cone.roots program).length=2 := rfl
  simp only [Array.length_toList,emptySize,rootsSize] at marked needed copied output
  have copyBound := copied.trans (Nat.mul_le_mul_left (program.code.size+1)
    (show 50*(1+2*program.code.size+(mark 0 program.code.toList (Cone.roots program)).value.length+1)+50 ≤
      50*(1+2*program.code.size+(2+3*program.code.size)+1)+50 by omega))
  simp only [compact,budget]
  nlinarith only [marked,needed,output,copyBound]

end Dependency

namespace Rewiring

def rewrite (address body : Nat) (mapping : Array Nat) (node : Node) : Counted Node :=
  match node with
  | .input i => ⟨if i=address then .band body body else .input i,16⟩
  | node => let output := mapRefs mapping node; ⟨output.value,output.cells+8⟩

theorem rewrite_value (address body : Nat) (mapping : Array Nat) (node : Node) :
    (rewrite address body mapping node).value=ArenaAction.rewrite address body mapping node := by
  cases node <;> simp only [rewrite,ArenaAction.rewrite,mapRefs_value]

theorem rewrite_cells (address body : Nat) (mapping : Array Nat) (node : Node) :
    (rewrite address body mapping node).cells ≤ 6*mapping.size+28 := by
  have cost := mapRefs_cells mapping node
  cases node <;> simp only [rewrite] <;> omega

def step (needed : List Nat) (address body index : Nat) (frame : Cone.Frame) (node : Node) : Counted Cone.Frame :=
  let found := has index needed
  if found.value then ⟨frame,found.cells+8*Dependency.size frame+8⟩ else
    let translated := rewrite address body frame.mapping node
    let output : Cone.Frame := ⟨frame.code.push translated.value,ArenaAction.mapPut frame.mapping index frame.code.size⟩
    ⟨output,found.cells+translated.cells+2*frame.mapping.size+8*Dependency.size output+12⟩

theorem step_value (needed : List Nat) (address body index : Nat) (frame : Cone.Frame) (node : Node) :
    (step needed address body index frame node).value=ArenaAction.step needed address body index frame node := by
  simp only [step,has_value,ArenaAction.step]
  split <;> simp only [rewrite_value]

theorem step_size (needed : List Nat) (address body index : Nat) (frame : Cone.Frame) (node : Node) :
    Dependency.size (step needed address body index frame node).value ≤ Dependency.size frame+1 := by
  simp only [step_value,ArenaAction.step]
  split <;> simp only [Dependency.size,Array.size_push,ArenaAction.mapPut_size] <;> omega

theorem step_cells (needed : List Nat) (address body index : Nat) (frame : Cone.Frame) (node : Node) :
    (step needed address body index frame node).cells ≤ 40*Dependency.size frame+2*needed.length+60 := by
  have found := has_cells index needed
  have translated := rewrite_cells address body frame.mapping node
  simp only [step]
  split <;> simp only [Dependency.size,Array.size_push,ArenaAction.mapPut_size] <;> omega

def finish (needed : List Nat) (address body : Nat) : Nat → Cone.Frame → List Node → Counted Cone.Frame
  | _,frame,[] => ⟨frame,8*Dependency.size frame+1⟩
  | index,frame,node::rest =>
      let first := step needed address body index frame node
      let tail := finish needed address body (index+1) first.value rest
      ⟨tail.value,first.cells+tail.cells+8*Dependency.size tail.value+8⟩

theorem finish_value (needed : List Nat) (address body offset : Nat) (frame : Cone.Frame) (code : List Node) :
    (finish needed address body offset frame code).value=ArenaAction.finish needed address body offset frame code := by
  induction code generalizing offset frame <;> simp_all [finish,ArenaAction.finish,step_value]

theorem finish_size (needed : List Nat) (address body offset : Nat) (frame : Cone.Frame) (code : List Node) :
    Dependency.size (finish needed address body offset frame code).value ≤ Dependency.size frame+code.length := by
  induction code generalizing offset frame with
  | nil => simp [finish]
  | cons node rest ih =>
      have first := step_size needed address body offset frame node
      have tail := ih (offset+1) (step needed address body offset frame node).value
      simp only [finish,List.length_cons]
      omega

theorem finish_cells (needed : List Nat) (address body offset : Nat) (frame : Cone.Frame) (code : List Node) :
    (finish needed address body offset frame code).cells ≤
      (code.length+1)*(100*(Dependency.size frame+code.length+needed.length+1)+100) := by
  induction code generalizing offset frame with
  | nil => simp only [finish,List.length_nil,Nat.zero_add,Nat.add_zero,Nat.one_mul]; omega
  | cons node rest ih =>
      have first := step_cells needed address body offset frame node
      have growth := step_size needed address body offset frame node
      have later := ih (offset+1) (step needed address body offset frame node).value
      have output := finish_size needed address body (offset+1) (step needed address body offset frame node).value rest
      have tail := later.trans (Nat.mul_le_mul_left (rest.length+1)
        (show 100*(Dependency.size (step needed address body offset frame node).value+rest.length+needed.length+1)+100 ≤
          100*(Dependency.size frame+(rest.length+1)+needed.length+1)+100 by omega))
      simp only [finish,List.length_cons]
      nlinarith only [first,growth,output,tail]

def rebuild (code : Array Node) (root : Fin code.size) (address : Nat) : Counted Cone.Frame :=
  let program := ArenaAction.focus code root
  let front := Dependency.compact program
  let needed := Dependency.mark 0 code.toList (Cone.roots program)
  let body := lookup front.value.mapping root.val
  let output := finish needed.value address body.value 0 front.value code.toList
  ⟨output.value,front.cells+needed.cells+body.cells+output.cells+
    8*(code.size+Dependency.size output.value)+2*needed.value.length+32⟩

theorem rebuild_value (code : Array Node) (root : Fin code.size) (address : Nat) :
    (rebuild code root address).value=ArenaAction.rebuild code root address := by
  simp only [rebuild,Dependency.compact_value,Dependency.mark_value,lookup,finish_value,
    ArenaAction.rebuild,Cone.marked]
  rfl

def budget (nodes : Nat) : Nat := (nodes+2)*(5000*nodes+10000)

theorem rebuild_cells (code : Array Node) (root : Fin code.size) (address : Nat) :
    (rebuild code root address).cells ≤ budget code.size := by
  let program := ArenaAction.focus code root
  let front := Dependency.compact program
  let needed := Dependency.mark 0 code.toList (Cone.roots program)
  have first := Dependency.compact_cells program
  have frontSize := Dependency.compact_size program
  have marked := Dependency.mark_cells 0 code.toList (Cone.roots program)
  have neededSize := Dependency.mark_length 0 code.toList (Cone.roots program)
  have done := finish_cells needed.value address (lookup front.value.mapping root.val).value 0 front.value code.toList
  have output := finish_size needed.value address (lookup front.value.mapping root.val).value 0 front.value code.toList
  have rootsSize : (Cone.roots program).length=2 := rfl
  have nodeSize : program.code.size=code.size := rfl
  simp only [nodeSize,rootsSize,Array.length_toList] at first frontSize marked neededSize done output
  change Dependency.size front.value ≤ 2*code.size+1 at frontSize
  change needed.value.length ≤ 2+3*code.size at neededSize
  have last := done.trans (Nat.mul_le_mul_left (code.size+1)
    (show 100*(Dependency.size front.value+code.size+needed.value.length+1)+100 ≤
      100*((2*code.size+1)+code.size+(2+3*code.size)+1)+100 by omega))
  have mappingSize : front.value.mapping.size ≤ 2*code.size+1 := by
    unfold Dependency.size at frontSize
    omega
  change front.cells+needed.cells+(lookup front.value.mapping root.val).cells+
    (finish needed.value address (lookup front.value.mapping root.val).value 0 front.value code.toList).cells+
    8*(code.size+Dependency.size (finish needed.value address (lookup front.value.mapping root.val).value 0 front.value code.toList).value)+
    2*needed.value.length+32 ≤ _
  change front.cells ≤ Dependency.budget code.size at first
  change needed.cells ≤ _ at marked
  simp only [lookup] at last output
  simp only [lookup,budget,Dependency.budget] at first ⊢
  nlinarith only [first,marked,frontSize,neededSize,last,output,mappingSize]

end Rewiring
end SaturationMonoid.ComplexityProjection.SATSource.ArenaCost

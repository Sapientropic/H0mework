import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Arena.Source

/-! Source-record execution. A node has at most three reference fields. Array
reads include a full address scan, updates and returned payloads include copies.
Nat/Int field arithmetic and counter arithmetic are separate bit-level work. -/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ArenaCost
open InterferenceProgram
abbrev Counted := CapacityMatching.SourceCost.Counted

def lookup (mapping : Array Nat) (index : Nat) : Counted Nat :=
  ⟨mapping.getD index 0,2*mapping.size+4⟩

def mapRefs (mapping : Array Nat) (node : Node) : Counted Node :=
  ⟨node.mapRefs (fun i => (lookup mapping i).value),
    (node.refs.map (fun i => (lookup mapping i).cells)).sum+8⟩

theorem mapRefs_value (mapping : Array Nat) (node : Node) :
    (mapRefs mapping node).value=node.mapRefs (fun i => mapping.getD i 0) := rfl

theorem mapRefs_cells (mapping : Array Nat) (node : Node) :
    (mapRefs mapping node).cells ≤ 6*mapping.size+20 := by
  cases node <;> simp [mapRefs,lookup,Node.refs] <;> omega

def shifts (offset : Nat) : List Node → Counted (List Node)
  | [] => ⟨[],1⟩
  | node::rest => let tail := shifts offset rest
      ⟨node.shift offset::tail.value,tail.cells+8*tail.value.length+16⟩

theorem shifts_value (offset : Nat) (code : List Node) : (shifts offset code).value=code.map (Node.shift offset) := by
  induction code <;> simp_all [shifts]

theorem shifts_cells (offset : Nat) (code : List Node) :
    (shifts offset code).cells ≤ code.length*(8*code.length+16)+1 := by
  induction code with
  | nil => simp [shifts]
  | cons node rest ih =>
      simp only [shifts,shifts_value,List.length_map,List.length_cons]
      nlinarith

def inputs (code : Array Node) : Counted (List Nat) :=
  let found := FunctionalSchedule.Cost.occurrences code.toList
  let result := AffineClauseProduct.Cost.unique found.value
  ⟨result.value,found.visits+result.visits+8*code.size+2*result.value.length+8⟩

theorem inputs_value (code : Array Node) : (inputs code).value=FunctionalSubstitution.inputs code := by
  simp only [inputs,AffineClauseProduct.Cost.unique_value,FunctionalSchedule.Cost.occurrences_value,
    FunctionalSubstitution.inputs]

theorem inputs_length (code : Array Node) : (inputs code).value.length ≤ code.size := by
  have first := FunctionalSchedule.Cost.occurrences_length code.toList
  have last := AffineClauseProduct.Cost.unique_length (FunctionalSchedule.Cost.occurrences code.toList).value
  simp only [Array.length_toList] at first
  exact last.trans first

def inputsBudget (size : Nat) : Nat := 4*size*size+25*size+10

theorem inputs_cells (code : Array Node) : (inputs code).cells ≤ inputsBudget code.size := by
  have first := FunctionalSchedule.Cost.occurrences_visits code.toList
  have length := FunctionalSchedule.Cost.occurrences_length code.toList
  have last := AffineClauseProduct.Cost.unique_visits (FunctionalSchedule.Cost.occurrences code.toList).value
  have output := inputs_length code
  simp only [Array.length_toList] at first length
  have square := Nat.mul_self_le_mul_self length
  simp only [inputs,inputsBudget] at output ⊢
  nlinarith

namespace Reduction

def size (frame : Reduce.Frame) : Nat := frame.state.code.size+frame.state.table.length+frame.mapping.size+1

def search (node : Node) : List Reduce.Entry → Counted (Option Nat)
  | [] => ⟨none,1⟩
  | item::rest => if item.node=node then ⟨some item.output,12⟩ else
      let tail := search node rest
      ⟨tail.value,tail.cells+12⟩

theorem search_value (node : Node) (table : List Reduce.Entry) : (search node table).value=Reduce.search node table := by
  induction table with
  | nil => rfl
  | cons item rest ih => simp only [search,Reduce.search]; split <;> simp_all

theorem search_cells (node : Node) (table : List Reduce.Entry) :
    (search node table).cells ≤ 12*table.length+1 := by
  induction table with
  | nil => rfl
  | cons item rest ih => simp only [search,List.length_cons]; split <;> simp only <;> omega

def intern (state : Reduce.State) (node : Node) : Counted (Reduce.State × Nat) :=
  let found := search node state.table
  let output := match found.value with
    | some index => (state,index)
    | none => (Reduce.append state node,state.code.size)
  ⟨output,found.cells+8*(output.1.code.size+output.1.table.length+1)+16⟩

theorem intern_value (state : Reduce.State) (node : Node) :
    (intern state node).value=Reduce.intern state node := by
  simp only [intern,search_value,Reduce.intern]
  rfl

theorem intern_cells (state : Reduce.State) (node : Node) :
    (intern state node).cells ≤ 8*state.code.size+20*state.table.length+41 := by
  have first := search_cells node state.table
  have sizes := Reduce.intern_sizes state node
  simp only [intern,search_value] at *
  change (Reduce.intern state node).1.code.size ≤ _ ∧ _ at sizes
  change (search node state.table).cells+8*((Reduce.intern state node).1.code.size+
    (Reduce.intern state node).1.table.length+1)+16 ≤ _
  omega

def emit (frame : Reduce.Frame) (node : Node) : Counted Reduce.Frame :=
  let translated := mapRefs frame.mapping node
  let added := intern frame.state translated.value
  let output : Reduce.Frame := ⟨added.value.1,frame.mapping.push added.value.2⟩
  ⟨output,translated.cells+added.cells+2*(frame.mapping.size+1)+8*size output+8⟩

theorem emit_value (frame : Reduce.Frame) (node : Node) : (emit frame node).value=Reduce.emit frame node := by
  simp only [emit,mapRefs_value,intern_value,Reduce.emit]

theorem emit_size (frame : Reduce.Frame) (node : Node) : size (emit frame node).value ≤ size frame+3 := by
  have growth := Reduce.intern_sizes frame.state (node.mapRefs (fun i => frame.mapping.getD i 0))
  simp only [emit_value,Reduce.emit,size,Array.size_push]
  omega

theorem emit_cells (frame : Reduce.Frame) (node : Node) : (emit frame node).cells ≤ 80*size frame+80 := by
  have translated := mapRefs_cells frame.mapping node
  have added := intern_cells frame.state (mapRefs frame.mapping node).value
  have output := emit_size frame node
  simp only [emit] at output ⊢
  unfold size at output ⊢
  omega

def fold : Reduce.Frame → List Node → Counted Reduce.Frame
  | frame,[] => ⟨frame,8*size frame+1⟩
  | frame,node::rest =>
      let first := emit frame node
      let tail := fold first.value rest
      ⟨tail.value,first.cells+tail.cells+8*size tail.value+8⟩

theorem fold_value (frame : Reduce.Frame) (code : List Node) : (fold frame code).value=Reduce.fold frame code := by
  induction code generalizing frame <;> simp_all [fold,Reduce.fold,emit_value]

theorem fold_size (frame : Reduce.Frame) (code : List Node) : size (fold frame code).value ≤ size frame+3*code.length := by
  induction code generalizing frame with
  | nil => simp [fold]
  | cons node rest ih =>
      have growth := emit_size frame node
      have later := ih (emit frame node).value
      simp only [fold,List.length_cons]
      omega

theorem fold_cells (frame : Reduce.Frame) (code : List Node) :
    (fold frame code).cells ≤ (code.length+1)*(100*(size frame+3*code.length)+100) := by
  induction code generalizing frame with
  | nil => simp only [fold,List.length_nil,Nat.zero_add,Nat.mul_zero,Nat.add_zero,Nat.one_mul]; omega
  | cons node rest ih =>
      have first := emit_cells frame node
      have growth := emit_size frame node
      have tail := ih (emit frame node).value
      have output := fold_size (emit frame node).value rest
      have tailBound := tail.trans (Nat.mul_le_mul_left (rest.length+1)
        (show 100*(size (emit frame node).value+3*rest.length)+100 ≤
          100*(size frame+3*(rest.length+1))+100 by omega))
      simp only [fold,List.length_cons]
      nlinarith only [first,growth,output,tailBound]

def compact (code : Array Node) : Counted Reduce.Frame :=
  let output := fold Reduce.first code.toList
  ⟨output.value,output.cells+8*(code.size+size output.value)+10⟩

theorem compact_value (code : Array Node) : (compact code).value=Reduce.compact code := by
  simp only [compact,fold_value,Reduce.compact]

def budget (nodes : Nat) : Nat := (nodes+2)*(400*nodes+500)

theorem compact_cells (code : Array Node) : (compact code).cells ≤ budget code.size := by
  have work := fold_cells Reduce.first code.toList
  have storage := fold_size Reduce.first code.toList
  have initial : size Reduce.first=3 := rfl
  simp only [Array.length_toList,initial] at work storage
  simp only [compact,budget]
  nlinarith

end Reduction
end SaturationMonoid.ComplexityProjection.SATSource.ArenaCost

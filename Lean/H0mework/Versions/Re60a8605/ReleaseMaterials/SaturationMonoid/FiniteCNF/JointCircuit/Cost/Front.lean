import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Iteration

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointCircuitCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
abbrev Counted := ArenaCost.Counted

def storage {n : Nat} (formula : CNFFormula n) : Nat := 3*Extract.literalCount formula+2*formula.length

theorem storage_append {n : Nat} (left right : CNFFormula n) :
    storage (left++right)=storage left+storage right := by
  simp only [storage,Extract.literalCount,List.map_append,List.sum_append,List.length_append]
  omega

theorem storage_measures {n : Nat} (formula : CNFFormula n) :
    formula.length ≤ storage formula ∧ Extract.literalCount formula ≤ storage formula := by
  unfold storage
  omega

theorem storage_clause {n : Nat} (formula : CNFFormula n)
    (bounded : ∀ clause ∈ formula, clause.length ≤ 3) : storage formula ≤ 11*formula.length := by
  induction formula with
  | nil => simp [storage,Extract.literalCount]
  | cons clause rest ih =>
      have first := bounded clause (by simp)
      have tail := ih (fun other member => bounded other (by simp [member]))
      simp only [storage,Extract.literalCount,List.map_cons,List.sum_cons,List.length_cons] at *
      omega

theorem gate_storage {n : Nat} (output : Fin n) (ref : Nat → Fin n) (node : Node) :
    storage (JointCircuit.gate output ref node) ≤ 44 := by
  have shape := storage_clause (JointCircuit.gate output ref node) (JointCircuit.gate_clause output ref node)
  have count := JointCircuit.gate_length output ref node
  omega

def append {n : Nat} (left right : CNFFormula n) : Counted (CNFFormula n) :=
  ⟨left++right,2*storage left+2*storage right+5⟩

def gather {α : Type} {n : Nat} (act : α → Counted (CNFFormula n)) : List α → Counted (CNFFormula n)
  | [] => ⟨[],1⟩
  | item::rest =>
      let first := act item
      let tail := gather act rest
      let joined := append first.value tail.value
      ⟨joined.value,first.cells+tail.cells+joined.cells⟩

theorem gather_value {α : Type} {n : Nat} (act : α → Counted (CNFFormula n)) (items : List α) :
    (gather act items).value=items.flatMap (fun item => (act item).value) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [gather,append,List.flatMap_cons,ih]

theorem gather_storage {α : Type} {n : Nat} (act : α → Counted (CNFFormula n)) (items : List α)
    (size : Nat) (bounded : ∀ item ∈ items, storage (act item).value ≤ size) :
    storage (gather act items).value ≤ items.length*size := by
  induction items with
  | nil => simp [gather,storage,Extract.literalCount]
  | cons item rest ih =>
      have first := bounded item (by simp)
      have tail := ih (fun other member => bounded other (by simp [member]))
      simp only [gather,append,storage_append,List.length_cons]
      nlinarith

def gatherBudget (length work size : Nat) : Nat := length*(work+(length+1)*size+5)+1

theorem gather_cells {α : Type} {n : Nat} (act : α → Counted (CNFFormula n)) (items : List α)
    (work size : Nat) (paid : ∀ item ∈ items, (act item).cells ≤ work)
    (bounded : ∀ item ∈ items, storage (act item).value ≤ size) :
    (gather act items).cells ≤ gatherBudget items.length work size := by
  induction items with
  | nil => simp [gather,gatherBudget]
  | cons item rest ih =>
      have first := paid item (by simp)
      have space := bounded item (by simp)
      have tailSpace := gather_storage act rest size (fun other member => bounded other (by simp [member]))
      have tail := ih (fun other member => paid other (by simp [member]))
        (fun other member => bounded other (by simp [member]))
      simp only [gather,append,List.length_cons,gatherBudget] at *
      nlinarith

def emitGate (state : ArenaSource.State) (i : Fin state.arena.code.size) : Counted (CNFFormula state.arena.code.size) :=
  let block := JointCircuit.gate i (JointCircuit.slot state) (JointCircuit.node state i)
  ⟨block,16*state.arena.code.size+80+2*storage block⟩

theorem emitGate_cells (state : ArenaSource.State) (i : Fin state.arena.code.size) :
    (emitGate state i).cells ≤ 16*state.arena.code.size+168 := by
  have bound := gate_storage i (JointCircuit.slot state) (JointCircuit.node state i)
  simp only [emitGate]
  omega

def emitAlias (state : ArenaSource.State) (i j : Fin state.arena.code.size) : Counted (CNFFormula state.arena.code.size) :=
  let block := if JointCircuit.sameInput state i j then JointCircuit.equal i j else []
  ⟨block,24*state.arena.code.size+100+2*storage block⟩

theorem emitAlias_storage (state : ArenaSource.State) (i j : Fin state.arena.code.size) :
    storage (emitAlias state i j).value ≤ 44 := by
  unfold emitAlias
  split
  · exact gate_storage i (fun _ => j) (.neg 0)
  · simp [storage,Extract.literalCount]

theorem emitAlias_cells (state : ArenaSource.State) (i j : Fin state.arena.code.size) :
    (emitAlias state i j).cells ≤ 24*state.arena.code.size+188 := by
  have bound := emitAlias_storage state i j
  change 24*state.arena.code.size+100+2*storage (emitAlias state i j).value ≤ _
  omega

def aliasRow (state : ArenaSource.State) (i : Fin state.arena.code.size) : Counted (CNFFormula state.arena.code.size) :=
  let output := gather (emitAlias state i) (List.finRange state.arena.code.size)
  ⟨output.value,output.cells+8*state.arena.code.size+8⟩

def aliasRowBudget (nodes : Nat) : Nat := gatherBudget nodes (24*nodes+188) 44+8*nodes+8

theorem aliasRow_storage (state : ArenaSource.State) (i : Fin state.arena.code.size) :
    storage (aliasRow state i).value ≤ state.arena.code.size*44 := by
  simpa only [aliasRow,List.length_finRange] using
    gather_storage (emitAlias state i) (List.finRange state.arena.code.size) 44
      (fun j _ => emitAlias_storage state i j)

theorem aliasRow_cells (state : ArenaSource.State) (i : Fin state.arena.code.size) :
    (aliasRow state i).cells ≤ aliasRowBudget state.arena.code.size := by
  have work := gather_cells (emitAlias state i) (List.finRange state.arena.code.size)
    (24*state.arena.code.size+188) 44 (fun j _ => emitAlias_cells state i j) (fun j _ => emitAlias_storage state i j)
  simpa only [aliasRow,aliasRowBudget,List.length_finRange,Nat.add_assoc] using
    Nat.add_le_add_right work (8*state.arena.code.size+8)

def emitRelation (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena) : Counted (CNFFormula state.arena.code.size) :=
  let block := JointCircuit.equal item.relation.left item.relation.right
  ⟨block,72+2*storage block⟩

theorem emitRelation_storage (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena) :
    storage (emitRelation state item).value ≤ 44 :=
  gate_storage item.relation.left (fun _ => item.relation.right) (.neg 0)

theorem emitRelation_cells (state : ArenaSource.State) (item : ArenaSource.Labeled state.arena) :
    (emitRelation state item).cells ≤ 160 := by
  have bound := emitRelation_storage state item
  change 72+2*storage (emitRelation state item).value ≤ _
  omega

def formula (state : ArenaSource.State) : Counted (CNFFormula state.arena.code.size) :=
  let gates := gather (emitGate state) (List.finRange state.arena.code.size)
  let aliases := gather (aliasRow state) (List.finRange state.arena.code.size)
  let relations := gather (emitRelation state) state.relations
  let first := append gates.value aliases.value
  let second := append first.value relations.value
  let third := append second.value (JointCircuit.unit state.program.weight true)
  ⟨third.value,gates.cells+aliases.cells+relations.cells+first.cells+second.cells+third.cells+
    32*(state.arena.code.size+state.relations.length+1)+32⟩

theorem formula_value (state : ArenaSource.State) : (formula state).value=JointCircuit.formula state := by
  simp only [formula,append,gather_value,emitGate,aliasRow,emitAlias,emitRelation,
    JointCircuit.formula,JointCircuit.gates,JointCircuit.aliases,JointCircuit.relations]

def formulaStorage (nodes count : Nat) : Nat := 44*nodes+44*nodes*nodes+44*count+5

theorem formula_storage (state : ArenaSource.State) :
    storage (formula state).value ≤ formulaStorage state.arena.code.size state.relations.length := by
  have a := gather_storage (emitGate state) (List.finRange state.arena.code.size) 44
    (fun i _ => gate_storage i (JointCircuit.slot state) (JointCircuit.node state i))
  have b := gather_storage (aliasRow state) (List.finRange state.arena.code.size) (state.arena.code.size*44)
    (fun i _ => aliasRow_storage state i)
  have c := gather_storage (emitRelation state) state.relations 44 (fun item _ => emitRelation_storage state item)
  simp only [List.length_finRange] at a b
  have task : storage (JointCircuit.unit state.program.weight true)=5 := by simp [storage,JointCircuit.unit,Extract.literalCount]
  simp only [formula,append,storage_append,task,formulaStorage]
  nlinarith

def formulaBudget (nodes count : Nat) : Nat :=
  gatherBudget nodes (16*nodes+168) 44+
    gatherBudget nodes (aliasRowBudget nodes) (nodes*44)+gatherBudget count 160 44+
    1024*(nodes*nodes+nodes+count+1)

theorem formula_cells (state : ArenaSource.State) :
    (formula state).cells ≤ formulaBudget state.arena.code.size state.relations.length := by
  have a := gather_cells (emitGate state) (List.finRange state.arena.code.size) (16*state.arena.code.size+168) 44
    (fun i _ => emitGate_cells state i) (fun i _ => gate_storage i (JointCircuit.slot state) (JointCircuit.node state i))
  have b := gather_cells (aliasRow state) (List.finRange state.arena.code.size) (aliasRowBudget state.arena.code.size)
    (state.arena.code.size*44) (fun i _ => aliasRow_cells state i) (fun i _ => aliasRow_storage state i)
  have c := gather_cells (emitRelation state) state.relations 160 44
    (fun item _ => emitRelation_cells state item) (fun item _ => emitRelation_storage state item)
  have sa := gather_storage (emitGate state) (List.finRange state.arena.code.size) 44
    (fun i _ => gate_storage i (JointCircuit.slot state) (JointCircuit.node state i))
  have sb := gather_storage (aliasRow state) (List.finRange state.arena.code.size) (state.arena.code.size*44)
    (fun i _ => aliasRow_storage state i)
  have sc := gather_storage (emitRelation state) state.relations 44 (fun item _ => emitRelation_storage state item)
  simp only [List.length_finRange] at a b sa sb
  have task : storage (JointCircuit.unit state.program.weight true)=5 := by simp [storage,JointCircuit.unit,Extract.literalCount]
  simp only [formula,append,storage_append,task,formulaBudget]
  nlinarith

def checked : List Node → Counted Bool
  | [] => ⟨true,1⟩
  | head::rest => if JointCircuit.allowed head then
      let tail := checked rest
      ⟨tail.value,tail.cells+4⟩
    else ⟨false,4⟩

theorem checked_value (code : List Node) : (checked code).value=code.all JointCircuit.allowed := by
  induction code with
  | nil => rfl
  | cons head rest ih => simp only [checked,List.all_cons]; split <;> simp_all

theorem checked_cells (code : List Node) : (checked code).cells ≤ 4*code.length+1 := by
  induction code with
  | nil => simp [checked]
  | cons head rest ih => simp only [checked,List.length_cons]; split <;> simp only <;> omega

end SaturationMonoid.ComplexityProjection.SATSource.JointCircuitCost

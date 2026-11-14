import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Relations

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open CapacityMatching.RowCost (rowCells rowsCells rowsCells_cons rowsCells_nil)
abbrev Counted := ArenaCost.Counted

def pairsFrom (right : List Nat) : List Nat → Counted (List (Nat × Nat))
  | [] => ⟨[],1⟩
  | i::rest =>
      let first := right.map (fun j => (i,j))
      let tail := pairsFrom right rest
      ⟨first++tail.value,tail.cells+16*(right.length+tail.value.length+1)+16⟩

theorem pairsFrom_value (right left : List Nat) : (pairsFrom right left).value=left.product right := by
  induction left <;> simp_all only [pairsFrom,List.product,List.flatMap_nil,List.flatMap_cons]

theorem pairsFrom_length (right left : List Nat) : (pairsFrom right left).value.length=left.length*right.length := by
  rw [pairsFrom_value]
  simp [List.product,List.length_flatMap]

def pairsBudget (p : Nat) : Nat := p*(16*(p+p*p+1)+16)+16*p+17

theorem pairsFrom_cells (right left : List Nat) :
    (pairsFrom right left).cells ≤ left.length*(16*(right.length+left.length*right.length+1)+16)+1 := by
  induction left with
  | nil => simp [pairsFrom]
  | cons i rest ih => simp only [pairsFrom,pairsFrom_length,List.length_cons]; nlinarith

def pairs (p : Nat) : Counted (List (Nat × Nat)) :=
  let output := pairsFrom (List.range p) (List.range p)
  ⟨output.value,output.cells+16*p+16⟩

theorem pairs_value (p : Nat) : (pairs p).value=ProductSource.pairs p := by simp only [pairs,pairsFrom_value,ProductSource.pairs]

theorem pairs_cells (p : Nat) : (pairs p).cells ≤ pairsBudget p := by
  have source := pairsFrom_cells (List.range p) (List.range p)
  simp only [List.length_range] at source
  simp only [pairs,pairsBudget]
  omega

def find (pair : Nat × Nat) : List (Nat × Nat) → Counted Nat
  | [] => ⟨0,1⟩
  | other::rest => if other=pair then ⟨0,8⟩ else
      let tail := find pair rest
      ⟨tail.value+1,tail.cells+8⟩

theorem find_value (pair : Nat × Nat) (source : List (Nat × Nat)) : (find pair source).value=source.idxOf pair := by
  induction source with
  | nil => rfl
  | cons other rest ih =>
      by_cases same : other=pair <;> simp [find,same,ih]

theorem find_cells (pair : Nat × Nat) (source : List (Nat × Nat)) : (find pair source).cells ≤ 8*source.length+1 := by
  induction source with
  | nil => rfl
  | cons other rest ih => simp only [find,List.length_cons]; split <;> simp only <;> omega

def index (frame : Frame) (i j : Nat) : Counted Nat :=
  let source := pairs frame.ports.size
  let found := find (i,j) source.value
  ⟨frame.ports.size+found.value,source.cells+found.cells+8*source.value.length+16⟩

theorem index_value (frame : Frame) (i j : Nat) : (index frame i j).value=ProductSource.index frame i j := by
  simp only [index,pairs_value,find_value,ProductSource.index]

def indexBudget (p : Nat) : Nat := pairsBudget p+16*p*p+17

theorem index_cells (frame : Frame) (i j : Nat) : (index frame i j).cells ≤ indexBudget frame.ports.size := by
  have source := pairs_cells frame.ports.size
  have found := find_cells (i,j) (pairs frame.ports.size).value
  have count : (pairs frame.ports.size).value.length=frame.ports.size*frame.ports.size := by rw [pairs_value,ProductSource.pairs_length]
  simp only [index,indexBudget,count] at found ⊢
  nlinarith

def nodes (frame : Frame) : List (Nat × Nat) → Counted (List Node)
  | [] => ⟨[],1⟩
  | pair::rest =>
      let tail := nodes frame rest
      ⟨ProductBatch.node frame pair::tail.value,tail.cells+16*(frame.ports.size+tail.value.length+1)+24⟩

theorem nodes_value (frame : Frame) (source : List (Nat × Nat)) : (nodes frame source).value=source.map (ProductBatch.node frame) := by
  induction source <;> simp_all only [nodes,List.map_nil,List.map_cons]

theorem nodes_cells (frame : Frame) (source : List (Nat × Nat)) :
    (nodes frame source).cells ≤ source.length*(16*(frame.ports.size+source.length+1)+24)+1 := by
  induction source with
  | nil => simp [nodes]
  | cons pair rest ih => simp only [nodes,nodes_value,List.length_map,List.length_cons]; nlinarith

def code (frame : Frame) : Counted (Array Node) :=
  let source := pairs frame.ports.size
  let generated := nodes frame source.value
  ⟨frame.state.arena.code++generated.value.toArray,source.cells+generated.cells+
    16*(frame.state.arena.code.size+source.value.length+generated.value.length+1)+24⟩

theorem code_value (frame : Frame) : (code frame).value=ProductBatch.code frame := by
  simp only [code,pairs_value,nodes_value,ProductBatch.code]

def codeBudget (n p : Nat) : Nat := pairsBudget p+p*p*(16*(p+p*p+1)+24)+1+16*(n+2*p*p+1)+24

theorem code_cells (frame : Frame) : (code frame).cells ≤ codeBudget frame.state.arena.code.size frame.ports.size := by
  have source := pairs_cells frame.ports.size
  have generated := nodes_cells frame (pairs frame.ports.size).value
  have size : (pairs frame.ports.size).value.length=frame.ports.size*frame.ports.size := by rw [pairs_value,ProductSource.pairs_length]
  rw [size] at generated
  simp only [code,nodes_value,List.length_map,size,codeBudget]
  nlinarith

def expand (frame : Frame) : Counted Frame :=
  let source := code frame
  let loaded := ArenaCost.Reduction.compact source.value
  let roots := frame.ports.toList.map Fin.val++(List.range (frame.ports.size*frame.ports.size)).map (frame.state.arena.code.size+·)
  let moved := PortCost.movePorts loaded.value.mapping roots
  let relations := ArenaCost.remap loaded.value.mapping (ArenaCost.rawRelations frame.state)
  let weight := ArenaCost.lookup loaded.value.mapping frame.state.program.weight.val
  let phase := ArenaCost.lookup loaded.value.mapping frame.state.program.phase.val
  ⟨ProductBatch.generate frame,4*(source.cells+loaded.cells+moved.cells+relations.cells+weight.cells+phase.cells)+
    64*(frame.state.arena.code.size+frame.ports.size+frame.ports.size*frame.ports.size+frame.state.relations.length+1)+64⟩

theorem expand_value (frame : Frame) : (expand frame).value=ProductBatch.generate frame := rfl

def expandBudget (n p c : Nat) : Nat :=
  let size := n+p*p
  let count := p+p*p
  4*(codeBudget n p+ArenaCost.Reduction.budget size+count*(2*size+8*count+20)+1+
    c*(4*size+6*c+24)+1+4*size+8)+64*(n+p+p*p+c+1)+64

theorem expand_cells (frame : Frame) : (expand frame).cells ≤ expandBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length := by
  have source := code_cells frame
  have size : (code frame).value.size=frame.state.arena.code.size+frame.ports.size*frame.ports.size := by rw [code_value,ProductBatch.code_size]
  have loaded := ArenaCost.Reduction.compact_cells (code frame).value
  have mapping := ArenaCost.reduction_mapping_size (code frame).value
  rw [size] at loaded mapping
  have moved := PortCost.movePorts_cells (ArenaCost.Reduction.compact (code frame).value).value.mapping
    (frame.ports.toList.map Fin.val++(List.range (frame.ports.size*frame.ports.size)).map (frame.state.arena.code.size+·))
  simp only [List.length_append,List.length_map,Array.length_toList,List.length_range,mapping] at moved
  have relations := ArenaCost.remap_cells (ArenaCost.Reduction.compact (code frame).value).value.mapping (ArenaCost.rawRelations frame.state)
  have count : (ArenaCost.rawRelations frame.state).length=frame.state.relations.length := by simp only [ArenaCost.rawRelations,List.length_map]
  rw [mapping,count] at relations
  simp only [expand,expandBudget,ArenaCost.lookup,mapping]
  omega

def indices (frame : Frame) (i : Nat) : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | j::rest =>
      let mapped := index frame i j
      let tail := indices frame i rest
      ⟨mapped.value::tail.value,mapped.cells+tail.cells+8*tail.value.length+16⟩

theorem indices_value (frame : Frame) (i : Nat) (source : List Nat) : (indices frame i source).value=source.map (ProductSource.index frame i) := by
  induction source <;> simp_all only [indices,index_value,List.map_nil,List.map_cons]

theorem indices_cells (frame : Frame) (i : Nat) (source : List Nat) :
    (indices frame i source).cells ≤ source.length*(indexBudget frame.ports.size+8*source.length+16)+1 := by
  induction source with
  | nil => simp [indices]
  | cons j rest ih =>
      have first := index_cells frame i j
      simp only [indices,indices_value,List.length_map,List.length_cons]
      nlinarith

def multiply (frame : Frame) (i : Nat) (row : Row) : Counted Row :=
  let mapped := indices frame i row.vars
  ⟨⟨mapped.value++if row.rhs then [i] else [],false⟩,mapped.cells+16*(rowCells row+1)+24⟩

theorem multiply_value (frame : Frame) (i : Nat) (row : Row) : (multiply frame i row).value=ProductSource.multiplyRow frame i row := by
  simp only [multiply,indices_value,ProductSource.multiplyRow]

def multiplyBudget (p s : Nat) : Nat := s*(indexBudget p+8*s+16)+1+16*(s+1)+24

theorem multiply_cells (frame : Frame) (i : Nat) (row : Row) : (multiply frame i row).cells ≤ multiplyBudget frame.ports.size (rowCells row) := by
  have source := indices_cells frame i row.vars
  have bound : row.vars.length ≤ rowCells row := by unfold rowCells; omega
  have work := source.trans (show row.vars.length*(indexBudget frame.ports.size+8*row.vars.length+16)+1 ≤
    rowCells row*(indexBudget frame.ports.size+8*rowCells row+16)+1 by gcongr)
  simp only [multiply,multiplyBudget]
  omega

def pairWork (frame : Frame) : List (Nat × Nat) → Counted (List Nat)
  | [] => ⟨[],1⟩
  | pair::rest =>
      let first := index frame pair.1 pair.2
      let tail := pairWork frame rest
      ⟨first.value::tail.value,first.cells+tail.cells+8*rest.length+16⟩

theorem pairWork_cells (frame : Frame) (source : List (Nat × Nat)) :
    (pairWork frame source).cells ≤ source.length*(indexBudget frame.ports.size+8*source.length+16)+1 := by
  induction source with
  | nil => simp [pairWork]
  | cons pair rest ih =>
      have first := index_cells frame pair.1 pair.2
      simp only [pairWork,List.length_cons]
      nlinarith

def requests (output : Nat) : Node → List (Nat × Nat)
  | .mul a b | .band a b => [(a,b),(output,a),(output,b)]
  | .select c a b => [(c,a),(c,b),(c,output)]
  | _ => []

theorem requests_length (output : Nat) (node : Node) : (requests output node).length ≤ 3 := by cases node <;> simp [requests]

def gate (frame : Frame) (output : Nat) (node : Node) : Counted (List Row) :=
  let products := pairWork frame (requests output node)
  let rows := ProductRows.gate frame output node
  ⟨rows,2*products.cells+16*(rowsCells rows+1)+24⟩

theorem gate_value (frame : Frame) (output : Nat) (node : Node) : (gate frame output node).value=ProductRows.gate frame output node := rfl

def gateBudget (p : Nat) : Nat := 2*(3*(indexBudget p+40)+1)+232

theorem gate_cells (frame : Frame) (output : Nat) (node : Node) : (gate frame output node).cells ≤ gateBudget frame.ports.size := by
  have products := pairWork_cells frame (requests output node)
  have length := requests_length output node
  have work : (pairWork frame (requests output node)).cells ≤ 3*(indexBudget frame.ports.size+40)+1 := by
    apply products.trans
    have unit : indexBudget frame.ports.size+8*(requests output node).length+16 ≤ indexBudget frame.ports.size+40 := by omega
    exact Nat.add_le_add_right (Nat.mul_le_mul length unit) 1
  have stored := ProductRows.gate_storage frame output node
  simp only [gate,gateBudget]
  omega

def gates (state : ArenaSource.State) : Counted (List Row) :=
  let generated := CapacityMatching.RowCost.gather (fun i : Fin state.arena.code.size => gate (PortEmbedding.initial state) i.val (JointCircuit.node state i))
    (List.finRange state.arena.code.size)
  ⟨generated.value,generated.cells+16*state.arena.code.size*(state.arena.code.size+1)+16⟩

theorem gates_value (state : ArenaSource.State) : (gates state).value=ProductRows.gates state := by
  simp only [gates,CapacityMatching.RowCost.gather_value,gate_value,ProductRows.gates]

def gatesBudget (n : Nat) : Nat := n*(gateBudget n+(n+1)*12+5)+1+16*n*(n+1)+16

theorem gates_cells (state : ArenaSource.State) : (gates state).cells ≤ gatesBudget state.arena.code.size := by
  have generated := CapacityMatching.RowCost.gather_cells
    (fun i : Fin state.arena.code.size => gate (PortEmbedding.initial state) i.val (JointCircuit.node state i))
    (List.finRange state.arena.code.size) (gateBudget state.arena.code.size) 12
    (fun i _ => by simpa only [PortEmbedding.initial_size] using gate_cells (PortEmbedding.initial state) i.val (JointCircuit.node state i))
    (fun i _ => ProductRows.gate_storage _ _ _)
  simp only [List.length_finRange] at generated
  simp only [gates,gatesBudget]
  omega

def diagonal (frame : Frame) (i : Nat) : Counted (List Row) :=
  let product := index frame i i
  ⟨[⟨[product.value,i],false⟩],product.cells+40⟩

def symmetric (frame : Frame) (pair : Nat × Nat) : Counted (List Row) :=
  let first := index frame pair.1 pair.2
  let second := index frame pair.2 pair.1
  ⟨[⟨[first.value,second.value],false⟩],first.cells+second.cells+48⟩

theorem diagonal_value (frame : Frame) (i : Nat) : (diagonal frame i).value=[ProductRows.diagonal frame i] := by simp only [diagonal,index_value,ProductRows.diagonal]
theorem symmetric_value (frame : Frame) (pair : Nat × Nat) : (symmetric frame pair).value=[ProductRows.symmetric frame pair] := by simp only [symmetric,index_value,ProductRows.symmetric]

def laws (frame : Frame) : Counted (List Row) :=
  let source := pairs frame.ports.size
  let first := CapacityMatching.RowCost.gather (diagonal frame) (List.range frame.ports.size)
  let second := CapacityMatching.RowCost.gather (symmetric frame) source.value
  let output := CapacityMatching.RowCost.append first.value second.value
  ⟨output.value,source.cells+first.cells+second.cells+output.cells+16*(frame.ports.size+source.value.length+1)+24⟩

theorem singleton_flatMap {α β : Type} (items : List α) (f : α → β) : items.flatMap (fun x => [f x])=items.map f := by
  induction items <;> simp_all only [List.flatMap_nil,List.map_nil,List.flatMap_cons,List.singleton_append,List.map_cons]

theorem laws_value (frame : Frame) : (laws frame).value=ProductRows.laws frame := by
  simp only [laws,CapacityMatching.RowCost.append,CapacityMatching.RowCost.gather_value,diagonal_value,symmetric_value,pairs_value,
    singleton_flatMap,ProductRows.laws]

def lawsBudget (p : Nat) : Nat := pairsBudget p+p*(indexBudget p+40+(p+1)*4+5)+1+
  p*p*(2*indexBudget p+48+(p*p+1)*4+5)+1+8*(p+p*p)+5+16*(p+p*p+1)+24

theorem laws_cells (frame : Frame) : (laws frame).cells ≤ lawsBudget frame.ports.size := by
  have source := pairs_cells frame.ports.size
  have count : (pairs frame.ports.size).value.length=frame.ports.size*frame.ports.size := by rw [pairs_value,ProductSource.pairs_length]
  have first := CapacityMatching.RowCost.gather_cells (diagonal frame) (List.range frame.ports.size) (indexBudget frame.ports.size+40) 4
    (fun i _ => by have work := index_cells frame i i; simp only [diagonal]; omega)
    (fun i _ => by simp only [diagonal,rowsCells_cons,rowsCells_nil,rowCells,List.length_cons,List.length_nil]; omega)
  have second := CapacityMatching.RowCost.gather_cells (symmetric frame) (pairs frame.ports.size).value (2*indexBudget frame.ports.size+48) 4
    (fun pair _ => by have a := index_cells frame pair.1 pair.2; have b := index_cells frame pair.2 pair.1; simp only [symmetric]; omega)
    (fun pair _ => by simp only [symmetric,rowsCells_cons,rowsCells_nil,rowCells,List.length_cons,List.length_nil]; omega)
  have firstStored := CapacityMatching.RowCost.gather_storage (diagonal frame) (List.range frame.ports.size) 4
    (fun i _ => by simp only [diagonal,rowsCells_cons,rowsCells_nil,rowCells,List.length_cons,List.length_nil]; omega)
  have secondStored := CapacityMatching.RowCost.gather_storage (symmetric frame) (pairs frame.ports.size).value 4
    (fun pair _ => by simp only [symmetric,rowsCells_cons,rowsCells_nil,rowCells,List.length_cons,List.length_nil]; omega)
  simp only [List.length_range,count] at first second firstStored secondStored
  simp only [laws,CapacityMatching.RowCost.append,count,lawsBudget]
  nlinarith

theorem rows_length (rows : List Row) : rows.length ≤ rowsCells rows := by
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [rowsCells_cons,rowCells,List.length_cons]; omega

theorem row_member (rows : List Row) (row : Row) (member : row ∈ rows) : rowCells row ≤ rowsCells rows := by
  induction rows with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | tail
      · simp only [rowsCells_cons]; omega
      · have size := ih tail; simp only [rowsCells_cons]; omega

def multiplied (frame : Frame) (basis : List Row) : Counted (List Row) :=
  CapacityMatching.RowCost.gather (fun i : Nat =>
    CapacityMatching.RowCost.gather (fun row =>
      let generated := multiply frame i row
      ⟨[generated.value],generated.cells+8*rowCells generated.value+8⟩) basis) (List.range frame.ports.size)

theorem multiplied_value (frame : Frame) (basis : List Row) : (multiplied frame basis).value=ProductSource.rows frame basis := by
  simp only [multiplied,CapacityMatching.RowCost.gather_value,multiply_value,singleton_flatMap,ProductSource.rows]

def multiplyPoolBudget (p s : Nat) : Nat := s*(multiplyBudget p s+8*(s+1)+8+(s+1)*(s+1)+5)+1
def multipliedBudget (p s : Nat) : Nat := p*(multiplyPoolBudget p s+(p+1)*s*(s+1)+5)+1

theorem multiplied_cells (frame : Frame) (basis : List Row) :
    (multiplied frame basis).cells ≤ multipliedBudget frame.ports.size (rowsCells basis) := by
  let s := rowsCells basis
  have length := rows_length basis
  have perIndex (i : Nat) :
      (CapacityMatching.RowCost.gather (fun row => let generated := multiply frame i row
        ⟨[generated.value],generated.cells+8*rowCells generated.value+8⟩) basis).cells ≤ multiplyPoolBudget frame.ports.size s := by
    have gathered := CapacityMatching.RowCost.gather_cells
      (fun row => let generated := multiply frame i row
        (⟨[generated.value],generated.cells+8*rowCells generated.value+8⟩ : Counted (List Row))) basis
      (multiplyBudget frame.ports.size s+8*(s+1)+8) (s+1)
      (fun row member => by
        have size := row_member basis row member
        have created := (multiply_cells frame i row).trans (show multiplyBudget frame.ports.size (rowCells row) ≤ multiplyBudget frame.ports.size s by unfold multiplyBudget; gcongr)
        have output := ProductRows.multiply_storage frame i row
        simp only [multiply_value]
        omega)
      (fun row member => by
        have size := row_member basis row member
        have output := ProductRows.multiply_storage frame i row
        simp only [multiply_value,rowsCells_cons,rowsCells_nil]
        omega)
    apply gathered.trans
    unfold multiplyPoolBudget
    gcongr
  have perStorage (i : Nat) : rowsCells
      (CapacityMatching.RowCost.gather (fun row => let generated := multiply frame i row
        ⟨[generated.value],generated.cells+8*rowCells generated.value+8⟩) basis).value ≤ s*(s+1) := by
    have gathered := CapacityMatching.RowCost.gather_storage
      (fun row => let generated := multiply frame i row
        (⟨[generated.value],generated.cells+8*rowCells generated.value+8⟩ : Counted (List Row))) basis (s+1)
      (fun row member => by
        have size := row_member basis row member
        have output := ProductRows.multiply_storage frame i row
        simp only [multiply_value,rowsCells_cons,rowsCells_nil]
        omega)
    exact gathered.trans (Nat.mul_le_mul_right _ length)
  have output := CapacityMatching.RowCost.gather_cells _ (List.range frame.ports.size)
    (multiplyPoolBudget frame.ports.size s) (s*(s+1)) (fun i _ => perIndex i) (fun i _ => perStorage i)
  simpa only [multiplied,multipliedBudget,List.length_range,Nat.mul_assoc] using output

def equations (state : ArenaSource.State) (basis : List Row) : Counted (List Row) :=
  let frame := PortEmbedding.initial state
  let first := laws frame
  let second := gates state
  let third := multiplied frame basis
  let output := first.value++second.value++basis++third.value
  ⟨output,first.cells+second.cells+third.cells+
    32*(rowsCells first.value+rowsCells second.value+rowsCells basis+rowsCells third.value+rowsCells output+1)+64⟩

theorem equations_value (state : ArenaSource.State) (basis : List Row) : (equations state basis).value=ProductRows.equations state basis := by
  simp only [equations,laws_value,gates_value,multiplied_value,ProductRows.equations]

def equationsBudget (n : Nat) : Nat := lawsBudget n+gatesBudget n+multipliedBudget n (n*(n+2))+32*(2*ProductRows.rowBound n+1)+64

theorem equations_cells (state : ArenaSource.State) (basis : List Row) (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) :
    (equations state basis).cells ≤ equationsBudget state.arena.code.size := by
  have first := laws_cells (PortEmbedding.initial state)
  have second := gates_cells state
  have third := multiplied_cells (PortEmbedding.initial state) basis
  have count := basis_length_le _ basis valid.1 valid.2
  have size := (AffineClauses.Cost.source_storage state.arena.code.size basis
    (fun row member => ⟨valid.1.1 row member,valid.2 row member⟩)).trans
      (show basis.length*(state.arena.code.size+2) ≤ state.arena.code.size*(state.arena.code.size+2) by gcongr)
  simp only [PortEmbedding.initial_size] at first third
  have thirdBound := third.trans (show multipliedBudget state.arena.code.size (rowsCells basis) ≤
      multipliedBudget state.arena.code.size (state.arena.code.size*(state.arena.code.size+2)) by
        unfold multipliedBudget multiplyPoolBudget multiplyBudget; gcongr)
  have stored := ProductRows.equations_storage state basis valid
  change rowsCells (ProductRows.laws (PortEmbedding.initial state)++ProductRows.gates state++basis++ProductSource.rows (PortEmbedding.initial state) basis) ≤ _ at stored
  simp only [CapacityMatching.RowCost.rowsCells_append] at stored
  simp only [equations,equationsBudget,CapacityMatching.RowCost.rowsCells_append,laws_value,gates_value,multiplied_value]
  omega

def seed (state : ArenaSource.State) : Counted Result :=
  let checked := JointCircuitCost.checked state.arena.code.toList
  if checked.value then
    let result := JointCircuitCost.analyzed state
    ⟨result.value,checked.cells+result.cells+16*(AffineCarrier.resultSize result.value+state.arena.code.size+state.relations.length+1)+24⟩
  else ⟨.basis [],checked.cells+16*(state.arena.code.size+state.relations.length+1)+24⟩

theorem seed_value (state : ArenaSource.State) : (seed state).value=ProductRows.seed state := by
  simp only [seed,JointCircuitCost.checked_value,ProductRows.seed,JointCircuit.noAdd]
  split <;> simp_all

def seedBudget (n c : Nat) : Nat := 4*n+1+JointCircuitCost.analysisBudget n c+16*(AffineCarrier.Cost.cellBound n+n+c+2)+24

theorem seed_cells (state : ArenaSource.State) : (seed state).cells ≤ seedBudget state.arena.code.size state.relations.length := by
  have first := JointCircuitCost.checked_cells state.arena.code.toList
  simp only [Array.length_toList] at first
  have second := JointCircuitCost.analyzed_cells state
  have valid := JointCircuitCost.analyzed_valid state
  have stored := AffineCarrier.Cost.result_size state.arena.code.size (JointCircuitCost.analyzed state).value valid.1 valid.2
  simp only [seed,seedBudget]
  split <;> simp only <;> omega

def prepare (state : ArenaSource.State) : Counted ProductRows.Prepared :=
  let frame := expand (PortEmbedding.initial state)
  let source := seed state
  match source.value with
  | .contradiction => ⟨⟨frame.value,[],true⟩,frame.cells+source.cells+32*(frame.value.state.arena.code.size+frame.value.ports.size+state.relations.length+1)+64⟩
  | .basis basis =>
      let rows := equations state basis
      ⟨⟨frame.value,rows.value,false⟩,frame.cells+source.cells+rows.cells+
        32*(frame.value.state.arena.code.size+frame.value.ports.size+state.relations.length+rowsCells rows.value+AffineCarrier.cellSize basis+1)+64⟩

theorem prepare_value (state : ArenaSource.State) : (prepare state).value=ProductRows.prepare state := by
  simp only [prepare,expand_value,seed_value,equations_value,ProductRows.prepare]
  split <;> simp_all

def prepareBudget (n c : Nat) : Nat := expandBudget n n c+seedBudget n c+equationsBudget n+
  32*((n+n*n+1)+(n+n*n)+c+ProductRows.rowBound n+AffineCarrier.Cost.cellBound n+1)+64

theorem prepare_cells (state : ArenaSource.State) : (prepare state).cells ≤ prepareBudget state.arena.code.size state.relations.length := by
  have expanded := expand_cells (PortEmbedding.initial state)
  simp only [PortEmbedding.initial_size] at expanded
  have first : (expand (PortEmbedding.initial state)).cells ≤ expandBudget state.arena.code.size state.arena.code.size state.relations.length := expanded
  have second := seed_cells state
  have size := ProductBatch.generate_size (PortEmbedding.initial state)
  have ports := ProductBatch.generate_ports (PortEmbedding.initial state)
  simp only [PortEmbedding.initial_size] at size ports
  change (expand (PortEmbedding.initial state)).value.state.arena.code.size ≤ state.arena.code.size+state.arena.code.size*state.arena.code.size+1 at size
  change (expand (PortEmbedding.initial state)).value.ports.size=state.arena.code.size+state.arena.code.size*state.arena.code.size at ports
  have valid := ProductRows.seed_valid state
  rw [← seed_value] at valid
  simp only [prepare]
  cases result : (seed state).value with
  | contradiction => simp only [prepareBudget]; omega
  | basis basis =>
      have vb : Triangular basis ∧ RowsWithin state.arena.code.size basis := by simpa only [result,Result.triangular,Result.within] using valid
      have generated := equations_cells state basis vb
      have rows := ProductRows.equations_storage state basis vb
      rw [← equations_value] at rows
      have stored := AffineCarrier.Cost.cell_size state.arena.code.size basis vb.1 vb.2
      simp only [prepareBudget]
      omega

end SaturationMonoid.ComplexityProjection.SATSource.ProductCost

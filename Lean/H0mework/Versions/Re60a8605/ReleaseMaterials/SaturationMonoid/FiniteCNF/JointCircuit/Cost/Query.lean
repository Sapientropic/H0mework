import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Cost.Front

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.JointCircuitCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine

/-- The query normalizes its actual two-slot row, then executes the paid Gaussian
reducer. Copies of the basis and both intermediate rows remain in its ledger. -/
def linked (basis : List Row) (left right : Nat) : Counted Bool :=
  let normalized := CapacityMatching.RowCost.normalize ⟨[left,right],false⟩
  let reduced := EliminateCost.reduce basis normalized.value
  ⟨decide (reduced.row=⟨[],false⟩),normalized.cells+reduced.cells+
    16*(AffineCarrier.cellSize basis+normalized.value.vars.length+reduced.row.vars.length+1)+24⟩

theorem linked_value (basis : List Row) (left right : Nat) :
    (linked basis left right).value=JointCircuit.linked basis left right := rfl

def linkBudget (n : Nat) : Nat :=
  6*n+17+n*EliminateCost.reduceCellBudget n+1+16*(AffineCarrier.Cost.cellBound n+2*n+1)+24

theorem linked_cells (n : Nat) (basis : List Row) (valid : Triangular basis ∧ RowsWithin n basis)
    (left right : Fin n) : (linked basis left.val right.val).cells ≤ linkBudget n := by
  let row : Row := ⟨[left.val,right.val],false⟩
  have inside : Parity.Within n row.vars := by
    intro i member
    simp only [row,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact left.isLt
    · exact right.isLt
  have normalized := CapacityMatching.RowCost.normalize_valid n row inside
  have first := CapacityMatching.RowCost.normalize_cells n row inside
  have inputLength := Table.row_length_le n _ normalized
  have second := EliminateCost.reduce_cells n basis (fun item member => ⟨valid.1.1 item member,valid.2 item member⟩)
    (CapacityMatching.RowCost.normalize row).value normalized
  have rank := basis_length_le n basis valid.1 valid.2
  have reduced : Table.RowValid n (EliminateCost.reduce basis (CapacityMatching.RowCost.normalize row).value).row := by
    rw [EliminateCost.reduce_row]
    exact ⟨reduceWith_nodup basis valid.1.1 _ normalized.1,reduceWith_within n basis valid.2 _ normalized.2⟩
  have outputLength := Table.row_length_le n _ reduced
  have basisSize := AffineCarrier.Cost.cell_size n basis valid.1 valid.2
  have reducedWork := second.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ rank) 1)
  change (CapacityMatching.RowCost.normalize row).cells+(EliminateCost.reduce basis (CapacityMatching.RowCost.normalize row).value).cells+
    16*(AffineCarrier.cellSize basis+(CapacityMatching.RowCost.normalize row).value.vars.length+
      (EliminateCost.reduce basis (CapacityMatching.RowCost.normalize row).value).row.vars.length+1)+24 ≤ _
  change (CapacityMatching.RowCost.normalize row).cells ≤ 2*(2*n+5)+2*n+7 at first
  unfold linkBudget
  omega

def probe (state : ArenaSource.State) (basis : List Row) (input root : Fin state.arena.code.size) (address : Nat) : Counted Bool :=
  let relation := linked basis input.val root.val
  let allowed := ArenaCost.eligible state (JointCircuit.proposal state input root address)
  ⟨relation.value && allowed.value,relation.cells+allowed.cells+20⟩

theorem probe_value (state : ArenaSource.State) (basis : List Row) (input root : Fin state.arena.code.size) (address : Nat) :
    (probe state basis input root address).value=
      (JointCircuit.linked basis input.val root.val && ArenaSource.eligible state (JointCircuit.proposal state input root address)) := by
  simp only [probe,linked_value,ArenaCost.eligible_value]

theorem probe_cells (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis)
    (input root : Fin state.arena.code.size) (address : Nat) :
    (probe state basis input root address).cells ≤ linkBudget state.arena.code.size+ArenaCost.eligibleBudget state.arena.code.size+20 := by
  have link := linked_cells state.arena.code.size basis valid input root
  have allowed := ArenaCost.eligible_cells state (JointCircuit.proposal state input root address)
  simp only [probe]
  omega

def rootScan (state : ArenaSource.State) (basis : List Row) (input : Fin state.arena.code.size) (address : Nat) :
    List (Fin state.arena.code.size) → Counted (Option (Fin state.arena.code.size))
  | [] => ⟨none,1⟩
  | root::rest =>
      let checked := probe state basis input root address
      if checked.value then ⟨some root,checked.cells+8⟩ else
        let tail := rootScan state basis input address rest
        ⟨tail.value,checked.cells+tail.cells+8⟩

theorem rootScan_value (state : ArenaSource.State) (basis : List Row) (input : Fin state.arena.code.size) (address : Nat)
    (roots : List (Fin state.arena.code.size)) :
    (rootScan state basis input address roots).value=roots.find? (fun root =>
      JointCircuit.linked basis input.val root.val && ArenaSource.eligible state (JointCircuit.proposal state input root address)) := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
      cases flag : (JointCircuit.linked basis input.val root.val &&
        ArenaSource.eligible state (JointCircuit.proposal state input root address)) <;>
        simp only [rootScan,probe_value,flag,List.find?_cons,ih,Bool.false_eq_true,if_false,if_true]

theorem rootScan_cells (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) (input : Fin state.arena.code.size) (address : Nat)
    (roots : List (Fin state.arena.code.size)) :
    (rootScan state basis input address roots).cells ≤
      roots.length*(linkBudget state.arena.code.size+ArenaCost.eligibleBudget state.arena.code.size+28)+1 := by
  induction roots with
  | nil => simp [rootScan]
  | cons root rest ih =>
      have first := probe_cells state basis valid input root address
      simp only [rootScan,List.length_cons]
      split <;> simp only <;> nlinarith

def rootFor (state : ArenaSource.State) (basis : List Row) (input : Fin state.arena.code.size) (address : Nat) :
    Counted (Option (Fin state.arena.code.size)) :=
  let output := rootScan state basis input address (List.finRange state.arena.code.size)
  ⟨output.value,output.cells+8*state.arena.code.size+8⟩

theorem rootFor_value (state : ArenaSource.State) (basis : List Row) (input : Fin state.arena.code.size) (address : Nat) :
    (rootFor state basis input address).value=JointCircuit.rootFor state basis input address := by
  simp only [rootFor,rootScan_value,JointCircuit.rootFor]

def rootBudget (nodes : Nat) : Nat :=
  nodes*(linkBudget nodes+ArenaCost.eligibleBudget nodes+28)+1+8*nodes+8

theorem rootFor_cells (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) (input : Fin state.arena.code.size) (address : Nat) :
    (rootFor state basis input address).cells ≤ rootBudget state.arena.code.size := by
  have work := rootScan_cells state basis valid input address (List.finRange state.arena.code.size)
  simp only [List.length_finRange] at work
  simp only [rootFor,rootBudget]
  omega

def scan (state : ArenaSource.State) (basis : List Row) :
    List (Fin state.arena.code.size) → Counted (Option (ArenaSource.Labeled state.arena))
  | [] => ⟨none,1⟩
  | input::rest =>
      match JointCircuit.node state input with
      | .input address =>
          let found := rootFor state basis input address
          match found.value with
          | some root => ⟨some (JointCircuit.proposal state input root address),found.cells+8*state.arena.code.size+18⟩
          | none =>
              let tail := scan state basis rest
              ⟨tail.value,found.cells+tail.cells+8*state.arena.code.size+18⟩
      | _ =>
          let tail := scan state basis rest
          ⟨tail.value,tail.cells+8*state.arena.code.size+18⟩

theorem scan_value (state : ArenaSource.State) (basis : List Row) (indices : List (Fin state.arena.code.size)) :
    (scan state basis indices).value=JointCircuit.scan state basis indices := by
  induction indices with
  | nil => rfl
  | cons input rest ih =>
      cases shape : JointCircuit.node state input <;> simp only [scan,JointCircuit.scan,shape,rootFor_value,ih]
      split <;> simp_all

theorem scan_cells (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) (indices : List (Fin state.arena.code.size)) :
    (scan state basis indices).cells ≤ indices.length*(rootBudget state.arena.code.size+8*state.arena.code.size+18)+1 := by
  induction indices with
  | nil => simp [scan]
  | cons input rest ih =>
      cases shape : JointCircuit.node state input <;> simp only [scan,shape,List.length_cons]
      all_goals try nlinarith
      rename_i address
      have first := rootFor_cells state basis valid input address
      split <;> simp only <;> nlinarith

def pick (state : ArenaSource.State) (basis : List Row) : Counted (Option (ArenaSource.Labeled state.arena)) :=
  let output := scan state basis (List.finRange state.arena.code.size)
  ⟨output.value,output.cells+8*state.arena.code.size+8⟩

theorem pick_value (state : ArenaSource.State) (basis : List Row) : (pick state basis).value=JointCircuit.pick state basis := by
  simp only [pick,scan_value,JointCircuit.pick]

def pickBudget (nodes : Nat) : Nat := nodes*(rootBudget nodes+8*nodes+18)+1+8*nodes+8

theorem pick_cells (state : ArenaSource.State) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin state.arena.code.size basis) :
    (pick state basis).cells ≤ pickBudget state.arena.code.size := by
  have work := scan_cells state basis valid (List.finRange state.arena.code.size)
  simp only [List.length_finRange] at work
  simp only [pick,pickBudget]
  omega

end SaturationMonoid.ComplexityProjection.SATSource.JointCircuitCost

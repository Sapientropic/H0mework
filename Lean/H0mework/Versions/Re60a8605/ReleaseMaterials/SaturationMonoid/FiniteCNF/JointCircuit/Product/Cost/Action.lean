import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Product.Cost.Source

/-! Actual remapping, Gaussian execution and source updates share the same rows. -/
set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ProductCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open CapacityMatching.RowCost (rowCells rowsCells rowsCells_cons rowsCells_nil)

def refs (frame : Frame) : List Nat → Counted (List Nat)
  | [] => ⟨[],1⟩
  | i::rest =>
      let root := (PortEmbedding.ref frame.state frame.ports i).val
      let tail := refs frame rest
      ⟨root::tail.value,tail.cells+8*(frame.ports.size+tail.value.length+1)+16⟩

theorem refs_value (frame : Frame) (indices : List Nat) :
    (refs frame indices).value=indices.map (fun i => (PortEmbedding.ref frame.state frame.ports i).val) := by
  induction indices <;> simp_all only [refs,List.map_nil,List.map_cons]

def refsBudget (p s : Nat) : Nat := s*(8*(p+s+1)+16)+1

theorem refs_cells (frame : Frame) (indices : List Nat) : (refs frame indices).cells ≤ refsBudget frame.ports.size indices.length := by
  induction indices with
  | nil => simp [refs,refsBudget]
  | cons i rest ih => simp only [refs,refs_value,List.length_map,List.length_cons,refsBudget] at *; nlinarith

def row (frame : Frame) (source : Row) : Counted (List Row) :=
  let generated := refs frame source.vars
  ⟨[⟨generated.value,source.rhs⟩],generated.cells+16*(rowCells source+1)+16⟩

theorem row_value (frame : Frame) (source : Row) : (row frame source).value=[ProductRows.mapped frame source] := by
  simp only [row,refs_value,ProductRows.mapped]

theorem row_storage (frame : Frame) (source : Row) : rowsCells (row frame source).value=rowCells source := by
  rw [row_value]
  simp only [rowsCells_cons,rowsCells_nil,ProductRows.mapped_storage,Nat.add_zero]

def rowBudget (p s : Nat) : Nat := refsBudget p s+16*(s+1)+16

theorem row_cells (frame : Frame) (source : Row) : (row frame source).cells ≤ rowBudget frame.ports.size (rowCells source) := by
  have first := refs_cells frame source.vars
  have work := first.trans (show refsBudget frame.ports.size source.vars.length ≤ refsBudget frame.ports.size (rowCells source) by
    unfold refsBudget rowCells; gcongr <;> omega)
  simp only [row,rowBudget]
  omega

def remap (frame : Frame) (source : List Row) : Counted (List Row) := CapacityMatching.RowCost.gather (row frame) source

theorem remap_value (frame : Frame) (source : List Row) : (remap frame source).value=source.map (ProductRows.mapped frame) := by
  simp only [remap,CapacityMatching.RowCost.gather_value,row_value,singleton_flatMap]

theorem remap_storage (frame : Frame) (source : List Row) : rowsCells (remap frame source).value=rowsCells source := by
  rw [remap_value]
  induction source <;> simp_all only [List.map_nil,List.map_cons,rowsCells_nil,rowsCells_cons,ProductRows.mapped_storage]

def remapBudget (p s : Nat) : Nat := s*(rowBudget p s+(s+1)*s+5)+1

theorem remap_cells (frame : Frame) (source : List Row) : (remap frame source).cells ≤ remapBudget frame.ports.size (rowsCells source) := by
  have count := rows_length source
  have work := CapacityMatching.RowCost.gather_cells (row frame) source
    (rowBudget frame.ports.size (rowsCells source)) (rowsCells source)
    (fun item member => (row_cells frame item).trans (by
      have bound := row_member source item member
      unfold rowBudget refsBudget
      gcongr))
    (fun item member => (row_storage frame item).le.trans (row_member source item member))
  exact work.trans (by unfold remapBudget; gcongr)

def analyze (frame : Frame) (source : List Row) : Counted Result :=
  let mapped := remap frame source
  let generated := EliminateCost.run mapped.value
  ⟨generated.result,mapped.cells+(generated.cells+1)*(16*(AffineCarrier.Cost.cellBound frame.state.arena.code.size+rowsCells source+1)+32)+
    16*(rowsCells mapped.value+AffineCarrier.resultSize generated.result+1)+32⟩

theorem analyze_value (frame : Frame) (source : List Row) : (analyze frame source).value=ProductRows.analyze frame source := by
  simp only [analyze,EliminateCost.run_result,remap_value,ProductRows.analyze]

def gaussianBudget (n s : Nat) : Nat := s*(2*n+5)+s*(EliminateCost.insertCellBudget n+1)+1
def analyzeBudget (n p s : Nat) : Nat := remapBudget p s+(gaussianBudget n s+1)*(16*(AffineCarrier.Cost.cellBound n+s+1)+32)+
  16*(s+AffineCarrier.Cost.cellBound n+2)+32

theorem analyze_cells (frame : Frame) (source : List Row) :
    (analyze frame source).cells ≤ analyzeBudget frame.state.arena.code.size frame.ports.size (rowsCells source) := by
  have first := remap_cells frame source
  have storage := remap_storage frame source
  have within : RowsWithin frame.state.arena.code.size (remap frame source).value := by
    rw [remap_value]
    intro row member
    obtain ⟨old,_,rfl⟩ := List.mem_map.mp member
    exact ProductRows.mapped_within frame old
  have count := rows_length (remap frame source).value
  have terms : Gates.rowTerms (remap frame source).value ≤ rowsCells source := by
    have same := AffineCollect.Cost.rows_size (remap frame source).value
    rw [storage] at same
    omega
  have second := EliminateCost.run_cells frame.state.arena.code.size (remap frame source).value within
  have work := second.trans (show Gates.rowTerms (remap frame source).value*(2*frame.state.arena.code.size+5)+
      (remap frame source).value.length*(EliminateCost.insertCellBudget frame.state.arena.code.size+1)+1 ≤ gaussianBudget frame.state.arena.code.size (rowsCells source) by
    unfold gaussianBudget
    gcongr
    omega)
  have valid := ProductRows.analyze_valid frame source
  have result := AffineCarrier.Cost.result_size frame.state.arena.code.size (ProductRows.analyze frame source) valid.1 valid.2
  rw [← analyze_value] at result
  simp only [analyze] at result
  simp only [analyze,analyzeBudget,storage]
  have multiplied := Nat.mul_le_mul_right (16*(AffineCarrier.Cost.cellBound frame.state.arena.code.size+rowsCells source+1)+32) (Nat.add_le_add_right work 1)
  omega

def update (frame : Frame) (source : List Row) : Counted PortUpdate.Output :=
  let generated := analyze frame source
  match generated.value with
  | .contradiction => ⟨⟨frame,true,[],some .contradiction⟩,generated.cells+32*(frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+rowsCells source+1)+48⟩
  | .basis basis =>
      let picked := JointCircuitCost.pick frame.state basis
      match picked.value with
      | none => ⟨⟨frame,false,[],some (.basis basis)⟩,generated.cells+picked.cells+
          32*(frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+rowsCells source+AffineCarrier.cellSize basis+1)+48⟩
      | some item =>
          let changed := PortCost.bind frame item.address item.relation.right
          let body := ArenaCost.Dependency.compact (ArenaAction.focus frame.state.arena.code item.relation.right)
          ⟨⟨changed.value,false,[ArenaSource.selected frame.state item],some (.basis basis)⟩,
            generated.cells+picked.cells+changed.cells+2*body.cells+
              32*(frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+rowsCells source+AffineCarrier.cellSize basis+body.value.code.size+1)+48⟩

theorem update_value (frame : Frame) (source : List Row) : (update frame source).value=ProductRows.update frame source := by
  simp only [update,analyze_value,JointCircuitCost.pick_value,PortCost.bind_value,ProductRows.update,ProductRows.apply]
  split
  · simp_all
  · split <;> simp_all

def updateBudget (n p c s : Nat) : Nat := analyzeBudget n p s+JointCircuitCost.pickBudget n+PortCost.bindBudget n p c+
  2*ArenaCost.Dependency.budget n+32*(2*n+p+c+s+AffineCarrier.Cost.cellBound n+1)+48

theorem update_cells (frame : Frame) (source : List Row) :
    (update frame source).cells ≤ updateBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length (rowsCells source) := by
  have first := analyze_cells frame source
  have valid := ProductRows.analyze_valid frame source
  rw [← analyze_value] at valid
  simp only [update]
  cases generated : (analyze frame source).value with
  | contradiction => simp only [updateBudget]; omega
  | basis basis =>
      have vb : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis := by simpa only [generated,Result.triangular,Result.within] using valid
      have stored := AffineCarrier.Cost.cell_size frame.state.arena.code.size basis vb.1 vb.2
      have picked := JointCircuitCost.pick_cells frame.state basis vb
      cases chosen : (JointCircuitCost.pick frame.state basis).value with
      | none => simp only [chosen,updateBudget]; omega
      | some item =>
          have changed := PortCost.bind_cells frame item.address item.relation.right
          have body := ArenaCost.Dependency.compact_cells (ArenaAction.focus frame.state.arena.code item.relation.right)
          change _ ≤ ArenaCost.Dependency.budget frame.state.arena.code.size at body
          have size := ArenaAction.actualBody_size frame.state.arena item.relation.right
          rw [← ArenaCost.body_code] at size
          simp only [chosen,updateBudget]
          omega

theorem update_history (frame : Frame) (source : List Row) : ArenaCost.historySize (update frame source).value.binding ≤ frame.state.arena.code.size+9 := by
  simp only [update]
  split
  · simp [ArenaCost.historySize]
  · split
    · simp [ArenaCost.historySize]
    · rename_i basis equation item found
      have size := ArenaAction.actualBody_size frame.state.arena item.relation.right
      change (ArenaAction.actualBody frame.state.arena item.relation.right).code.size+9 ≤ _
      omega

theorem update_joint (frame : Frame) (source : List Row) :
    JointCircuitCost.jointStorage (update frame source).value.joint ≤ AffineCarrier.Cost.cellBound frame.state.arena.code.size+2 := by
  have valid := ProductRows.analyze_valid frame source
  rw [← analyze_value] at valid
  simp only [update]
  cases generated : (analyze frame source).value with
  | contradiction => simp [JointCircuitCost.jointStorage,AffineCarrier.resultSize]
  | basis basis =>
      have vb : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis := by simpa only [generated,Result.triangular,Result.within] using valid
      have stored := AffineCarrier.Cost.cell_size frame.state.arena.code.size basis vb.1 vb.2
      cases picked : (JointCircuitCost.pick frame.state basis).value <;>
        simp only [picked,JointCircuitCost.jointStorage,AffineCarrier.resultSize] <;> omega

end SaturationMonoid.ComplexityProjection.SATSource.ProductCost

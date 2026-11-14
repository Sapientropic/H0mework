import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Effects.Relations

set_option autoImplicit false
namespace SaturationMonoid.ComplexityProjection.SATSource.EffectRelationsCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowsCells)
abbrev Counted := ArenaCost.Counted

def read (frame : PortEmbedding.Frame) (root : Nat) : Result → Counted (Option Bool)
  | .contradiction => ⟨none,32*(frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+1)+32⟩
  | .basis basis =>
      let table := Table.coordinates frame.state.arena.code.size basis
      let chosen := ProductClosureCost.coordinate frame table root
      let row := chosen.value.headD Gates.zeroRow
      ⟨(if row.vars.isEmpty then some row.rhs else none),AffineCollect.coordinateWork frame.state.arena.code.size basis+chosen.cells+
        32*(AffineCollect.tableSize table+rowsCells chosen.value+AffineCarrier.resultSize (.basis basis)+
          frame.state.arena.code.size+frame.ports.size+frame.state.relations.length+1)+64⟩

theorem read_value (frame : PortEmbedding.Frame) (root : Nat) (result : Result) : (read frame root result).value=
    match result with
    | .contradiction => none
    | .basis basis =>
        let row := (Table.coordinates frame.state.arena.code.size basis).getD (PortEmbedding.ref frame.state frame.ports root).val Gates.zeroRow
        if row.vars.isEmpty then some row.rhs else none := by
  cases result <;> simp only [read,ProductClosureCost.coordinate_value,List.headD_cons]

def readBudget (n p c : Nat) : Nat := AffineCollect.Cost.coordinateBudget n+ProductClosureCost.coordinateBudget n p+
  32*(2*AffineCarrier.Cost.cellBound n+2*n+p+c+4)+64

theorem read_cells (frame : PortEmbedding.Frame) (root : Nat) (result : Result)
    (valid : result.triangular ∧ result.within frame.state.arena.code.size) :
    (read frame root result).cells ≤ readBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length := by
  cases result with
  | contradiction => simp only [read,readBudget]; omega
  | basis basis =>
      have basisValid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis := valid
      have first := AffineCollect.Cost.coordinate_visits frame.state.arena.code.size basis basisValid
      have tableStored := AffineCollect.Cost.coordinate_size frame.state.arena.code.size basis
      have tableValid : Table.Valid frame.state.arena.code.size (Table.coordinates frame.state.arena.code.size basis) :=
        ConditionalCandidateCost.table_valid _ _
      have chosen := ProductClosureCost.coordinate_cells frame _ _ tableValid (Table.coordinates_size _ _) root
      have chosenStored := ProductClosureCost.coordinate_storage frame _ _ tableValid root
      have before := AffineCarrier.Cost.result_size frame.state.arena.code.size (.basis basis) valid.1 valid.2
      simp only [read,readBudget]
      omega

def prepare (state : ArenaSource.State) : Counted ProductRows.Prepared :=
  let expanded := ProductCost.expand (PortEmbedding.initial state)
  let rows := ProductCost.equations state []
  ⟨⟨expanded.value,rows.value,false⟩,expanded.cells+rows.cells+
    32*(state.arena.code.size+state.relations.length+expanded.value.state.arena.code.size+
      expanded.value.ports.size+expanded.value.state.relations.length+rowsCells rows.value+1)+32⟩

theorem prepare_value (state : ArenaSource.State) : (prepare state).value=EffectRelations.prepared state := rfl

theorem prepared_size (state : ArenaSource.State) :
    (EffectRelations.prepared state).frame.state.arena.code.size ≤ state.arena.code.size+state.arena.code.size*state.arena.code.size+1 := by
  have size := ProductBatch.generate_size (PortEmbedding.initial state)
  rw [PortEmbedding.initial_size] at size
  rw [EffectRelations.prepared_frame,ProductClosure.frame]
  exact size

theorem prepared_ports (state : ArenaSource.State) :
    (EffectRelations.prepared state).frame.ports.size=state.arena.code.size+state.arena.code.size*state.arena.code.size := by
  rw [EffectRelations.prepared_frame,ProductClosure.frame,ProductBatch.generate_ports,PortEmbedding.initial_size]

theorem prepared_count (state : ArenaSource.State) : (EffectRelations.prepared state).frame.state.relations.length=state.relations.length := by
  rw [EffectRelations.prepared_frame,ProductClosure.frame,ProductBatch.generate_count]
  rfl

theorem prepared_rows (state : ArenaSource.State) : rowsCells (EffectRelations.prepared state).rows ≤ ProductRows.rowBound state.arena.code.size := by
  rw [EffectRelations.prepared_rows]
  exact ProductRows.equations_storage state [] ⟨triangular_nil,by simp [RowsWithin]⟩

def prepareBudget (n c : Nat) : Nat := ProductCost.expandBudget n n c+ProductCost.equationsBudget n+
  32*(n+c+(n+n*n+1)+(n+n*n)+c+ProductRows.rowBound n+1)+32

theorem prepare_cells (state : ArenaSource.State) : (prepare state).cells ≤ prepareBudget state.arena.code.size state.relations.length := by
  have expanded := ProductCost.expand_cells (PortEmbedding.initial state)
  rw [PortEmbedding.initial_size] at expanded
  change (ProductCost.expand (PortEmbedding.initial state)).cells ≤ ProductCost.expandBudget state.arena.code.size state.arena.code.size state.relations.length at expanded
  have equations := ProductCost.equations_cells state [] ⟨triangular_nil,by simp [RowsWithin]⟩
  have size := prepared_size state
  have ports := prepared_ports state
  have count := prepared_count state
  have rows := prepared_rows state
  change (ProductCost.expand (PortEmbedding.initial state)).cells+(ProductCost.equations state []).cells+
    32*(state.arena.code.size+state.relations.length+(EffectRelations.prepared state).frame.state.arena.code.size+
      (EffectRelations.prepared state).frame.ports.size+(EffectRelations.prepared state).frame.state.relations.length+
      rowsCells (EffectRelations.prepared state).rows+1)+32 ≤ _
  unfold prepareBudget
  omega

def constant (state : ArenaSource.State) : Counted (Option Bool) :=
  let source := prepare state
  let kernel := ProductClosureCost.fromPrepared (PortEmbedding.initial state) source.value
  let result := read source.value.frame state.program.weight.val kernel.value
  ⟨result.value,source.cells+kernel.cells+result.cells+16*(state.arena.code.size+state.relations.length+1)+16⟩

theorem constant_value (state : ArenaSource.State) : (constant state).value=EffectRelations.constant state := by
  simp only [constant,prepare_value,read_value,EffectRelations.constant]
  rfl

def constantBudget (n c : Nat) : Nat :=
  prepareBudget n c+ProductClosureCost.preparedBudget n n c (n+n*n+1) (n+n*n) c (ProductRows.rowBound n)+
    readBudget (n+n*n+1) (n+n*n) c+16*(n+c+1)+16

theorem readBudget_mono (n N p P c C : Nat) (hn : n ≤ N) (hp : p ≤ P) (hc : c ≤ C) : readBudget n p c ≤ readBudget N P C := by
  unfold readBudget AffineCollect.Cost.coordinateBudget ProductClosureCost.coordinateBudget AffineCarrier.Cost.cellBound
  gcongr

theorem constant_cells (state : ArenaSource.State) : (constant state).cells ≤ constantBudget state.arena.code.size state.relations.length := by
  have source := prepare_cells state
  have kernel := ProductClosureCost.fromPrepared_cells (PortEmbedding.initial state) (EffectRelations.prepared state)
  have expanded := prepared_size state
  have ports := prepared_ports state
  have count := prepared_count state
  have rows := prepared_rows state
  have kernelBound := kernel.trans (ProductClosureCost.preparedBudget_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _
    le_rfl (by rw [PortEmbedding.initial_size]) le_rfl expanded (by rw [ports]) (by rw [count]) rows)
  have result := read_cells (EffectRelations.prepared state).frame state.program.weight.val
    (ProductClosureCost.fromPrepared (PortEmbedding.initial state) (EffectRelations.prepared state)).value (ProductClosureCost.fromPrepared_valid _ _)
  have readBound := result.trans (readBudget_mono _ _ _ _ _ _ expanded (by rw [ports]) (by rw [count]))
  simp only [constant,prepare_value,constantBudget]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add source kernelBound) readBound) _) _

def normalize (program : Program) : Counted Program :=
  let source := ArenaCost.build program []
  let result := constant source.value
  let output := match result.value with | none => program | some value => Affine.Boolean.constant value
  ⟨output,source.cells+result.cells+32*(program.code.size+source.value.arena.code.size+output.code.size+1)+32⟩

theorem normalize_value (program : Program) : (normalize program).value=EffectRelations.normalize program := by
  simp only [normalize,ArenaCost.build_value,constant_value,EffectRelations.normalize]
  rfl

theorem normalize_size (program : Program) : (normalize program).value.code.size ≤ program.code.size+2 := by
  dsimp only [normalize]
  split <;> simp [Affine.Boolean.constant,InterferenceDecision.fromAmplitude,Fragment.constant]

theorem prepareBudget_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : prepareBudget n c ≤ prepareBudget N C := by
  unfold prepareBudget ProductCost.expandBudget ProductCost.equationsBudget
    ProductCost.codeBudget ProductCost.lawsBudget ProductCost.gatesBudget ProductCost.gateBudget
    ProductCost.multipliedBudget ProductCost.multiplyPoolBudget ProductCost.multiplyBudget ProductCost.indexBudget
    ProductCost.pairsBudget ProductRows.rowBound ArenaCost.Reduction.budget
  dsimp only
  gcongr

theorem constantBudget_mono (n N c C : Nat) (hn : n ≤ N) (hc : c ≤ C) : constantBudget n c ≤ constantBudget N C := by
  have source := prepareBudget_mono n N c C hn hc
  have kernel := ProductClosureCost.preparedBudget_mono n N n N c C (n+n*n+1) (N+N*N+1) (n+n*n) (N+N*N) c C
    (ProductRows.rowBound n) (ProductRows.rowBound N) hn hn hc (by gcongr) (by gcongr) hc (by unfold ProductRows.rowBound; gcongr)
  have result := readBudget_mono (n+n*n+1) (N+N*N+1) (n+n*n) (N+N*N) c C (by gcongr) (by gcongr) hc
  unfold constantBudget
  omega

def normalizeBudget (n : Nat) : Nat := ArenaCost.buildBudget 0 (n+1)+constantBudget (n+1) 0+32*(n+(n+1)+(n+2)+1)+32

theorem normalize_cells (program : Program) : (normalize program).cells ≤ normalizeBudget program.code.size := by
  have source := ArenaCost.build_cells program []
  have nodes := ArenaCost.build_nodes program []
  simp only [ArenaCost.inventory,List.map_nil,List.sum_nil,List.length_nil,Nat.add_zero] at source nodes
  have result := constant_cells (ArenaCost.build program []).value
  have count : (ArenaCost.build program []).value.relations.length=0 := by rw [ArenaCost.build_value,ArenaSource.build_count]; rfl
  have resultBound := result.trans (constantBudget_mono _ _ _ _ nodes (by rw [count]))
  have output := normalize_size program
  change (ArenaCost.build program []).cells+(constant (ArenaCost.build program []).value).cells+
    32*(program.code.size+(ArenaCost.build program []).value.arena.code.size+(normalize program).value.code.size+1)+32 ≤ _
  unfold normalizeBudget
  omega

end SaturationMonoid.ComplexityProjection.SATSource.EffectRelationsCost

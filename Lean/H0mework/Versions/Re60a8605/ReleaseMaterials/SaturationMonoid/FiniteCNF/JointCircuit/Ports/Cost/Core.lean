import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointCircuit.Ports.Update

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.PortCost
open InterferenceProgram
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open PortEmbedding (Frame)
open CapacityMatching.RowCost (rowCells rowsCells)
abbrev Counted := ArenaCost.Counted

theorem rowValid_mono (n N : Nat) (row : Row) (valid : Table.RowValid n row) (bound : n ≤ N) :
    Table.RowValid N row := ⟨valid.1,fun i member => (valid.2 i member).trans_le bound⟩

theorem image_valid_mono (n q N : Nat) (image : AtomImage.State) (valid : image.Valid n q)
    (coeff : n ≤ N) (label : q ≤ N) : image.Valid N N := by
  refine ⟨?_,?_⟩
  · intro row member
    exact ⟨rowValid_mono n N row.coeff (valid.1 row member).1 coeff,
      rowValid_mono q N row.label (valid.1 row member).2 label⟩
  · intro row member
    exact rowValid_mono q N row (valid.2 row member) label

/-- The existing insertion program consumes the rectangular table unchanged.
The workspace allowance controls copies; it does not pad the source table. -/
def image (n : Nat) (source : Array Row) : Counted AtomImage.State :=
  AffineForget.Cost.buildImage (n+source.size) source

theorem image_value (n : Nat) (source : Array Row) : (image n source).value=AtomImage.generate source :=
  AffineForget.Cost.buildImage_value _ _

def imageVisitsBudget (n q : Nat) : Nat :=
  (q*n+q)*(2*(n+q)+5)+q*(n*AtomImage.stepBudget n q+q+11)+2

def imageBudget (n q : Nat) : Nat :=
  (imageVisitsBudget n q+1)*(8*AffineForget.Cost.imageWorkspace (n+q)+8)+
    2*(q*n+2*q+1+(q*n+4*q)+((n+q)*(2*(n+q)+3)+2))+7

theorem image_cells (n : Nat) (source : Array Row) (valid : Table.Valid n source) :
    (image n source).cells ≤ imageBudget n source.size := by
  have inside : AtomImage.SourceWithin n source := fun row member => (valid row member).2
  have count := AtomImage.generate_count source
  have bounded := image_valid_mono n source.size (n+source.size) (AtomImage.generate source)
    (AtomImage.generate_valid n source inside) (by omega) (by omega)
  have stored := AffineForget.Cost.imageSize_bound (n+source.size) (AtomImage.generate source) bounded (by omega)
  have terms := Table.rowTerms_bound n source valid
  have visits := AtomImage.generateVisits_bound n source inside
  have visitBound : AtomImage.generateVisits source ≤ imageVisitsBudget n source.size := by
    apply visits.trans
    unfold imageVisitsBudget
    gcongr
  have tagged : AffineForget.Cost.tagsSize (AtomImage.tagged source) ≤ source.size*n+4*source.size := by
    rw [AffineForget.Cost.tagsSize_eq,AtomImage.tagged_terms]
    simp only [AtomImage.tagged,List.length_ofFn]
    omega
  have tableBound : AffineCollect.tableSize source ≤ source.size*n+2*source.size+1 := by
    rw [AffineCollect.Cost.table_size]
    omega
  change ((AffineForget.Cost.imageRun AtomImage.initial (AtomImage.tagged source)).cells+4*source.size+2)*
    (8*AffineForget.Cost.imageWorkspace (n+source.size)+8)+
      2*(AffineCollect.tableSize source+AffineForget.Cost.tagsSize (AtomImage.tagged source)+
        AffineForget.Cost.imageSize (image n source).value)+7 ≤ _
  rw [AffineForget.Cost.imageRun_cells,image_value]
  have ledger : AtomImage.runVisits AtomImage.initial (AtomImage.tagged source)+4*source.size+2=
      AtomImage.generateVisits source+1 := by unfold AtomImage.generateVisits; omega
  rw [ledger]
  unfold imageBudget
  gcongr

theorem image_prefix_storage (n : Nat) (source : Array Row) (valid : Table.Valid n source) (length : Nat) :
    AffineForget.Cost.imageSize
      (AffineForget.Cost.imageRun AtomImage.initial ((AtomImage.tagged source).take length)).value ≤
        (n+source.size)*(2*(n+source.size)+3)+2 := by
  have inside := AtomImage.tagged_within n source (fun row member => (valid row member).2)
  have known := AtomImage.runFrom_valid n source.size AtomImage.initial
    (by simp [AtomImage.State.Valid,AtomImage.initial]) ((AtomImage.tagged source).take length)
      (fun row member => inside row (List.mem_of_mem_take member))
  have counts := AtomImage.runFrom_count AtomImage.initial ((AtomImage.tagged source).take length)
  have prefixLength : ((AtomImage.tagged source).take length).length ≤ source.size := by
    simp only [List.length_take,AtomImage.tagged,List.length_ofFn]
    omega
  simp only [show AtomImage.initial.basis.length=0 from rfl,
    show AtomImage.initial.kernel.length=0 from rfl,Nat.zero_add] at counts
  rw [AffineForget.Cost.imageRun_value]
  exact AffineForget.Cost.imageSize_bound _ _
    (image_valid_mono n source.size _ _ known (by omega) (by omega)) (by omega)

def flagsFrom (state : ArenaSource.State) (input : Fin state.arena.code.size) (address : Nat) :
    List (Fin state.arena.code.size) → Counted (List Bool)
  | [] => ⟨[],1⟩
  | root::rest =>
      let checked := ArenaCost.eligible state (JointCircuit.proposal state input root address)
      let tail := flagsFrom state input address rest
      ⟨checked.value::tail.value,checked.cells+tail.cells+8*tail.value.length+16⟩

theorem flagsFrom_value (state : ArenaSource.State) (input : Fin state.arena.code.size) (address : Nat)
    (roots : List (Fin state.arena.code.size)) :
    (flagsFrom state input address roots).value=roots.map
      (fun root => ArenaSource.eligible state (JointCircuit.proposal state input root address)) := by
  induction roots <;> simp_all only [flagsFrom,ArenaCost.eligible_value,List.map_nil,List.map_cons]

theorem flagsFrom_cells (state : ArenaSource.State) (input : Fin state.arena.code.size) (address : Nat)
    (roots : List (Fin state.arena.code.size)) :
    (flagsFrom state input address roots).cells ≤ roots.length*(ArenaCost.eligibleBudget state.arena.code.size+8*roots.length+16)+1 := by
  induction roots with
  | nil => simp [flagsFrom]
  | cons root rest ih =>
      have checked := ArenaCost.eligible_cells state (JointCircuit.proposal state input root address)
      simp only [flagsFrom,flagsFrom_value,List.length_map,List.length_cons]
      nlinarith

def independent (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) : Counted (Array Bool) :=
  let flags := flagsFrom frame.state input address frame.ports.toList
  ⟨flags.value.toArray,flags.cells+16*frame.ports.size+16⟩

theorem independent_value (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) :
    (independent frame input address).value=PortRelations.independent frame input address := by
  simp only [independent,flagsFrom_value,PortRelations.independent]
  apply Array.toList_inj.mp
  simp only [Array.toList_map]

def independentBudget (n p : Nat) : Nat := p*(ArenaCost.eligibleBudget n+8*p+16)+16*p+17

theorem independent_cells (frame : Frame) (input : Fin frame.state.arena.code.size) (address : Nat) :
    (independent frame input address).cells ≤ independentBudget frame.state.arena.code.size frame.ports.size := by
  have work := flagsFrom_cells frame.state input address frame.ports.toList
  simp only [Array.length_toList] at work
  simp only [independent,independentBudget]
  omega

def select (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool)
    (coordinates : Array Row) (i : Nat) : Counted (List Row) :=
  let address := if i=0 then input.val else (PortEmbedding.ref frame.state frame.ports (i-1)).val
  let found := AffineClauses.Cost.lookup coordinates.toList address
  let row := if i=0 then found.value else if flags.getD (i-1) false then found.value else Gates.zeroRow
  ⟨[row],found.cells+8*(flags.size+frame.ports.size+rowCells row+1)+16⟩

theorem select_value (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool)
    (coordinates : Array Row) (i : Nat) :
    (select frame input flags coordinates i).value=
      [if i=0 then coordinates.getD input.val Gates.zeroRow else if flags.getD (i-1) false then
        coordinates.getD (PortEmbedding.ref frame.state frame.ports (i-1)).val Gates.zeroRow else Gates.zeroRow] := by
  by_cases zero : i=0 <;> simp [select,zero,AffineClauses.Cost.lookup_value]

theorem select_storage (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool)
    (coordinates : Array Row) (n : Nat) (valid : Table.Valid n coordinates) (i : Nat) :
    rowsCells (select frame input flags coordinates i).value ≤ n+2 := by
  rw [select_value]
  split
  · have bound := Table.row_length_le n _ (Table.read_valid n coordinates valid input.val)
    simp only [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells]
    omega
  · split
    · have bound := Table.row_length_le n _ (Table.read_valid n coordinates valid (PortEmbedding.ref frame.state frame.ports (i-1)).val)
      simp only [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells]
      omega
    · simp [CapacityMatching.RowCost.rowsCells_cons,CapacityMatching.RowCost.rowsCells_nil,rowCells,Gates.zeroRow]

def selectBudget (n p f : Nat) : Nat := 2*n*(n+2)+4*n+4+8*(f+p+n+3)+16

theorem select_cells (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool)
    (coordinates : Array Row) (n : Nat) (valid : Table.Valid n coordinates) (size : coordinates.size=n) (i : Nat) :
    (select frame input flags coordinates i).cells ≤ selectBudget n frame.ports.size flags.size := by
  have storage := AffineClauses.Cost.source_storage n coordinates.toList valid
  have lookup := AffineClauses.Cost.lookup_cells coordinates.toList
    (if i=0 then input.val else (PortEmbedding.ref frame.state frame.ports (i-1)).val)
  have rowBound := Table.row_length_le n _ (AffineClauses.Cost.lookup_valid n coordinates.toList valid
    (if i=0 then input.val else (PortEmbedding.ref frame.state frame.ports (i-1)).val))
  simp only [Array.length_toList,size] at storage lookup
  by_cases zero : i=0
  · simp only [select,zero,if_true,selectBudget,rowCells] at lookup rowBound ⊢
    nlinarith
  · simp only [select,zero,if_false,selectBudget,rowCells] at lookup rowBound ⊢
    split
    · nlinarith
    · simp only [Gates.zeroRow,List.length_nil]; nlinarith

def table (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) : Counted (Array Row) :=
  let coordinates := Table.coordinates frame.state.arena.code.size basis
  let chosen := CapacityMatching.RowCost.gather
    (fun i : Fin (frame.ports.size+1) => select frame input flags coordinates i.val) (List.finRange (frame.ports.size+1))
  ⟨chosen.value.toArray,AffineCollect.coordinateWork frame.state.arena.code.size basis+chosen.cells+
    8*(AffineCollect.tableSize coordinates+rowsCells chosen.value+flags.size+frame.ports.size+1)+16⟩

theorem table_value (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) :
    (table frame input flags basis).value=PortRelations.table frame input flags basis := by
  simp only [table,CapacityMatching.RowCost.gather_value,select_value]
  have flatten {α β : Type} (items : List α) (f : α → β) : items.flatMap (fun i => [f i])=items.map f := by
    induction items <;> simp_all
  rw [flatten]
  apply Array.toList_inj.mp
  simp only [List.finRange,List.map_ofFn,Function.comp_def,PortRelations.table,Array.toList_ofFn]

theorem table_valid (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) :
    Table.Valid frame.state.arena.code.size (table frame input flags basis).value := by
  rw [table_value]
  intro row member
  exact rowValid_mono _ _ row (PortRelations.table_valid frame input flags basis row member) (Table.freeWidth_le _ _)

theorem table_storage (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row) :
    AffineCollect.tableSize (table frame input flags basis).value ≤ (frame.ports.size+1)*(frame.state.arena.code.size+2)+1 := by
  have terms := Table.rowTerms_bound _ _ (table_valid frame input flags basis)
  rw [AffineCollect.Cost.table_size]
  rw [table_value,PortRelations.table_size] at terms ⊢
  nlinarith

def tableBudget (n p f : Nat) : Nat := AffineCollect.Cost.coordinateBudget n+
  (p+1)*(selectBudget n p f+(p+2)*(n+2)+5)+1+
    8*(AffineCarrier.Cost.cellBound n+(p+1)*(n+2)+f+p+1)+16

theorem table_cells (frame : Frame) (input : Fin frame.state.arena.code.size) (flags : Array Bool) (basis : List Row)
    (valid : Triangular basis ∧ RowsWithin frame.state.arena.code.size basis) :
    (table frame input flags basis).cells ≤ tableBudget frame.state.arena.code.size frame.ports.size flags.size := by
  let n := frame.state.arena.code.size
  let coordinates := Table.coordinates n basis
  have tableValid : Table.Valid n coordinates := by
    intro row member
    exact rowValid_mono _ _ row (Table.coordinates_valid n basis row member) (Table.freeWidth_le n basis)
  have size : coordinates.size=n := Table.coordinates_size _ _
  have first := AffineCollect.Cost.coordinate_visits n basis valid
  have storage := AffineCollect.Cost.coordinate_size n basis
  have generated := CapacityMatching.RowCost.gather_cells
    (fun i : Fin (frame.ports.size+1) => select frame input flags coordinates i.val) (List.finRange (frame.ports.size+1))
    (selectBudget n frame.ports.size flags.size) (n+2)
    (fun i _ => select_cells frame input flags coordinates n tableValid size i.val)
    (fun i _ => select_storage frame input flags coordinates n tableValid i.val)
  have output := table_storage frame input flags basis
  simp only [List.length_finRange] at generated
  simp only [table,AffineCollect.tableSize,List.toList_toArray] at output ⊢
  unfold tableBudget
  simp only [AffineCollect.tableSize] at storage
  change rowsCells (CapacityMatching.RowCost.gather
    (fun i : Fin (frame.ports.size+1) => select frame input flags coordinates i.val) (List.finRange (frame.ports.size+1))).value+1 ≤ _ at output
  dsimp only [n,coordinates] at first storage generated output
  simp only [Nat.add_assoc] at generated ⊢
  norm_num only at generated ⊢
  omega

def embedFrom (state : ArenaSource.State) (ports : Array (Fin state.arena.code.size)) : List Node → Counted (List Node)
  | [] => ⟨[],1⟩
  | node::rest =>
      let tail := embedFrom state ports rest
      ⟨PortEmbedding.embed state ports node::tail.value,tail.cells+8*(ports.size+tail.value.length+1)+16⟩

theorem embedFrom_value (state : ArenaSource.State) (ports : Array (Fin state.arena.code.size)) (code : List Node) :
    (embedFrom state ports code).value=code.map (PortEmbedding.embed state ports) := by
  induction code <;> simp_all only [embedFrom,List.map_nil,List.map_cons]

theorem embedFrom_cells (state : ArenaSource.State) (ports : Array (Fin state.arena.code.size)) (code : List Node) :
    (embedFrom state ports code).cells ≤ code.length*(8*(ports.size+code.length+1)+16)+1 := by
  induction code with
  | nil => simp [embedFrom]
  | cons node rest ih =>
      simp only [embedFrom,embedFrom_value,List.length_map,List.length_cons]
      nlinarith

def code (state : ArenaSource.State) (ports : Array (Fin state.arena.code.size)) (body : Fragment) : Counted (Array Node) :=
  let mapped := embedFrom state ports body.code.toList
  ⟨state.arena.code++mapped.value.toArray,mapped.cells+16*(state.arena.code.size+body.code.size+1)+16⟩

theorem code_value (state : ArenaSource.State) (ports : Array (Fin state.arena.code.size)) (body : Fragment) :
    (code state ports body).value=PortEmbedding.code state ports body := by
  simp only [code,embedFrom_value,PortEmbedding.code]
  congr 1
  apply Array.toList_inj.mp
  simp only [Array.toList_map]

def codeBudget (n p b : Nat) : Nat := b*(8*(p+b+1)+16)+1+16*(n+b+1)+16

theorem code_cells (state : ArenaSource.State) (ports : Array (Fin state.arena.code.size)) (body : Fragment) :
    (code state ports body).cells ≤ codeBudget state.arena.code.size ports.size body.code.size := by
  have work := embedFrom_cells state ports body.code.toList
  simp only [Array.length_toList] at work
  simp only [code,codeBudget]
  omega

/-- The sealed emission performs two loads. Both those loads and the paired
measurement execution are covered, together with every old root and relation. -/
def append (frame : Frame) (body : Fragment) : Counted (PortEmbedding.Emission frame.state) :=
  let generated := code frame.state frame.ports body
  let loaded := ArenaCost.Reduction.compact generated.value
  let relations := ArenaCost.remap loaded.value.mapping (ArenaCost.rawRelations frame.state)
  let weight := ArenaCost.lookup loaded.value.mapping frame.state.program.weight.val
  let phase := ArenaCost.lookup loaded.value.mapping frame.state.program.phase.val
  let root := ArenaCost.lookup loaded.value.mapping (frame.state.arena.code.size+body.output.val)
  ⟨PortEmbedding.append frame.state frame.ports body,
    2*(generated.cells+2*loaded.cells+relations.cells+weight.cells+phase.cells+root.cells)+
      48*(frame.state.arena.code.size+body.code.size+frame.state.relations.length+frame.ports.size+1)+64⟩

theorem append_value (frame : Frame) (body : Fragment) :
    (append frame body).value=PortEmbedding.append frame.state frame.ports body := rfl

def appendBudget (n p c b : Nat) : Nat :=
  2*(codeBudget n p b+2*ArenaCost.Reduction.budget (n+b)+c*(4*(n+b)+6*c+24)+1+6*(n+b)+12)+
    48*(n+b+c+p+1)+64

theorem append_cells (frame : Frame) (body : Fragment) :
    (append frame body).cells ≤ appendBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length body.code.size := by
  have first := code_cells frame.state frame.ports body
  have size : (code frame.state frame.ports body).value.size=frame.state.arena.code.size+body.code.size := by
    rw [code_value,PortEmbedding.code_size]
  have loaded := ArenaCost.Reduction.compact_cells (code frame.state frame.ports body).value
  have mapping := ArenaCost.reduction_mapping_size (code frame.state frame.ports body).value
  change (ArenaCost.Reduction.compact (code frame.state frame.ports body).value).value.mapping.size=
    (code frame.state frame.ports body).value.size at mapping
  rw [size] at loaded mapping
  have remapping := ArenaCost.remap_cells
    (ArenaCost.Reduction.compact (code frame.state frame.ports body).value).value.mapping (ArenaCost.rawRelations frame.state)
  rw [mapping] at remapping
  have count : (ArenaCost.rawRelations frame.state).length=frame.state.relations.length := by
    simp only [ArenaCost.rawRelations,List.length_map]
  rw [count] at remapping
  simp only [append,ArenaCost.lookup,mapping,appendBudget]
  omega

def allowed (frame : Frame) (offer : PortRelations.Offer frame) : Counted Bool :=
  let emitted := append frame offer.body
  let item : ArenaSource.Labeled emitted.value.target.arena :=
    ⟨offer.address,⟨emitted.value.ref offer.input,emitted.value.root⟩⟩
  let checked := ArenaCost.eligible emitted.value.target item
  ⟨checked.value,emitted.cells+checked.cells+
    16*(frame.state.arena.code.size+offer.body.code.size+frame.state.relations.length+frame.ports.size+1)+24⟩

theorem allowed_value (frame : Frame) (offer : PortRelations.Offer frame) : (allowed frame offer).value=offer.allowed := by
  simp only [allowed,ArenaCost.eligible_value,append_value,PortRelations.Offer.allowed,PortRelations.Offer.emission,PortRelations.Offer.item]

def allowedBudget (n p c b : Nat) : Nat := appendBudget n p c b+ArenaCost.eligibleBudget (n+b+1)+16*(n+b+c+p+1)+24

theorem eligibleBudget_mono (n N : Nat) (bound : n ≤ N) : ArenaCost.eligibleBudget n ≤ ArenaCost.eligibleBudget N := by
  unfold ArenaCost.eligibleBudget ArenaCost.Dependency.budget ArenaCost.inputsBudget
  gcongr

theorem allowed_cells (frame : Frame) (offer : PortRelations.Offer frame) :
    (allowed frame offer).cells ≤ allowedBudget frame.state.arena.code.size frame.ports.size frame.state.relations.length offer.body.code.size := by
  have emitted := append_cells frame offer.body
  have size := PortEmbedding.append_size frame.state frame.ports offer.body
  have checked := (ArenaCost.eligible_cells offer.emission.target offer.item).trans
    (eligibleBudget_mono _ _ size)
  simp only [allowed,append_value,allowedBudget]
  simp only [PortRelations.Offer.item,PortRelations.Offer.emission] at checked
  omega

end SaturationMonoid.ComplexityProjection.SATSource.PortCost

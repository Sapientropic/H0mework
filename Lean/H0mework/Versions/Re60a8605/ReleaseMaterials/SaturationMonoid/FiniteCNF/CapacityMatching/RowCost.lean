import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.SourceTight

/-!
The paired renderer consumes the actual source setup and tight-family run.
Its ledger includes source addressing, membership, paid parity normalization,
and full row/append-copy allowances. Counter evaluation and bit-level machine
implementations remain separate.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.RowCost

open SaturationMonoid.ComplexityProjection.SATSource.Affine
open InterferenceProgram

def rowCells (row : Row) : Nat := row.vars.length+2
def rowsCells (rows : List Row) : Nat := (rows.map rowCells).sum

@[simp] theorem rowsCells_nil : rowsCells [] = 0 := rfl
@[simp] theorem rowsCells_cons (row : Row) (rows : List Row) :
    rowsCells (row::rows) = rowCells row+rowsCells rows := rfl
@[simp] theorem rowsCells_append (left right : List Row) :
    rowsCells (left++right) = rowsCells left+rowsCells right := by simp [rowsCells]

def append (left right : List Row) : SourceCost.Counted (List Row) :=
  ⟨left++right,2*rowsCells left+2*rowsCells right+5⟩

def gather {α : Type} (act : α → SourceCost.Counted (List Row)) : List α → SourceCost.Counted (List Row)
  | [] => ⟨[],1⟩
  | item::rest =>
      let first := act item
      let tail := gather act rest
      let joined := append first.value tail.value
      ⟨joined.value,first.cells+tail.cells+joined.cells⟩

theorem gather_value {α : Type} (act : α → SourceCost.Counted (List Row)) (items : List α) :
    (gather act items).value = items.flatMap (fun item => (act item).value) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [gather,append,List.flatMap_cons,ih]

theorem gather_storage {α : Type} (act : α → SourceCost.Counted (List Row)) (items : List α)
    (size : Nat) (bound : ∀ item ∈ items, rowsCells (act item).value ≤ size) :
    rowsCells (gather act items).value ≤ items.length*size := by
  induction items with
  | nil => simp [gather]
  | cons item rest ih =>
      have first := bound item (by simp)
      have tail := ih (fun other member => bound other (by simp [member]))
      simp only [gather,append,rowsCells_append,List.length_cons]
      nlinarith

theorem gather_cells {α : Type} (act : α → SourceCost.Counted (List Row)) (items : List α)
    (cost size : Nat) (time : ∀ item ∈ items, (act item).cells ≤ cost)
    (space : ∀ item ∈ items, rowsCells (act item).value ≤ size) :
    (gather act items).cells ≤ items.length*(cost+(items.length+1)*size+5)+1 := by
  induction items with
  | nil => simp [gather]
  | cons item rest ih =>
      have first := time item (by simp)
      have firstSpace := space item (by simp)
      have tailSpace := gather_storage act rest size (fun other member => space other (by simp [member]))
      have tail := ih (fun other member => time other (by simp [member]))
        (fun other member => space other (by simp [member]))
      simp only [gather,append,List.length_cons]
      nlinarith

def normalize (row : Row) : SourceCost.Counted Row :=
  let result := row.normalize
  ⟨result,Table.mergeVisits row.vars []+2*rowCells result+2⟩

theorem normalize_valid (n : Nat) (row : Row) (inside : Parity.Within n row.vars) :
    Table.RowValid n (normalize row).value :=
  ⟨row.normalize_nodup,Row.normalize_within n row inside⟩

theorem normalize_storage (n : Nat) (row : Row) (inside : Parity.Within n row.vars) :
    rowCells (normalize row).value ≤ n+2 :=
  Nat.add_le_add_right (Table.row_length_le n _ (normalize_valid n row inside)) 2

theorem normalize_cells (n : Nat) (row : Row) (inside : Parity.Within n row.vars) :
    (normalize row).cells ≤ row.vars.length*(2*n+5)+2*n+7 := by
  have merged := Table.mergeVisits_bound n row.vars [] inside (by simp) (by simp [Parity.Within])
  have stored := normalize_storage n row inside
  simp only [normalize]
  change Table.mergeVisits row.vars []+2*rowCells (normalize row).value+2 ≤ _
  omega

private theorem group_length {α : Type} (data : List (List α)) (j : Fin data.length) :
    (data.get j).length ≤ data.flatten.length := by
  rw [List.length_flatten]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨data.get j,List.get_mem _ _,rfl⟩)

def groupRow {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) : SourceCost.Counted Row :=
  let group := data.get j
  let result := normalize ⟨group.map (fun item => item.literal.val),true⟩
  ⟨result.value,result.cells+j.val+1+6*group.length+2⟩

theorem groupRow_value {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) :
    (groupRow data j).value = SourceTight.groupRow data j := rfl

theorem groupRow_valid {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) :
    Table.RowValid n (groupRow data j).value := by
  apply normalize_valid
  intro i member
  obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
  exact item.literal.isLt

theorem groupRow_storage {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) :
    rowCells (groupRow data j).value ≤ n+2 :=
  Nat.add_le_add_right (Table.row_length_le n _ (groupRow_valid data j)) 2

def groupBudget (n groups items : Nat) : Nat := items*(2*n+11)+groups+2*n+10

theorem groupRow_cells {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) :
    (groupRow data j).cells ≤ groupBudget n data.length data.flatten.length := by
  have inside : Parity.Within n ((data.get j).map (fun item => item.literal.val)) := by
    intro i member
    obtain ⟨item,_,rfl⟩ := List.mem_map.mp member
    exact item.literal.isLt
  have normalized := normalize_cells n ⟨(data.get j).map (fun item => item.literal.val),true⟩ inside
  simp only [List.length_map] at normalized
  have size := group_length data j
  have address := j.isLt
  simp only [groupRow,groupBudget]
  nlinarith

def ownerScan {d : Nat} (owner : Fin d) : List (Fin d) → SourceCost.Counted Bool
  | [] => ⟨false,1⟩
  | i::rest =>
      if owner == i then ⟨true,2⟩
      else let tail := ownerScan owner rest; ⟨tail.value,tail.cells+2⟩

theorem ownerScan_value {d : Nat} (owner : Fin d) (demands : List (Fin d)) :
    (ownerScan owner demands).value = decide (owner ∈ demands) := by
  induction demands with
  | nil => rfl
  | cons i rest ih => simp only [ownerScan,List.mem_cons]; split <;> simp_all

theorem ownerScan_cells {d : Nat} (owner : Fin d) (demands : List (Fin d)) :
    (ownerScan owner demands).cells ≤ 2*demands.length+1 := by
  induction demands with
  | nil => rfl
  | cons i rest ih => simp only [ownerScan,List.length_cons]; split <;> simp only <;> omega

def outsideGroup {n d : Nat} (demands : List (Fin d)) : List (Source.Item n d) → SourceCost.Counted (List Row)
  | [] => ⟨[],1⟩
  | item::rest =>
      let found := ownerScan item.demand demands
      let tail := outsideGroup demands rest
      if found.value then ⟨tail.value,found.cells+tail.cells+2*rowsCells tail.value+4⟩
      else ⟨⟨[item.literal.val],false⟩::tail.value,found.cells+tail.cells+2*rowsCells tail.value+10⟩

theorem outsideGroup_value {n d : Nat} (demands : List (Fin d)) (items : List (Source.Item n d)) :
    (outsideGroup demands items).value = items.filterMap (fun item =>
      if item.demand ∈ demands then none else some (⟨[item.literal.val],false⟩ : Row)) := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [outsideGroup,ownerScan_value,List.filterMap_cons]; split <;> simp_all

theorem outsideGroup_storage {n d : Nat} (demands : List (Fin d)) (items : List (Source.Item n d)) :
    rowsCells (outsideGroup demands items).value ≤ 3*items.length := by
  induction items with
  | nil => simp [outsideGroup]
  | cons item rest ih =>
      simp only [outsideGroup,List.length_cons]
      split <;> simp only [rowsCells_cons,rowCells,List.length_cons,List.length_nil] <;> omega

theorem outsideGroup_cells {n d : Nat} (demands : List (Fin d)) (items : List (Source.Item n d)) :
    (outsideGroup demands items).cells ≤ items.length*(2*demands.length+6*items.length+13)+1 := by
  induction items with
  | nil => simp [outsideGroup]
  | cons item rest ih =>
      have first := ownerScan_cells item.demand demands
      have stored := outsideGroup_storage demands rest
      simp only [outsideGroup,List.length_cons]
      split <;> simp only <;> nlinarith

def outsideAt {n d : Nat} (data : List (List (Source.Item n d))) (demands : List (Fin d))
    (j : Fin data.length) : SourceCost.Counted (List Row) :=
  let group := data.get j
  let rendered := outsideGroup demands group
  ⟨rendered.value,rendered.cells+j.val+1+4*group.length+2⟩

theorem outsideAt_storage {n d : Nat} (data : List (List (Source.Item n d))) (demands : List (Fin d))
    (j : Fin data.length) : rowsCells (outsideAt data demands j).value ≤ 3*data.flatten.length :=
  (outsideGroup_storage demands (data.get j)).trans (Nat.mul_le_mul_left 3 (group_length data j))

def outsideBudget (groups items demands : Nat) : Nat := items*(2*demands+6*items+17)+groups+3

theorem outsideAt_cells {n d : Nat} (data : List (List (Source.Item n d))) (demands : List (Fin d))
    (j : Fin data.length) : (outsideAt data demands j).cells ≤ outsideBudget data.length data.flatten.length demands.length := by
  have first := outsideGroup_cells demands (data.get j)
  have size := group_length data j
  have address := j.isLt
  have mono : (data.get j).length*(2*demands.length+6*(data.get j).length+17) ≤
      data.flatten.length*(2*demands.length+6*data.flatten.length+17) := by gcongr
  simp only [outsideAt,outsideBudget]
  nlinarith

def singleGroup {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) : SourceCost.Counted (List Row) :=
  let result := groupRow data j
  ⟨[result.value],result.cells+1⟩

def outsideRows {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) : SourceCost.Counted (List Row) :=
  gather (outsideAt data value.demands) value.groups

theorem outsideRows_value {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) :
    (outsideRows data value).value = SourceTight.outsideRows data value := by
  simp only [outsideRows,gather_value,outsideAt,outsideGroup_value,SourceTight.outsideRows]

def one {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) : SourceCost.Counted (List Row) :=
  let groups := gather (singleGroup data) value.groups
  let outside := outsideRows data value
  let joined := append groups.value outside.value
  ⟨joined.value,groups.cells+outside.cells+joined.cells⟩

theorem one_value {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) :
    (one data value).value = SourceTight.one data value := by
  simp only [one,append,gather_value,singleGroup,groupRow_value,outsideRows_value,SourceTight.one]
  simp
  induction value.groups <;> simp_all

theorem singleGroup_storage {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) :
    rowsCells (singleGroup data j).value ≤ n+2 := by
  simpa only [singleGroup,rowsCells_cons,rowsCells_nil,Nat.add_zero] using groupRow_storage data j

theorem singleGroup_cells {n d : Nat} (data : List (List (Source.Item n d))) (j : Fin data.length) :
    (singleGroup data j).cells ≤ groupBudget n data.length data.flatten.length+1 :=
  Nat.add_le_add_right (groupRow_cells data j) 1

theorem one_storage {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) :
    rowsCells (one data value).value ≤ value.groups.length*(n+2+3*data.flatten.length) := by
  have groups := gather_storage (singleGroup data) value.groups (n+2) (fun j _ => singleGroup_storage data j)
  have outside := gather_storage (outsideAt data value.demands) value.groups (3*data.flatten.length)
    (fun j _ => outsideAt_storage data value.demands j)
  simp only [one,append,rowsCells_append,outsideRows]
  nlinarith

def oneBudget (n groups items selected demands : Nat) : Nat :=
  selected*(groupBudget n groups items+outsideBudget groups items demands+
    (selected+3)*(n+2+3*items)+12)+7

theorem one_cells {n d : Nat} (data : List (List (Source.Item n d))) (value : Cut d data.length) :
    (one data value).cells ≤ oneBudget n data.length data.flatten.length value.groups.length value.demands.length := by
  have groups := gather_cells (singleGroup data) value.groups
    (groupBudget n data.length data.flatten.length+1) (n+2)
    (fun j _ => singleGroup_cells data j) (fun j _ => singleGroup_storage data j)
  have groupSize := gather_storage (singleGroup data) value.groups (n+2) (fun j _ => singleGroup_storage data j)
  have outside := gather_cells (outsideAt data value.demands) value.groups
    (outsideBudget data.length data.flatten.length value.demands.length) (3*data.flatten.length)
    (fun j _ => outsideAt_cells data value.demands j) (fun j _ => outsideAt_storage data value.demands j)
  have outsideSize := gather_storage (outsideAt data value.demands) value.groups (3*data.flatten.length)
    (fun j _ => outsideAt_storage data value.demands j)
  simp only [one,append,outsideRows,oneBudget]
  nlinarith

def render {n d : Nat} (data : List (List (Source.Item n d))) (values : List (Cut d data.length)) :
    SourceCost.Counted (List Row) := gather (one data) values

theorem render_value {n d : Nat} (data : List (List (Source.Item n d))) (values : List (Cut d data.length)) :
    (render data values).value = values.flatMap (SourceTight.one data) := by simp [render,gather_value,one_value]

theorem render_cells {n d : Nat} (data : List (List (Source.Item n d))) (values : List (Cut d data.length))
    (selected demands : Nat)
    (bound : ∀ value ∈ values, value.groups.length ≤ selected ∧ value.demands.length ≤ demands) :
    (render data values).cells ≤ values.length*(oneBudget n data.length data.flatten.length selected demands+
      (values.length+1)*(selected*(n+2+3*data.flatten.length))+5)+1 := by
  apply gather_cells
  · intro value member
    obtain ⟨groups,owners⟩ := bound value member
    apply (one_cells data value).trans
    unfold oneBudget outsideBudget
    gcongr
  · intro value member
    exact (one_storage data value).trans (Nat.mul_le_mul_right _ (bound value member).1)

theorem render_storage {n d : Nat} (data : List (List (Source.Item n d))) (values : List (Cut d data.length))
    (selected : Nat) (bound : ∀ value ∈ values, value.groups.length ≤ selected) :
    rowsCells (render data values).value ≤ values.length*(selected*(n+2+3*data.flatten.length)) := by
  apply gather_storage
  intro value member
  exact (one_storage data value).trans (Nat.mul_le_mul_right _ (bound value member))

def rows {n : Nat} (formula : CNFFormula n) : SourceCost.Counted (List Row) :=
  let prepared := SourceCost.setup formula
  let found := TightCost.run prepared.graph
  let rendered := render prepared.data found.value
  ⟨rendered.value,prepared.cells+found.cells+rendered.cells+4⟩

theorem rows_value {n : Nat} (formula : CNFFormula n) : (rows formula).value = SourceTight.rows formula := by
  simp only [rows,render_value,SourceTight.rows]

theorem setup_item_count {n : Nat} (formula : CNFFormula n) :
    (SourceCost.setup formula).data.flatten.length ≤ Extract.literalCount formula := by
  rw [SourceCost.setup_data,(Source.partition_perm formula _).length_eq]
  have length := congrArg List.length (Source.tags_erase (SourceCost.setup formula).rows)
  simp only [List.length_map] at length
  rw [length,SourceCost.setup_rows]
  exact Capacity.positives_literals formula

theorem tight_dimensions {m r : Nat} (graph : Graph m r) (value : Cut m r)
    (member : value ∈ (TightCost.run graph).value) : value.groups.length ≤ r ∧ value.demands.length ≤ m := by
  have correct := TightCost.run_correct graph value member
  constructor
  · rw [correct.2.1]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  · simpa only [Fintype.card_fin] using correct.1.length_le_card

def renderBudget (n demands items : Nat) : Nat :=
  items*(oneBudget n items items items demands+(items+1)*(items*(n+2+3*items))+5)+1

def rowsBudget (n demands items : Nat) : Nat :=
  SourceCost.setupBound demands items+TightCost.runBudget demands items+renderBudget n demands items+4

theorem rows_cells {n : Nat} (formula : CNFFormula n) :
    (rows formula).cells ≤ rowsBudget n formula.length (Extract.literalCount formula) := by
  let prepared := SourceCost.setup formula
  let found := (TightCost.run prepared.graph).value
  obtain ⟨demands,groups⟩ := SourceCost.setup_dimensions formula
  have items := setup_item_count formula
  have count : found.length ≤ Extract.literalCount formula := (TightCost.run_length prepared.graph).trans groups
  have dimensions : ∀ value ∈ found, value.groups.length ≤ Extract.literalCount formula ∧ value.demands.length ≤ formula.length := by
    intro value member
    have shape := tight_dimensions prepared.graph value member
    exact ⟨shape.1.trans groups,shape.2.trans demands⟩
  have original := SourceCost.setup_cells formula
  change prepared.cells ≤ SourceCost.setupBound formula.length (Extract.literalCount formula) at original
  have probing := TightCost.run_cells prepared.graph
  have writing := render_cells prepared.data found (Extract.literalCount formula) formula.length dimensions
  have probeBound : (TightCost.run prepared.graph).cells ≤ TightCost.runBudget formula.length (Extract.literalCount formula) := by
    apply probing.trans
    unfold TightCost.runBudget TightCost.probeBudget TightCost.generateBudget solveUnits roundUnits
    gcongr
  have renderBound : (render prepared.data found).cells ≤ renderBudget n formula.length (Extract.literalCount formula) := by
    apply writing.trans
    unfold renderBudget oneBudget groupBudget outsideBudget
    gcongr
  change prepared.cells+(TightCost.run prepared.graph).cells+(render prepared.data found).cells+4 ≤ _
  unfold rowsBudget
  omega

theorem rows_storage {n : Nat} (formula : CNFFormula n) :
    rowsCells (rows formula).value ≤ Extract.literalCount formula*Extract.literalCount formula*(n+2+3*Extract.literalCount formula) := by
  let prepared := SourceCost.setup formula
  let found := (TightCost.run prepared.graph).value
  have groups := (SourceCost.setup_dimensions formula).2
  have items := setup_item_count formula
  have count : found.length ≤ Extract.literalCount formula := (TightCost.run_length prepared.graph).trans groups
  have writing := render_storage prepared.data found (Extract.literalCount formula)
    (fun value member => (tight_dimensions prepared.graph value member).1.trans groups)
  change rowsCells (render prepared.data found).value ≤ _
  apply writing.trans
  rw [Nat.mul_assoc]
  gcongr

def plainRow {n : Nat} (group : List (Fin n)) : SourceCost.Counted (List Row) :=
  let written := normalize ⟨group.map (·.val),true⟩
  ⟨[written.value],written.cells+4*group.length+3⟩

theorem plainRow_storage {n : Nat} (group : List (Fin n)) :
    rowsCells (plainRow group).value ≤ n+2 := by
  apply normalize_storage
  intro i member
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
  exact j.isLt

theorem plainRow_cells {n : Nat} (group : List (Fin n)) :
    (plainRow group).cells ≤ group.length*(2*n+9)+2*n+10 := by
  have bound := normalize_cells n ⟨group.map (·.val),true⟩ (by
    intro i member
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp member
    exact j.isLt)
  simp only [List.length_map] at bound
  simp only [plainRow]
  nlinarith

def capacityRender {n : Nat} (demands : List (List (Fin n)))
    (data : List (List (Source.Item n demands.length))) : SourceCost.Counted (List Row) :=
  let groups := Source.erase data
  let copied := 8*data.flatten.length+4*demands.flatten.length+8*(data.length+demands.length)+20
  if groups.length < demands.length then ⟨[⟨[],true⟩],copied+4⟩
  else if demands.length = groups.length then
    let written := gather plainRow (groups++demands)
    ⟨written.value,copied+written.cells+3⟩
  else ⟨[],copied+1⟩

theorem capacityRender_value {n : Nat} (formula : CNFFormula n) :
    (capacityRender (SourceCost.setup formula).rows (SourceCost.setup formula).data).value =
      Capacity.relations formula := by
  have erased : Source.erase (SourceCost.setup formula).data =
      Capacity.partition formula (Capacity.positives formula).flatten := by
    rw [SourceCost.setup_data,Source.partition_erase,Source.tags_erase,SourceCost.setup_rows]
  simp only [capacityRender,erased,SourceCost.setup_rows,Capacity.relations]
  split
  · rfl
  · split
    · simp only [gather_value,plainRow,normalize]
      induction Capacity.partition formula (Capacity.positives formula).flatten ++ Capacity.positives formula <;> simp_all
    · rfl

private theorem erase_lengths {n d : Nat} (data : List (List (Source.Item n d))) :
    (Source.erase data).length = data.length ∧ (Source.erase data).flatten.length = data.flatten.length := by
  constructor
  · simp [Source.erase]
  · simp [Source.erase,List.length_flatten,List.map_map,Function.comp_def]

def capacityBudget (n demands groups items : Nat) : Nat :=
  12*items+8*(groups+demands)+25+
    (groups+demands)*(items*(2*n+9)+2*n+10+(groups+demands+1)*(n+2)+5)+1

theorem capacityRender_cells {n : Nat} (demands : List (List (Fin n)))
    (data : List (List (Source.Item n demands.length))) (items : Nat)
    (groupSize : data.flatten.length ≤ items) (demandSize : demands.flatten.length ≤ items) :
    (capacityRender demands data).cells ≤ capacityBudget n demands.length data.length items := by
  obtain ⟨groupCount,groupItems⟩ := erase_lengths data
  have groupBound (group : List (Fin n)) (member : group ∈ Source.erase data ++ demands) : group.length ≤ items := by
    rcases List.mem_append.mp member with left | right
    · rw [← groupItems] at groupSize
      exact (List.le_sum_of_mem (List.mem_map.mpr ⟨group,left,rfl⟩)).trans (by simpa [List.length_flatten] using groupSize)
    · exact (List.le_sum_of_mem (List.mem_map.mpr ⟨group,right,rfl⟩)).trans (by simpa [List.length_flatten] using demandSize)
  have writing := gather_cells (@plainRow n) (Source.erase data++demands)
    (items*(2*n+9)+2*n+10) (n+2)
    (fun group member => (plainRow_cells group).trans (by gcongr; exact groupBound group member))
    (fun group _ => plainRow_storage group)
  simp only [List.length_append,groupCount] at writing
  simp only [capacityRender,capacityBudget]
  split
  · simp only; omega
  · split <;> simp only <;> omega

theorem capacityRender_storage {n : Nat} (demands : List (List (Fin n)))
    (data : List (List (Source.Item n demands.length))) :
    rowsCells (capacityRender demands data).value ≤ (data.length+demands.length)*(n+2)+2 := by
  have bound := gather_storage (@plainRow n) (Source.erase data++demands) (n+2)
    (fun group _ => plainRow_storage group)
  simp only [List.length_append,(erase_lengths data).1] at bound
  simp only [capacityRender]
  split
  · simp [rowsCells,rowCells]
  · split <;> simp only [rowsCells_nil] <;> omega

/-- The expanded source is partitioned and matched once; both kinds of rows use that same table. -/
def both {n : Nat} (formula : CNFFormula n) : SourceCost.Counted (List Row × List Row) :=
  let prepared := SourceCost.setup formula
  let found := TightCost.run prepared.graph
  let written := render prepared.data found.value
  let previous := capacityRender prepared.rows prepared.data
  ⟨(previous.value,written.value),prepared.cells+found.cells+written.cells+4+previous.cells+3⟩

theorem both_value {n : Nat} (formula : CNFFormula n) :
    (both formula).value = (Capacity.relations formula,SourceTight.rows formula) := by
  simp only [both,capacityRender_value,render_value,SourceTight.rows]

def bothBudget (n demands items : Nat) : Nat :=
  rowsBudget n demands items+capacityBudget n demands items items+3

theorem both_cells {n : Nat} (formula : CNFFormula n) :
    (both formula).cells ≤ bothBudget n formula.length (Extract.literalCount formula) := by
  have current := rows_cells formula
  obtain ⟨demands,groups⟩ := SourceCost.setup_dimensions formula
  have demandItems : (SourceCost.setup formula).rows.flatten.length ≤ Extract.literalCount formula := by
    rw [SourceCost.setup_rows]
    exact Capacity.positives_literals formula
  have previous := capacityRender_cells (SourceCost.setup formula).rows (SourceCost.setup formula).data
    (Extract.literalCount formula) (setup_item_count formula) demandItems
  have bound : (capacityRender (SourceCost.setup formula).rows (SourceCost.setup formula).data).cells ≤
      capacityBudget n formula.length (Extract.literalCount formula) (Extract.literalCount formula) := by
    apply previous.trans
    unfold capacityBudget
    gcongr
  change (rows formula).cells+(capacityRender (SourceCost.setup formula).rows (SourceCost.setup formula).data).cells+3 ≤ _
  unfold bothBudget
  omega

def previousStorage (n demands items : Nat) : Nat := (items+demands)*(n+2)+2
def currentStorage (n items : Nat) : Nat := items*items*(n+2+3*items)

theorem both_storage {n : Nat} (formula : CNFFormula n) :
    rowsCells (both formula).value.1 ≤ previousStorage n formula.length (Extract.literalCount formula) ∧
    rowsCells (both formula).value.2 ≤ currentStorage n (Extract.literalCount formula) := by
  constructor
  · have bound := capacityRender_storage (SourceCost.setup formula).rows (SourceCost.setup formula).data
    obtain ⟨demands,groups⟩ := SourceCost.setup_dimensions formula
    apply bound.trans
    unfold previousStorage
    gcongr
  · exact rows_storage formula

private theorem rows_length_le_cells (values : List Row) : values.length ≤ rowsCells values := by
  induction values with
  | nil => rfl
  | cons row rest ih => simp only [List.length_cons,rowsCells_cons,rowCells]; omega

private theorem row_le_cells (row : Row) (values : List Row) (member : row ∈ values) :
    rowCells row ≤ rowsCells values := List.le_sum_of_mem (List.mem_map.mpr ⟨row,member,rfl⟩)

theorem table_storage (n : Nat) (table : Array Row) (valid : Table.Valid n table) :
    rowsCells table.toList ≤ table.size*(n+2) := by
  have bound : ∀ values : List Row, (∀ row ∈ values, Table.RowValid n row) → rowsCells values ≤ values.length*(n+2) := by
    intro values contained
    induction values with
    | nil => simp
    | cons row rest ih =>
        have first := Table.row_length_le n row (contained row (by simp))
        have tail := ih (fun other member => contained other (by simp [member]))
        simp only [rowsCells_cons,rowCells,List.length_cons]
        nlinarith
  simpa only [Array.length_toList] using bound table.toList valid

def decodeOne (table : Array Row) (row : Row) : SourceCost.Counted (List Row) :=
  let result := Table.combine table row.vars ⟨[],row.rhs⟩
  ⟨[result],Table.combineVisits table row.vars ⟨[],row.rhs⟩+
    row.vars.length*(4*rowsCells table.toList+4*table.size+12)+2*rowCells result+4⟩

theorem decodeOne_storage (n : Nat) (table : Array Row) (valid : Table.Valid n table) (row : Row) :
    rowsCells (decodeOne table row).value ≤ n+2 := by
  have generated := Table.combine_valid n table valid row.vars ⟨[],row.rhs⟩
    (by simp [Table.RowValid,Parity.Within])
  simpa only [decodeOne,rowsCells_cons,rowsCells_nil,Nat.add_zero,rowCells] using
    Nat.add_le_add_right (Table.row_length_le n _ generated) 2

def decodeUnit (n size : Nat) : Nat := n*(2*n+5)+4*size*(n+2)+4*size+2*n+24

theorem decodeOne_cells (n : Nat) (table : Array Row) (valid : Table.Valid n table) (row : Row) :
    (decodeOne table row).cells ≤ (row.vars.length+1)*decodeUnit n table.size := by
  have visits := Table.combineVisits_bound n table valid row.vars ⟨[],row.rhs⟩
    (by simp [Table.RowValid,Parity.Within])
  have source := table_storage n table valid
  have result := decodeOne_storage n table valid row
  simp only [decodeOne,rowsCells_cons,rowsCells_nil,Nat.add_zero] at result ⊢
  unfold decodeUnit
  nlinarith

def decodeRows (table : Array Row) (values : List Row) : SourceCost.Counted (List Row) := gather (decodeOne table) values

theorem decodeRows_value (table : Array Row) (values : List Row) :
    (decodeRows table values).value = values.map (fun row => Table.combine table row.vars ⟨[],row.rhs⟩) := by
  simp only [decodeRows,gather_value,decodeOne]
  induction values <;> simp_all

def decodeBudget (n size storage : Nat) : Nat :=
  storage*((storage+1)*decodeUnit n size+(storage+1)*(n+2)+5)+1

theorem decodeRows_cells (n : Nat) (table : Array Row) (valid : Table.Valid n table) (values : List Row) :
    (decodeRows table values).cells ≤ decodeBudget n table.size (rowsCells values) := by
  have length := rows_length_le_cells values
  have writing := gather_cells (decodeOne table) values
    ((rowsCells values+1)*decodeUnit n table.size) (n+2)
    (fun row member => (decodeOne_cells n table valid row).trans (by
      have bound := row_le_cells row values member
      simp only [rowCells] at bound
      gcongr
      omega))
    (fun row _ => decodeOne_storage n table valid row)
  apply writing.trans
  unfold decodeBudget
  gcongr

theorem decodeRows_storage (n : Nat) (table : Array Row) (valid : Table.Valid n table) (values : List Row) :
    rowsCells (decodeRows table values).value ≤ rowsCells values*(n+2) :=
  (gather_storage (decodeOne table) values (n+2) (fun row _ => decodeOne_storage n table valid row)).trans
    (Nat.mul_le_mul_right _ (rows_length_le_cells values))

def formulaCells {n : Nat} (formula : CNFFormula n) : Nat := 3*Extract.literalCount formula+2*formula.length+1

def expand {n : Nat} (formula : CNFFormula n) : SourceCost.Counted (CNFFormula (n+n)) :=
  let positive := SignedCapacity.demands formula
  let negative := SignedCapacity.exclusions formula
  let cover := SignedCapacity.covers n
  let disjoint := SignedCapacity.disjoint n
  let first := positive++negative
  let second := first++cover
  ⟨second++disjoint,12*Extract.literalCount formula+8*formula.length+24*n+8+
    2*(formulaCells positive+formulaCells negative+formulaCells first+formulaCells cover+
      formulaCells second+formulaCells disjoint)+9⟩

theorem expand_value {n : Nat} (formula : CNFFormula n) : (expand formula).value = SignedCapacity.expand formula := rfl

theorem expand_cells {n : Nat} (formula : CNFFormula n) :
    (expand formula).cells ≤ 80*(Extract.literalCount formula+formula.length+n+1) := by
  simp [expand,formulaCells,SignedCapacity.demands,SignedCapacity.exclusions,SignedCapacity.covers,
    SignedCapacity.disjoint,Extract.literalCount,List.map_map,Function.comp_def]
  have same : (formula.map (fun clause => clause.length)).sum = (formula.map List.length).sum := rfl
  omega

def coordinates (n : Nat) : SourceCost.Counted (Array Row) :=
  let table := SignedCapacity.coordinates n
  ⟨table,2*rowsCells table.toList+(table.size+1)*(2*rowsCells table.toList+6)+2⟩

def coordinateBudget (n : Nat) : Nat :=
  2*((n+n)*(n+2))+(n+n+1)*(2*((n+n)*(n+2))+6)+2

theorem coordinates_cells (n : Nat) : (coordinates n).cells ≤ coordinateBudget n := by
  have stored := table_storage n (SignedCapacity.coordinates n) (SignedCapacity.coordinates_valid n)
  have size : (SignedCapacity.coordinates n).size = n+n := by simp [SignedCapacity.coordinates]
  simp only [size] at stored
  simp only [coordinates,size,coordinateBudget]
  gcongr

def prepare {n : Nat} (formula : CNFFormula n) : SourceCost.Counted (List Row) :=
  let transformed := expand formula
  let generated := both transformed.value
  let original := rows formula
  let table := coordinates n
  let previous := decodeRows table.value generated.value.1
  let mixed := decodeRows table.value generated.value.2
  let first := append previous.value original.value
  let full := append first.value mixed.value
  ⟨full.value,transformed.cells+generated.cells+original.cells+table.cells+
    previous.cells+mixed.cells+first.cells+full.cells+8⟩

theorem prepare_value {n : Nat} (formula : CNFFormula n) :
    (prepare formula).value = SourceTight.prepare formula := by
  simp only [prepare,append,expand_value,both_value,rows_value,decodeRows_value,coordinates,
    SourceTight.prepare,SignedCapacity.relations]
  rfl

def prepareStorage (n demands items : Nat) : Nat :=
  previousStorage (n+n) (2*demands+2*n) (2*items+4*n)*(n+2)+currentStorage n items+
    currentStorage (n+n) (2*items+4*n)*(n+2)

def prepareBudget (n demands items : Nat) : Nat :=
  80*(items+demands+n+1)+bothBudget (n+n) (2*demands+2*n) (2*items+4*n)+
    rowsBudget n demands items+coordinateBudget n+
    decodeBudget n (n+n) (previousStorage (n+n) (2*demands+2*n) (2*items+4*n))+
    decodeBudget n (n+n) (currentStorage (n+n) (2*items+4*n))+
    4*(previousStorage (n+n) (2*demands+2*n) (2*items+4*n)*(n+2)+currentStorage n items)+
    2*(currentStorage (n+n) (2*items+4*n)*(n+2))+18

theorem prepare_storage {n : Nat} (formula : CNFFormula n) :
    rowsCells (prepare formula).value ≤ prepareStorage n formula.length (Extract.literalCount formula) := by
  let generated := (both (SignedCapacity.expand formula)).value
  let table := SignedCapacity.coordinates n
  have previous := decodeRows_storage n table (SignedCapacity.coordinates_valid n) generated.1
  have mixed := decodeRows_storage n table (SignedCapacity.coordinates_valid n) generated.2
  obtain ⟨before,after⟩ := both_storage (SignedCapacity.expand formula)
  simp only [SignedCapacity.expand_length,SignedCapacity.expand_literals] at before after
  have original := rows_storage formula
  simp only [prepare,append,rowsCells_append,expand_value,coordinates]
  unfold prepareStorage currentStorage at *
  dsimp only [generated,table] at previous mixed
  nlinarith

theorem prepare_cells {n : Nat} (formula : CNFFormula n) :
    (prepare formula).cells ≤ prepareBudget n formula.length (Extract.literalCount formula) := by
  let generated := (both (SignedCapacity.expand formula)).value
  let table := SignedCapacity.coordinates n
  have tableSize : table.size = n+n := by simp [table,SignedCapacity.coordinates]
  have generatedCells := both_cells (SignedCapacity.expand formula)
  rw [SignedCapacity.expand_length,SignedCapacity.expand_literals] at generatedCells
  obtain ⟨before,after⟩ := both_storage (SignedCapacity.expand formula)
  simp only [SignedCapacity.expand_length,SignedCapacity.expand_literals] at before after
  have previous := decodeRows_cells n table (SignedCapacity.coordinates_valid n) generated.1
  have mixed := decodeRows_cells n table (SignedCapacity.coordinates_valid n) generated.2
  have previousBound : (decodeRows table generated.1).cells ≤
      decodeBudget n (n+n) (previousStorage (n+n) (2*formula.length+2*n) (2*Extract.literalCount formula+4*n)) := by
    apply previous.trans
    rw [tableSize]
    unfold decodeBudget
    gcongr
  have mixedBound : (decodeRows table generated.2).cells ≤
      decodeBudget n (n+n) (currentStorage (n+n) (2*Extract.literalCount formula+4*n)) := by
    apply mixed.trans
    rw [tableSize]
    unfold decodeBudget
    gcongr
  have previousSize := decodeRows_storage n table (SignedCapacity.coordinates_valid n) generated.1
  have mixedSize := decodeRows_storage n table (SignedCapacity.coordinates_valid n) generated.2
  have originalSize := rows_storage formula
  have sourceCost := expand_cells formula
  have originalCost := rows_cells formula
  have tableCost := coordinates_cells n
  simp only [prepare,append,rowsCells_append,expand_value]
  change (expand formula).cells+(both (SignedCapacity.expand formula)).cells+(rows formula).cells+
    (coordinates n).cells+(decodeRows table generated.1).cells+(decodeRows table generated.2).cells+
    (2*rowsCells (decodeRows table generated.1).value+2*rowsCells (rows formula).value+5)+
    (2*(rowsCells (decodeRows table generated.1).value+rowsCells (rows formula).value)+
      2*rowsCells (decodeRows table generated.2).value+5)+8 ≤ _
  unfold prepareBudget currentStorage at *
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.RowCost

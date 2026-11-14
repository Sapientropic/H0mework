import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.CapacityMatching.Source

/-!
The paired source execution charges row addressing, field maps, full group/table
copy budgets, owner scans, and vector writes. Computing the counters themselves,
and bit-level implementations of addresses, comparisons, and allocation, remain separate.
-/

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.SourceCost

open SaturationMonoid.ComplexityProjection.SATSource.Affine

structure Counted (α : Type) where
  value : α
  cells : Nat

private theorem sum_bound {α : Type} (items : List α) (cost size : α → Nat) (a b : Nat)
    (bound : ∀ item ∈ items, cost item ≤ a+b*size item) :
    (items.map cost).sum ≤ a*items.length+b*(items.map size).sum := by
  induction items with
  | nil => simp
  | cons item rest ih =>
      have head := bound item (by simp)
      have tail := ih (fun other member => bound other (by simp [member]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith

def annotate {n d : Nat} (owner : Fin d) : List (Fin n) → Counted (List (Source.Item n d))
  | [] => ⟨[],1⟩
  | literal::rest =>
      let tail := annotate owner rest
      ⟨⟨literal,owner⟩::tail.value,tail.cells+4⟩

theorem annotate_value {n d : Nat} (owner : Fin d) (row : List (Fin n)) :
    (annotate owner row).value = row.map (fun literal => (⟨literal,owner⟩ : Source.Item n d)) := by
  induction row with
  | nil => rfl
  | cons literal rest ih => simp only [annotate,List.map_cons,ih]

theorem annotate_cells {n d : Nat} (owner : Fin d) (row : List (Fin n)) :
    (annotate owner row).cells = 4*row.length+1 := by
  induction row with
  | nil => rfl
  | cons literal rest ih => simp only [annotate,ih,List.length_cons]; omega

def tagRow {n : Nat} (rows : List (List (Fin n))) (i : Fin rows.length) :
    Counted (List (Source.Item n rows.length)) :=
  let tagged := annotate i (rows.get i)
  ⟨tagged.value,tagged.cells+i.val+1⟩

def tags {n : Nat} (rows : List (List (Fin n))) : Counted (List (Source.Item n rows.length)) :=
  let parts := List.ofFn (tagRow rows)
  ⟨(parts.map Counted.value).flatten,(parts.map Counted.cells).sum+2*rows.flatten.length+4*rows.length+2⟩

theorem tags_value {n : Nat} (rows : List (List (Fin n))) : (tags rows).value = Source.tags rows := by
  simp [tags,tagRow,Source.tags,annotate_value,List.map_ofFn,Function.comp_def]

theorem tags_cells {n : Nat} (rows : List (List (Fin n))) :
    (tags rows).cells ≤ rows.length*(rows.length+5)+6*rows.flatten.length+2 := by
  let parts := List.ofFn (tagRow rows)
  have each (part : Counted (List (Source.Item n rows.length))) (member : part ∈ parts) :
      part.cells ≤ rows.length+1+4*part.value.length := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    simp only [tagRow,annotate_value,annotate_cells,List.length_map]
    have inside := i.isLt
    omega
  have total := sum_bound parts Counted.cells (fun part => part.value.length) (rows.length+1) 4 each
  have lengths : (parts.map (fun part => part.value.length)).sum = rows.flatten.length := by
    simp only [parts,tagRow,List.map_ofFn,Function.comp_def,annotate_value,List.length_map]
    change (List.ofFn (List.length ∘ rows.get)).sum = _
    rw [← List.map_ofFn,List.ofFn_get,List.length_flatten]
  rw [lengths] at total
  simp only [parts,List.length_ofFn] at total
  change (parts.map Counted.cells).sum+2*rows.flatten.length+4*rows.length+2 ≤ _
  nlinarith

def copyCells {n d : Nat} (groups : List (List (Source.Item n d))) : Nat :=
  4*groups.flatten.length+2*groups.length+8

/-- The entire rewritten group table receives a full field-copy allowance at every return. -/
def put {n d : Nat} (formula : CNFFormula n) (item : Source.Item n d) :
    List (List (Source.Item n d)) → Counted (List (List (Source.Item n d)))
  | [] => ⟨[[item]],8⟩
  | group::rest =>
      let erased := group.map (·.literal)
      let found := Capacity.fits formula item.literal erased
      let used := found.visits+2*group.length+1+copyCells (group::rest)+4
      if found.accepted then ⟨(item::group)::rest,used⟩
      else let tail := put formula item rest
           ⟨group::tail.value,used+tail.cells⟩

theorem put_value {n d : Nat} (formula : CNFFormula n) (item : Source.Item n d)
    (groups : List (List (Source.Item n d))) : (put formula item groups).value = Source.put formula item groups := by
  induction groups with
  | nil => rfl
  | cons group rest ih => simp only [put,Source.put]; split <;> simp_all

theorem put_cells {n d : Nat} (formula : CNFFormula n) (item : Source.Item n d)
    (groups : List (List (Source.Item n d))) :
    (put formula item groups).cells ≤ groups.flatten.length*(Capacity.queryBudget formula+3)+
      groups.length*(4*groups.flatten.length+2*groups.length+16)+8 := by
  induction groups with
  | nil => simp [put]
  | cons group rest ih =>
      have query := Capacity.fits_visits formula item.literal (group.map (·.literal))
      simp only [List.length_map] at query
      simp only [put,copyCells,List.flatten_cons,List.length_append,List.length_cons]
      split <;> simp only <;> nlinarith

def partition {n d : Nat} (formula : CNFFormula n) :
    List (Source.Item n d) → Counted (List (List (Source.Item n d)))
  | [] => ⟨[],1⟩
  | item::rest =>
      let before := partition formula rest
      let after := put formula item before.value
      ⟨after.value,before.cells+after.cells+2⟩

theorem partition_value {n d : Nat} (formula : CNFFormula n) (items : List (Source.Item n d)) :
    (partition formula items).value = Source.partition formula items := by
  induction items with
  | nil => rfl
  | cons item rest ih => simp only [partition,Source.partition,put_value,ih]

theorem partition_length {n d : Nat} (formula : CNFFormula n) (items : List (Source.Item n d)) :
    (Source.partition formula items).length ≤ items.length := by
  have same := congrArg List.length (Source.partition_erase formula items)
  simp only [Source.erase,List.length_map] at same
  rw [same]
  simpa only [List.length_map] using Capacity.partition_length formula (items.map (·.literal))

theorem partition_cells {n d : Nat} (formula : CNFFormula n) (items : List (Source.Item n d)) :
    (partition formula items).cells ≤ (items.length+1)^2*(Capacity.queryBudget formula+6*items.length+30) := by
  induction items with
  | nil => simp [partition]
  | cons item rest ih =>
      have inserted := put_cells formula item (partition formula rest).value
      rw [partition_value] at inserted
      have retained := (Source.partition_perm formula rest).length_eq
      rw [retained] at inserted
      have count := partition_length formula rest
      have insertion : (put formula item (partition formula rest).value).cells ≤
          rest.length*(Capacity.queryBudget formula+3)+rest.length*(6*rest.length+16)+8 := by
        rw [partition_value]
        apply inserted.trans
        gcongr
        omega
      simp only [partition,List.length_cons]
      nlinarith

def ownerScan {n d : Nat} (i : Fin d) : List (Source.Item n d) → Extract.Check
  | [] => ⟨false,1⟩
  | item::rest =>
      if item.demand == i then ⟨true,3⟩
      else let next := ownerScan i rest; ⟨next.accepted,next.visits+3⟩

theorem ownerScan_value {n d : Nat} (i : Fin d) (group : List (Source.Item n d)) :
    (ownerScan i group).accepted = group.any (fun item => item.demand == i) := by
  induction group with
  | nil => rfl
  | cons item rest ih => simp only [ownerScan,List.any_cons]; split <;> simp_all

theorem ownerScan_visits {n d : Nat} (i : Fin d) (group : List (Source.Item n d)) :
    (ownerScan i group).visits ≤ 3*group.length+1 := by
  induction group with
  | nil => rfl
  | cons item rest ih => simp only [ownerScan,List.length_cons]; split <;> simp only <;> omega

def graphCell {n d : Nat} (data : List (List (Source.Item n d))) (i : Fin d) (j : Fin data.length) : Counted Bool :=
  let group := data.get j
  let found := ownerScan i group
  ⟨found.accepted,found.visits+j.val+1+4*group.length+3⟩

def graphRow {n d : Nat} (data : List (List (Source.Item n d))) (i : Fin d) : Counted (Vector Bool data.length) :=
  let cells := Vector.ofFn (graphCell data i)
  ⟨cells.map Counted.value,(cells.toList.map Counted.cells).sum+2*data.length+2⟩

theorem graphRow_value {n d : Nat} (data : List (List (Source.Item n d))) (i : Fin d) :
    (graphRow data i).value = Vector.ofFn (fun j => (data.get j).any (fun item => item.demand == i)) := by
  simp [graphRow,graphCell,ownerScan_value,Function.comp_def]

theorem graphRow_cells {n d : Nat} (data : List (List (Source.Item n d))) (i : Fin d) :
    (graphRow data i).cells ≤ data.length*(data.length+6)+7*data.flatten.length+2 := by
  let inputs := List.finRange data.length
  have each (j : Fin data.length) (_member : j ∈ inputs) :
      (graphCell data i j).cells ≤ data.length+4+7*(data.get j).length := by
    have scanBound := ownerScan_visits i (data.get j)
    have inside := j.isLt
    simp only [graphCell]
    omega
  have total := sum_bound inputs (fun j => (graphCell data i j).cells) (fun j => (data.get j).length)
    (data.length+4) 7 each
  have lengths : (inputs.map (fun j => (data.get j).length)).sum = data.flatten.length := by
    change (List.map _ (List.ofFn id)).sum = _
    rw [List.map_ofFn]
    change (List.ofFn (List.length ∘ data.get)).sum = _
    rw [← List.map_ofFn,List.ofFn_get,List.length_flatten]
  rw [lengths] at total
  simp only [inputs,List.finRange,List.map_ofFn,Function.comp_def,List.length_ofFn] at total
  simp only [graphRow,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]
  nlinarith

def ofGroups {n d : Nat} (data : List (List (Source.Item n d))) : Counted (Graph d data.length) :=
  let rows := Vector.ofFn (graphRow data)
  ⟨rows.map Counted.value,(rows.toList.map Counted.cells).sum+2*d*data.length+2*d+2⟩

theorem ofGroups_value {n d : Nat} (data : List (List (Source.Item n d))) :
    (ofGroups data).value = Source.ofGroups data := by
  simp [ofGroups,Source.ofGroups,graphRow_value,Function.comp_def]

theorem ofGroups_cells {n d : Nat} (data : List (List (Source.Item n d))) :
    (ofGroups data).cells ≤ d*(data.length*(data.length+8)+7*data.flatten.length+4)+2 := by
  let rows := (Vector.ofFn (graphRow data)).toList
  have each (row : Counted (Vector Bool data.length)) (member : row ∈ rows) :
      row.cells ≤ data.length*(data.length+6)+7*data.flatten.length+2 := by
    have present : row ∈ List.ofFn (graphRow data) := by simpa only [rows,Vector.toList_ofFn] using member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
    exact graphRow_cells data i
  have total := sum_bound rows Counted.cells (fun _ => 0)
    (data.length*(data.length+6)+7*data.flatten.length+2) 0 (by simpa only [Nat.zero_mul,Nat.add_zero] using each)
  simp only [Nat.zero_mul,Nat.add_zero,rows,Vector.length_toList] at total
  change (rows.map Counted.cells).sum+2*d*data.length+2*d+2 ≤ _
  nlinarith

def positiveScan {n : Nat} : CNFClause n → Extract.Check
  | [] => ⟨true,1⟩
  | literal::rest =>
      if literal.positive then let next := positiveScan rest; ⟨next.accepted,next.visits+2⟩
      else ⟨false,2⟩

theorem positiveScan_value {n : Nat} (clause : CNFClause n) :
    (positiveScan clause).accepted = clause.all (·.positive) := by
  induction clause with
  | nil => rfl
  | cons literal rest ih => simp only [positiveScan,List.all_cons]; split <;> simp_all

theorem positiveScan_cells {n : Nat} (clause : CNFClause n) :
    (positiveScan clause).visits ≤ 2*clause.length+1 := by
  induction clause with
  | nil => rfl
  | cons literal rest ih => simp only [positiveScan,List.length_cons]; split <;> simp only <;> omega

def positives {n : Nat} : CNFFormula n → Counted (List (List (Fin n)))
  | [] => ⟨[],1⟩
  | clause::rest =>
      let found := positiveScan clause
      let tail := positives rest
      ⟨if found.accepted then clause.map (·.var)::tail.value else tail.value,
        found.visits+6*clause.length+4+tail.cells⟩

theorem positives_value {n : Nat} (formula : CNFFormula n) : (positives formula).value = Capacity.positives formula := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp only [positives,Capacity.positives_cons,positiveScan_value,ih]

theorem positives_cells {n : Nat} (formula : CNFFormula n) :
    (positives formula).cells ≤ 8*Extract.literalCount formula+5*formula.length+1 := by
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
      have first := positiveScan_cells clause
      simp only [positives,Extract.literalCount,List.map_cons,List.sum_cons,List.length_cons]
      simp only [Extract.literalCount] at ih
      omega

structure Setup (n : Nat) where
  rows : List (List (Fin n))
  data : List (List (Source.Item n rows.length))
  graph : Graph rows.length data.length
  cells : Nat

def setup {n : Nat} (formula : CNFFormula n) : Setup n :=
  let rows := positives formula
  let marked := tags rows.value
  let grouped := partition formula marked.value
  let written := ofGroups grouped.value
  ⟨rows.value,grouped.value,written.value,rows.cells+marked.cells+grouped.cells+written.cells+3⟩

theorem setup_rows {n : Nat} (formula : CNFFormula n) : (setup formula).rows = Capacity.positives formula :=
  positives_value formula

theorem setup_data {n : Nat} (formula : CNFFormula n) :
    (setup formula).data = Source.partition formula (Source.tags (setup formula).rows) := by
  simp only [setup,partition_value,tags_value]

theorem setup_graph {n : Nat} (formula : CNFFormula n) :
    (setup formula).graph = Source.ofGroups (setup formula).data := ofGroups_value _

theorem setup_possible {n : Nat} (formula : CNFFormula n) :
    CapacityMatching.possible (setup formula).graph = Source.possible formula := by
  rw [setup_graph,setup_data]
  exact congrArg (fun rows => CapacityMatching.possible (Source.ofGroups (Source.partition formula (Source.tags rows))))
    (setup_rows formula)

def setupBound (m literals : Nat) : Nat :=
  (8*literals+5*m+1)+(m*(m+5)+6*literals+2)+
    (literals+1)^2*(16*literals+8*m+31)+
    (m*(literals*(literals+8)+7*literals+4)+2)+3

theorem setup_cells {n : Nat} (formula : CNFFormula n) :
    (setup formula).cells ≤ setupBound formula.length (Extract.literalCount formula) := by
  let rows := (positives formula).value
  let marked := (tags rows).value
  let grouped := (partition formula marked).value
  have rowCount : rows.length ≤ formula.length := by
    simpa only [rows,positives_value] using Capacity.positives_length formula
  have rowSize : rows.flatten.length ≤ Extract.literalCount formula := by
    simpa only [rows,positives_value] using Capacity.positives_literals formula
  have tagSize : marked.length = rows.flatten.length := by
    have same := congrArg List.length (Source.tags_erase rows)
    simpa only [marked,tags_value,List.length_map] using same
  have groupCount : grouped.length ≤ Extract.literalCount formula := by
    simp only [grouped,partition_value]
    exact (partition_length formula marked).trans (tagSize ▸ rowSize)
  have groupSize : grouped.flatten.length ≤ Extract.literalCount formula := by
    simp only [grouped,partition_value]
    rw [(Source.partition_perm formula marked).length_eq,tagSize]
    exact rowSize
  have tagging := tags_cells rows
  have partitioning := partition_cells formula marked
  have writing := ofGroups_cells grouped
  have tagsBound : (tags rows).cells ≤ formula.length*(formula.length+5)+6*Extract.literalCount formula+2 := by
    apply tagging.trans
    gcongr
  have partitionBound : (partition formula marked).cells ≤
      (Extract.literalCount formula+1)^2*(16*Extract.literalCount formula+8*formula.length+31) := by
    have size : marked.length ≤ Extract.literalCount formula := tagSize ▸ rowSize
    calc
      (partition formula marked).cells ≤
          (marked.length+1)^2*(Capacity.queryBudget formula+6*marked.length+30) := partitioning
      _ ≤ (Extract.literalCount formula+1)^2*(Capacity.queryBudget formula+6*Extract.literalCount formula+30) := by gcongr
      _ = _ := by unfold Capacity.queryBudget; ring
  have graphBound : (ofGroups grouped).cells ≤ formula.length*(Extract.literalCount formula*
      (Extract.literalCount formula+8)+7*Extract.literalCount formula+4)+2 := by
    apply writing.trans
    gcongr
  have preprocessing := positives_cells formula
  change (positives formula).cells+(tags rows).cells+(partition formula marked).cells+(ofGroups grouped).cells+3 ≤ _
  unfold setupBound
  omega

theorem setup_dimensions {n : Nat} (formula : CNFFormula n) :
    (setup formula).rows.length ≤ formula.length ∧ (setup formula).data.length ≤ Extract.literalCount formula := by
  constructor
  · rw [setup_rows]
    exact Capacity.positives_length formula
  · rw [setup_data]
    have count := partition_length formula (Source.tags (setup formula).rows)
    have retained := congrArg List.length (Source.tags_erase (setup formula).rows)
    simp only [List.length_map] at retained
    apply count.trans
    rw [retained,setup_rows]
    exact Capacity.positives_literals formula

def run {n : Nat} (formula : CNFFormula n) : Counted Bool :=
  let prepared := setup formula
  let result := generate prepared.graph
  ⟨match result.answer with | .matched _ => true | .deficient _ => false,
    prepared.cells+result.visits+1⟩

theorem run_value {n : Nat} (formula : CNFFormula n) : (run formula).value = Source.possible formula := by
  have same := setup_possible formula
  cases generated : (generate (setup formula).graph).answer <;>
    simpa only [run,CapacityMatching.possible,generated] using same

theorem run_cells {n : Nat} (formula : CNFFormula n) :
    (run formula).cells ≤ setupBound formula.length (Extract.literalCount formula)+
      (formula.length+1)*solveUnits formula.length (Extract.literalCount formula)+Extract.literalCount formula+2 := by
  have first := setup_cells formula
  obtain ⟨rowCount,groupCount⟩ := setup_dimensions formula
  have matched := generate_visits (setup formula).graph
  have final : (generate (setup formula).graph).visits ≤
      (formula.length+1)*solveUnits formula.length (Extract.literalCount formula)+Extract.literalCount formula+1 := by
    apply matched.trans
    unfold solveUnits roundUnits
    gcongr
  change (setup formula).cells+(generate (setup formula).graph).visits+1 ≤ _
  omega

end SaturationMonoid.ComplexityProjection.SATSource.CapacityMatching.SourceCost

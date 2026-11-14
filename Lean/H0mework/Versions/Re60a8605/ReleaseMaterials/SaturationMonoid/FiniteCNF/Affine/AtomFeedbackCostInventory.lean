import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.AtomFeedbackCost

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineAtomFeedbackCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
open CapacityMatching.RowCost (rowCells rowsCells)

def keyStorage (keys : List (List Nat)) : Nat := (keys.map (fun terms => terms.length+1)).sum

@[simp] theorem keyStorage_nil : keyStorage []=0 := rfl
@[simp] theorem keyStorage_cons (head : List Nat) (rest : List (List Nat)) :
    keyStorage (head::rest)=head.length+1+keyStorage rest := rfl
@[simp] theorem keyStorage_append (left right : List (List Nat)) :
    keyStorage (left++right)=keyStorage left+keyStorage right := by simp [keyStorage]

theorem keyStorage_sublist {left right : List (List Nat)} (part : left.Sublist right) :
    keyStorage left ≤ keyStorage right :=
  List.Sublist.sum_le_sum (part.map (fun terms => terms.length+1)) (fun _ _ => Nat.zero_le _)

theorem keys_length_storage (keys : List (List Nat)) : keys.length ≤ keyStorage keys := by
  induction keys with
  | nil => rfl
  | cons head rest ih => simp only [List.length_cons,keyStorage_cons]; omega

theorem key_length_storage (keys : List (List Nat)) (key : List Nat) (member : key ∈ keys) :
    key.length+1 ≤ keyStorage keys :=
  List.le_sum_of_mem (List.mem_map.mpr ⟨key,member,rfl⟩)

def equalTerms : List Nat → List Nat → Counted Bool
  | [],[] => ⟨true,1⟩
  | [],_::_ => ⟨false,1⟩
  | _::_,[] => ⟨false,1⟩
  | i::left,j::right =>
      if i==j then let tail := equalTerms left right; ⟨tail.value,tail.cells+3⟩
      else ⟨false,2⟩

theorem equalTerms_value (left right : List Nat) : (equalTerms left right).value=decide (left=right) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons i left ih =>
      cases right with
      | nil => rfl
      | cons j right => simp only [equalTerms]; split <;> simp_all

theorem equalTerms_cells (left right : List Nat) : (equalTerms left right).cells ≤ 3*left.length+1 := by
  induction left generalizing right with
  | nil => cases right <;> simp [equalTerms]
  | cons i left ih =>
      cases right with
      | nil => simp [equalTerms]
      | cons j right =>
          have tail := ih right
          simp only [equalTerms,List.length_cons]
          split <;> simp only <;> omega

def contains (key : List Nat) : List (List Nat) → Counted Bool
  | [] => ⟨false,1⟩
  | head::rest =>
      let tested := equalTerms key head
      if tested.value then ⟨true,tested.cells+2⟩
      else let tail := contains key rest; ⟨tail.value,tested.cells+tail.cells+2⟩

theorem contains_value (key : List Nat) (keys : List (List Nat)) :
    (contains key keys).value=decide (key ∈ keys) := by
  induction keys with
  | nil => rfl
  | cons head rest ih => simp only [contains,equalTerms_value]; split <;> simp_all

theorem contains_cells (key : List Nat) (keys : List (List Nat)) :
    (contains key keys).cells ≤ keys.length*(3*key.length+3)+1 := by
  induction keys with
  | nil => simp [contains]
  | cons head rest ih =>
      have first := equalTerms_cells key head
      simp only [contains,List.length_cons]
      split <;> simp only <;> nlinarith

def unique : List (List Nat) → Counted (List (List Nat))
  | [] => ⟨[],1⟩
  | head::rest =>
      let tail := unique rest
      let found := contains head tail.value
      ⟨if found.value then tail.value else head::tail.value,
        tail.cells+found.cells+2*(keyStorage tail.value+head.length+1)+5⟩

theorem unique_value (keys : List (List Nat)) : (unique keys).value=keys.dedup := by
  induction keys with
  | nil => rfl
  | cons head rest ih => simp only [unique,contains_value,ih,List.dedup_cons']; split <;> simp_all

theorem unique_sublist (keys : List (List Nat)) : (unique keys).value.Sublist keys := by
  rw [unique_value]
  exact List.dedup_sublist _

theorem unique_storage (keys : List (List Nat)) : keyStorage (unique keys).value ≤ keyStorage keys :=
  keyStorage_sublist (unique_sublist keys)

def uniqueBudget (size : Nat) : Nat := size*(size*(3*size+3)+2*size+6)+1

theorem unique_cells_aux (keys : List (List Nat)) (size : Nat) (total : keyStorage keys ≤ size) :
    (unique keys).cells ≤ keys.length*(size*(3*size+3)+2*size+6)+1 := by
  induction keys with
  | nil => simp [unique]
  | cons head rest ih =>
      have firstSize : head.length ≤ size := by simp only [keyStorage_cons] at total; omega
      have restSize : keyStorage rest ≤ size := by simp only [keyStorage_cons] at total; omega
      have tail := ih restSize
      have stored := unique_storage rest
      have length := (keys_length_storage (unique rest).value).trans (stored.trans restSize)
      have found := contains_cells head (unique rest).value
      have search : (contains head (unique rest).value).cells ≤ size*(3*size+3)+1 := by
        apply found.trans; gcongr
      simp only [unique,List.length_cons]
      simp only [keyStorage_cons] at total
      nlinarith

theorem unique_cells (keys : List (List Nat)) : (unique keys).cells ≤ uniqueBudget (keyStorage keys) := by
  apply (unique_cells_aux keys (keyStorage keys) (Nat.le_refl _)).trans
  unfold uniqueBudget
  gcongr
  exact keys_length_storage keys

def rowsKeys : List Row → Counted (List (List Nat))
  | [] => ⟨[],1⟩
  | row::rest =>
      let copied := AffineClauseProduct.Cost.copyVars row.vars
      let tail := rowsKeys rest
      ⟨copied.value::tail.value,copied.visits+tail.cells+2*(copied.value.length+1+keyStorage tail.value)+5⟩

theorem rowsKeys_value (rows : List Row) : (rowsKeys rows).value=rows.map Row.vars := by
  induction rows <;> simp_all [rowsKeys,AffineClauseProduct.Cost.copyVars_value]

theorem rowsKeys_storage (rows : List Row) : keyStorage (rowsKeys rows).value ≤ rowsCells rows := by
  rw [rowsKeys_value]
  induction rows with
  | nil => rfl
  | cons row rest ih => simp only [List.map_cons,keyStorage_cons,CapacityMatching.RowCost.rowsCells_cons,rowCells]; omega

theorem rowsKeys_cells (rows : List Row) :
    (rowsKeys rows).cells ≤ rowsCells rows*(2*rowsCells rows+8)+1 := by
  induction rows with
  | nil => simp [rowsKeys]
  | cons row rest ih =>
      have stored := rowsKeys_storage rest
      simp only [rowsKeys,AffineClauseProduct.Cost.copyVars_visits,AffineClauseProduct.Cost.copyVars_value,
        CapacityMatching.RowCost.rowsCells_cons,rowCells]
      nlinarith

def rawKeys : Data → Counted (List (List Nat))
  | [] => ⟨[],1⟩
  | rows::rest =>
      let first := rowsKeys rows
      let tail := rawKeys rest
      ⟨first.value++tail.value,first.cells+tail.cells+2*(keyStorage first.value+keyStorage tail.value)+5⟩

theorem rawKeys_value (source : Data) : (rawKeys source).value=source.flatten.map Row.vars := by
  induction source <;> simp_all [rawKeys,rowsKeys_value]

theorem rawKeys_storage (source : Data) : keyStorage (rawKeys source).value ≤ rowsCells source.flatten := by
  induction source with
  | nil => rfl
  | cons rows rest ih =>
      have first := rowsKeys_storage rows
      simp only [rawKeys,keyStorage_append,List.flatten_cons,CapacityMatching.RowCost.rowsCells_append]
      omega

theorem rawKeys_cells (source : Data) : (rawKeys source).cells ≤ dataSize source*(2*dataSize source+10)+1 := by
  induction source with
  | nil => simp [rawKeys,dataSize]
  | cons rows rest ih =>
      have first := rowsKeys_cells rows
      have firstStored := rowsKeys_storage rows
      have tailStored := rawKeys_storage rest
      have tailSize : rowsCells rest.flatten ≤ dataSize rest := by unfold dataSize; omega
      simp only [rawKeys,dataSize_cons]
      nlinarith

def keys (source : Data) : Counted (List (List Nat)) :=
  let original := rawKeys source
  let filtered := unique ([]::original.value)
  ⟨filtered.value,original.cells+filtered.cells+2*(keyStorage original.value+keyStorage filtered.value)+5⟩

theorem keys_value (source : Data) : (keys source).value=Atoms.keys source := by
  simp only [keys,unique_value,rawKeys_value,Atoms.keys]

theorem keys_storage (source : Data) : keyStorage (keys source).value ≤ dataSize source := by
  have unique := unique_storage ([]::(rawKeys source).value)
  have original := rawKeys_storage source
  simp only [keyStorage_cons,List.length_nil] at unique
  change keyStorage (keys source).value ≤ _ at unique
  unfold dataSize
  omega

def keysBudget (size : Nat) : Nat := size*(2*size+10)+1+uniqueBudget size+4*size+5

theorem keys_cells (source : Data) : (keys source).cells ≤ keysBudget (dataSize source) := by
  have original := rawKeys_cells source
  have originalStored := rawKeys_storage source
  have filtered := unique_cells ([]::(rawKeys source).value)
  have keySize : keyStorage ([]::(rawKeys source).value) ≤ dataSize source := by
    simp only [keyStorage_cons,List.length_nil]
    unfold dataSize
    omega
  have filteredCost : (unique ([]::(rawKeys source).value)).cells ≤ uniqueBudget (dataSize source) := by
    apply filtered.trans
    unfold uniqueBudget
    gcongr
  have stored := keys_storage source
  change keyStorage (unique ([]::(rawKeys source).value)).value ≤ _ at stored
  simp only [keys,keysBudget]
  unfold dataSize at *
  omega

def index (key : List Nat) : List (List Nat) → Counted Nat
  | [] => ⟨0,1⟩
  | head::rest =>
      let tested := equalTerms key head
      if tested.value then ⟨0,tested.cells+2⟩
      else let tail := index key rest; ⟨tail.value+1,tested.cells+tail.cells+3⟩

theorem index_value (key : List Nat) (keys : List (List Nat)) : (index key keys).value=keys.idxOf key := by
  induction keys with
  | nil => rfl
  | cons head rest ih => simp only [index,equalTerms_value]; split <;> simp_all [eq_comm]

theorem index_cells (key : List Nat) (keys : List (List Nat)) :
    (index key keys).cells ≤ keys.length*(3*key.length+4)+1 := by
  induction keys with
  | nil => simp [index]
  | cons head rest ih =>
      have first := equalTerms_cells key head
      simp only [index,List.length_cons]
      split <;> simp only <;> nlinarith

def addressWith (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (terms : List Nat) : Counted (Fin (Atoms.keys source).length) :=
  let found := contains terms inventory
  if present : found.value=true then
    let located := index terms inventory
    ⟨⟨located.value,by
      have checked : (contains terms inventory).value=true := present
      have member : terms ∈ inventory := by simpa only [contains_value,decide_eq_true_eq] using checked
      change (index terms inventory).value < (Atoms.keys source).length
      simpa only [index_value,correct] using List.idxOf_lt_length_of_mem member⟩,
      found.cells+located.cells+2*(keyStorage inventory+terms.length)+5⟩
  else
    let located := index [] inventory
    ⟨⟨located.value,by
      have member : [] ∈ inventory := by rw [correct]; exact Atoms.zero_present source
      change (index [] inventory).value < (Atoms.keys source).length
      simpa only [index_value,correct] using List.idxOf_lt_length_of_mem member⟩,
      found.cells+located.cells+2*(keyStorage inventory+terms.length)+5⟩

theorem addressWith_value (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (terms : List Nat) : (addressWith source inventory correct terms).value=Atoms.address source terms := by
  apply Fin.ext
  simp only [addressWith]
  split
  · rename_i found
    have member : terms ∈ Atoms.keys source := by
      simpa only [contains_value,correct,decide_eq_true_eq] using found
    simp only [Atoms.address,dif_pos member,index_value,correct]
  · rename_i missing
    have absent : terms ∉ Atoms.keys source := by
      simpa only [contains_value,correct,decide_eq_true_eq] using missing
    simp only [Atoms.address,dif_neg absent,index_value,correct]

def addressBudget (size : Nat) : Nat := size*(6*size+7)+4*size+7

theorem addressWith_cells (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (terms : List Nat) (size : Nat) (stored : keyStorage inventory ≤ size) (querySize : terms.length ≤ size) :
    (addressWith source inventory correct terms).cells ≤ addressBudget size := by
  have count := (keys_length_storage inventory).trans stored
  have found := contains_cells terms inventory
  have located := index_cells terms inventory
  have fallback := index_cells [] inventory
  have first : (contains terms inventory).cells ≤ size*(3*size+3)+1 := by apply found.trans; gcongr
  have second : (index terms inventory).cells ≤ size*(3*size+4)+1 := by apply located.trans; gcongr
  have third : (index [] inventory).cells ≤ size*(3*size+4)+1 := by apply fallback.trans; simp only [List.length_nil]; gcongr; omega
  simp only [addressWith]
  split <;> simp only <;> unfold addressBudget <;> nlinarith

def literalWith (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (row : Row) : Counted (CNFLiteral (Atoms.keys source).length) :=
  let address := addressWith source inventory correct row.vars
  ⟨⟨address.value,!row.rhs⟩,address.cells+2*rowCells row+6⟩

theorem literalWith_value (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (row : Row) : (literalWith source inventory correct row).value=Atoms.literal source row := by
  simp only [literalWith,addressWith_value,Atoms.literal]

def clauseWith (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : List Row) : Counted (CNFClause (Atoms.keys source).length) :=
  rows.rec ⟨[],1⟩ (fun row _ tail =>
      let first := literalWith source inventory correct row
      ⟨first.value::tail.value,first.cells+tail.cells+6*tail.value.length+7⟩)

theorem clauseWith_value (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : List Row) : (clauseWith source inventory correct rows).value=Atoms.clause source rows := by
  induction rows <;> simp_all [clauseWith,literalWith_value,Atoms.clause]

theorem clauseWith_length (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : List Row) : (clauseWith source inventory correct rows).value.length=rows.length := by
  simp only [clauseWith_value,Atoms.clause,List.length_map]

theorem clauseWith_cells (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : List Row) (size : Nat) (stored : keyStorage inventory ≤ size) (sourceSize : rowsCells rows ≤ size) :
    (clauseWith source inventory correct rows).cells ≤ rows.length*(addressBudget size+8*size+13)+1 := by
  induction rows with
  | nil => simp [clauseWith]
  | cons row rest ih =>
      have rowSize : rowCells row ≤ size := by simp only [CapacityMatching.RowCost.rowsCells_cons] at sourceSize; omega
      have restSize : rowsCells rest ≤ size := by simp only [CapacityMatching.RowCost.rowsCells_cons] at sourceSize; omega
      have querySize : row.vars.length ≤ size := by unfold rowCells at rowSize; omega
      have first := addressWith_cells source inventory correct row.vars size stored querySize
      have tail := ih restSize
      have restLength := (StrongFeedbackScale.rows_length rest).trans restSize
      change (literalWith source inventory correct row).cells+(clauseWith source inventory correct rest).cells+
        6*(clauseWith source inventory correct rest).value.length+7 ≤
        (rest.length+1)*(addressBudget size+8*size+13)+1
      rw [clauseWith_length]
      unfold literalWith
      nlinarith

def bodyWith (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (all : Data) : Counted (CNFFormula (Atoms.keys source).length) :=
  all.rec ⟨[],1⟩ (fun rows _ tail =>
      let first := clauseWith source inventory correct rows
      ⟨first.value::tail.value,first.cells+tail.cells+6*first.value.length+
        2*CapacityMatching.RowCost.formulaCells tail.value+7⟩)

theorem bodyWith_value (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : Data) : (bodyWith source inventory correct rows).value=rows.map (Atoms.clause source) := by
  induction rows <;> simp_all [bodyWith,clauseWith_value]

theorem bodyWith_length (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : Data) : (bodyWith source inventory correct rows).value.length=rows.length := by simp [bodyWith_value]

theorem bodyWith_literals (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : Data) : Extract.literalCount (bodyWith source inventory correct rows).value=rows.flatten.length := by
  simp [bodyWith_value,Extract.literalCount,Atoms.clause,List.length_flatten,Function.comp_def]

theorem bodyWith_storage (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : Data) : CapacityMatching.RowCost.formulaCells (bodyWith source inventory correct rows).value ≤ 5*dataSize rows := by
  have count := StrongFeedbackScale.rows_length rows.flatten
  simp only [CapacityMatching.RowCost.formulaCells,bodyWith_literals,bodyWith_length,dataSize]
  omega

theorem bodyWith_cells (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (rows : Data) (size : Nat) (stored : keyStorage inventory ≤ size) (sourceSize : dataSize rows ≤ size) :
    (bodyWith source inventory correct rows).cells ≤
      rows.length*(size*(addressBudget size+8*size+13)+16*size+8)+1 := by
  induction rows with
  | nil => simp [bodyWith]
  | cons first rest ih =>
      have firstSize : rowsCells first ≤ size := by rw [dataSize_cons] at sourceSize; omega
      have restSize : dataSize rest ≤ size := by rw [dataSize_cons] at sourceSize; omega
      have firstCount := (StrongFeedbackScale.rows_length first).trans firstSize
      have raw := clauseWith_cells source inventory correct first size stored firstSize
      have firstCost : (clauseWith source inventory correct first).cells ≤ size*(addressBudget size+8*size+13)+1 := by
        apply raw.trans; gcongr
      have tail := ih restSize
      have tailStorage := (bodyWith_storage source inventory correct rest).trans (Nat.mul_le_mul_left 5 restSize)
      change (clauseWith source inventory correct first).cells+(bodyWith source inventory correct rest).cells+
        6*(clauseWith source inventory correct first).value.length+
        2*CapacityMatching.RowCost.formulaCells (bodyWith source inventory correct rest).value+7 ≤
        (rest.length+1)*(size*(addressBudget size+8*size+13)+16*size+8)+1
      rw [clauseWith_length]
      nlinarith

def formulaWith (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source) :
    Counted (CNFFormula (Atoms.keys source).length) :=
  let zero := addressWith source inventory correct []
  let body := bodyWith source inventory correct source
  ⟨[⟨zero.value,false⟩]::body.value,zero.cells+body.cells+
    2*CapacityMatching.RowCost.formulaCells body.value+9⟩

theorem formulaWith_value (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source) :
    (formulaWith source inventory correct).value=Atoms.compile source := by
  simp only [formulaWith,addressWith_value,bodyWith_value,Atoms.compile]

def formulaBudget (size : Nat) : Nat :=
  addressBudget size+size*(size*(addressBudget size+8*size+13)+16*size+8)+10*size+10

theorem formulaWith_cells (source : Data) (inventory : List (List Nat)) (correct : inventory=Atoms.keys source)
    (size : Nat) (stored : keyStorage inventory ≤ size) (sourceSize : dataSize source ≤ size) :
    (formulaWith source inventory correct).cells ≤ formulaBudget size := by
  have first := addressWith_cells source inventory correct [] size stored (Nat.zero_le _)
  have tail := bodyWith_cells source inventory correct source size stored sourceSize
  have sourceLength : source.length ≤ size := by unfold dataSize at sourceSize; omega
  have bodyCost : (bodyWith source inventory correct source).cells ≤
      size*(size*(addressBudget size+8*size+13)+16*size+8)+1 := by
    apply tail.trans; gcongr
  have bodyStored := (bodyWith_storage source inventory correct source).trans (Nat.mul_le_mul_left 5 sourceSize)
  simp only [formulaWith,formulaBudget]
  omega

def tableRows : List (List Nat) → Counted (List Row)
  | [] => ⟨[],1⟩
  | terms::rest =>
      let first := AffineClauseProduct.Cost.copyVars terms
      let tail := tableRows rest
      ⟨⟨first.value,false⟩::tail.value,first.visits+tail.cells+2*(first.value.length+2+rowsCells tail.value)+5⟩

theorem tableRows_value (inventory : List (List Nat)) :
    (tableRows inventory).value=inventory.map (fun terms => (⟨terms,false⟩ : Row)) := by
  induction inventory <;> simp_all [tableRows,AffineClauseProduct.Cost.copyVars_value]

theorem tableRows_storage (inventory : List (List Nat)) :
    rowsCells (tableRows inventory).value=keyStorage inventory+inventory.length := by
  induction inventory with
  | nil => rfl
  | cons terms rest ih =>
      simp only [tableRows,CapacityMatching.RowCost.rowsCells_cons,AffineClauseProduct.Cost.copyVars_value,
        keyStorage_cons,List.length_cons,rowCells,ih]
      omega

theorem tableRows_cells (inventory : List (List Nat)) :
    (tableRows inventory).cells ≤ keyStorage inventory*(4*keyStorage inventory+12)+1 := by
  induction inventory with
  | nil => simp [tableRows]
  | cons terms rest ih =>
      have length := keys_length_storage rest
      simp only [tableRows,AffineClauseProduct.Cost.copyVars_visits,AffineClauseProduct.Cost.copyVars_value,
        tableRows_storage,keyStorage_cons]
      nlinarith

def tableWith (inventory : List (List Nat)) : Counted (Array Row) :=
  let rows := tableRows inventory
  ⟨rows.value.toArray,rows.cells+2*rowsCells rows.value+2*keyStorage inventory+3⟩

theorem tableWith_value (inventory : List (List Nat)) :
    (tableWith inventory).value=(inventory.map (fun terms => (⟨terms,false⟩ : Row))).toArray := by
  simp only [tableWith,tableRows_value]

def tableBudget (size : Nat) : Nat := size*(4*size+12)+6*size+4

theorem tableWith_cells (inventory : List (List Nat)) (size : Nat) (stored : keyStorage inventory ≤ size) :
    (tableWith inventory).cells ≤ tableBudget size := by
  have generated := tableRows_cells inventory
  have length := (keys_length_storage inventory).trans stored
  have cost : (tableRows inventory).cells ≤ size*(4*size+12)+1 := by apply generated.trans; gcongr
  simp only [tableWith,tableRows_storage,tableBudget]
  omega

structure Frontend (source : Data) where
  inventory : List (List Nat)
  table : Array Row
  formula : CNFFormula (Atoms.keys source).length
  cells : Nat

/-- The same stored key list supplies the physical table and every source literal address. -/
def front (source : Data) : Frontend source :=
  let inventory := keys source
  let table := tableWith inventory.value
  let formula := formulaWith source inventory.value (keys_value source)
  ⟨inventory.value,table.value,formula.value,inventory.cells+table.cells+formula.cells+
    2*(dataSize source+keyStorage inventory.value+rowsCells table.value.toList+
      CapacityMatching.RowCost.formulaCells formula.value)+7⟩

theorem front_inventory (source : Data) : (front source).inventory=Atoms.keys source := keys_value source

theorem front_table (source : Data) : (front source).table=Atoms.table source := by
  simp only [front,tableWith_value,keys_value,Atoms.table]

theorem front_formula (source : Data) : (front source).formula=Atoms.compile source :=
  formulaWith_value source _ _

def frontBudget (size : Nat) : Nat := keysBudget size+tableBudget size+formulaBudget size+20*size+17

theorem front_cells (source : Data) : (front source).cells ≤ frontBudget (dataSize source) := by
  have stored := keys_storage source
  have first := keys_cells source
  have second := tableWith_cells (keys source).value (dataSize source) stored
  have third := formulaWith_cells source (keys source).value (keys_value source) (dataSize source) stored (Nat.le_refl _)
  have tableStored : rowsCells (tableWith (keys source).value).value.toList ≤ 2*dataSize source := by
    simp only [tableWith,List.toList_toArray,tableRows_storage]
    have count := (keys_length_storage (keys source).value).trans stored
    omega
  have formulaStored : CapacityMatching.RowCost.formulaCells
      (formulaWith source (keys source).value (keys_value source)).value ≤ 6*dataSize source+5 := by
    have previous := bodyWith_storage source (keys source).value (keys_value source) source
    change 3*(1+Extract.literalCount (bodyWith source (keys source).value (keys_value source) source).value)+
      2*((bodyWith source (keys source).value (keys_value source) source).value.length+1)+1 ≤ _
    unfold CapacityMatching.RowCost.formulaCells at previous
    omega
  simp only [front,frontBudget]
  nlinarith

end SaturationMonoid.ComplexityProjection.SATSource.AffineAtomFeedbackCost

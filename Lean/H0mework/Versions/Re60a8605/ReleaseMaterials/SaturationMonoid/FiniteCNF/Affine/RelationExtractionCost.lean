import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Affine.RelationExtractionCostPrimitives

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.AffineRelationExtractionCost
open SaturationMonoid.ComplexityProjection.SATSource.Affine
attribute [local irreducible] normalize

def payloadSize {α : Type} (bytes : α → Nat) : Option α → Nat
  | none => 1
  | some item => bytes item+1

def first {α β : Type} (bytes : β → Nat) (action : α → Counted (Option β)) : List α → Counted (Option β)
  | [] => ⟨none,1⟩
  | item::rest =>
      let checked := action item
      match checked.value with
      | some found => ⟨some found,checked.cells+2*(bytes found+1)+3⟩
      | none =>
          let tail := first bytes action rest
          ⟨tail.value,checked.cells+tail.cells+2*payloadSize bytes tail.value+3⟩

theorem first_value {α β : Type} (bytes : β → Nat) (action : α → Counted (Option β)) (items : List α) :
    (first bytes action items).value=items.findSome? (fun item => (action item).value) := by
  induction items with
  | nil => rfl
  | cons item rest ih => cases answer : (action item).value <;> simp [first,answer,ih]

theorem payloadSize_bound {α : Type} (bytes : α → Nat) (limit : Nat) (bounded : ∀ value, bytes value ≤ limit)
    (value : Option α) : payloadSize bytes value ≤ limit+1 := by
  cases value <;> simp only [payloadSize]
  · omega
  · exact Nat.add_le_add_right (bounded _) 1

theorem first_cells {α β : Type} (bytes : β → Nat) (action : α → Counted (Option β)) (items : List α)
    (work storage : Nat) (bounded : ∀ value, bytes value ≤ storage)
    (paid : ∀ item ∈ items, (action item).cells ≤ work) :
    (first bytes action items).cells ≤ items.length*(work+2*(storage+1)+3)+1 := by
  induction items with
  | nil => simp [first]
  | cons item rest ih =>
      have head := paid item (by simp)
      have tail := ih (fun value member => paid value (by simp [member]))
      have stored := payloadSize_bound bytes storage bounded (first bytes action rest).value
      cases answer : (action item).value with
      | none => simp only [first,answer,List.length_cons]; nlinarith
      | some value =>
          have size := bounded value
          simp only [first,answer,List.length_cons]
          nlinarith

def changeSize {n : Nat} {formula : CNFFormula n} : Subsumption.Change formula → Nat
  | .absorb parent victim _ _ _ _ _ => 3*(parent.length+victim.length)+3
  | .shorten parent victim _ _ _ _ _ _ _ => 3*(parent.length+victim.length)+6

theorem changeSize_bound {n : Nat} (formula : CNFFormula n) (change : Subsumption.Change formula) :
    changeSize change ≤ 6*size formula+6 := by
  cases change with
  | absorb parent victim hp hv different positive included =>
      have a := clause_length_le_size formula parent hp
      have b := clause_length_le_size formula victim hv
      simp only [changeSize]
      omega
  | shorten parent victim pivot hp hv different hpm hvm included =>
      have a := clause_length_le_size formula parent hp
      have b := clause_length_le_size formula victim hv
      simp only [changeSize]
      omega

theorem covers_value {n : Nat} (left right : CNFClause n) :
    (Extract.subset left right).accepted=Subsumption.covers left right := by
  apply Bool.eq_iff_iff.mpr
  rw [Extract.subset_accepted,Subsumption.covers_true_iff]
  rfl

private def pivotValue {n : Nat} (formula : CNFFormula n)
    (parent victim : { clause : CNFClause n // clause ∈ formula }) (different : parent.val ≠ victim.val)
    (pivot : { literal : CNFLiteral n // literal ∈ parent.val }) : Option (Subsumption.Change formula) :=
  if opposite : Alias.negate pivot.val ∈ victim.val then
    if included : Subsumption.covers (parent.val.erase pivot.val) (victim.val.erase (Alias.negate pivot.val))=true then
      some (.shorten parent.val victim.val pivot.val parent.property victim.property different pivot.property opposite included)
    else none
  else none

def pivotCheck {n : Nat} (formula : CNFFormula n)
    (parent victim : { clause : CNFClause n // clause ∈ formula }) (different : parent.val ≠ victim.val)
    (pivot : { literal : CNFLiteral n // literal ∈ parent.val }) : Counted (Option (Subsumption.Change formula)) :=
  let found := Extract.member (Alias.negate pivot.val) victim.val
  if present : found.accepted=true then
    let p := literalErase pivot.val parent.val
    let v := literalErase (Alias.negate pivot.val) victim.val
    let checked := Extract.subset p.value v.value
    let result := if included : checked.accepted=true then
      some (Subsumption.Change.shorten parent.val victim.val pivot.val parent.property victim.property different pivot.property
        (by exact (Extract.member_accepted _ _).mp present)
        (by
          have hit : (Extract.subset (literalErase pivot.val parent.val).value
            (literalErase (Alias.negate pivot.val) victim.val).value).accepted=true := included
          simpa only [literalErase_value,covers_value] using hit))
      else none
    ⟨result,found.visits+p.cells+v.cells+checked.visits+
      6*(p.value.length+v.value.length)+2*payloadSize changeSize result+9⟩
  else ⟨none,found.visits+6*(parent.val.length+victim.val.length)+5⟩

theorem pivotCheck_value {n : Nat} (formula : CNFFormula n)
    (parent victim : { clause : CNFClause n // clause ∈ formula }) (different : parent.val ≠ victim.val)
    (pivot : { literal : CNFLiteral n // literal ∈ parent.val }) :
    (pivotCheck formula parent victim different pivot).value=pivotValue formula parent victim different pivot := by
  by_cases present : Alias.negate pivot.val ∈ victim.val
  · have found := (Extract.member_accepted _ _).mpr present
    by_cases included : Subsumption.covers (parent.val.erase pivot.val) (victim.val.erase (Alias.negate pivot.val))=true
    · simp [pivotCheck,pivotValue,found,present,literalErase_value,covers_value,included]
    · simp [pivotCheck,pivotValue,found,present,literalErase_value,covers_value,included]
  · have absent : (Extract.member (Alias.negate pivot.val) victim.val).accepted=false :=
      Bool.eq_false_iff.mpr (fun hit => present ((Extract.member_accepted _ _).mp hit))
    simp [pivotCheck,pivotValue,absent,present]

def pair {n : Nat} (formula : CNFFormula n)
    (parent victim : { clause : CNFClause n // clause ∈ formula }) : Counted (Option (Subsumption.Change formula)) :=
  let equality := clauseEqual parent.val victim.val
  if distinct : equality.value=false then
    have different : parent.val ≠ victim.val := by
      have tested : (clauseEqual parent.val victim.val).value=false := distinct
      simpa only [clauseEqual_value,decide_eq_false_iff_not] using tested
    let covered := Extract.subset parent.val victim.val
    if included : covered.accepted=true then
      let result := if positive : 0 < victim.val.length then
        some (Subsumption.Change.absorb parent.val victim.val parent.property victim.property different positive
          (by exact (covers_value _ _).symm.trans included))
        else none
      ⟨result,equality.cells+covered.visits+victim.val.length+
        2*payloadSize changeSize result+6*(parent.val.length+victim.val.length)+7⟩
    else
      let probes := first changeSize (pivotCheck formula parent victim different) parent.val.attach
      ⟨probes.value,equality.cells+covered.visits+probes.cells+
        2*payloadSize changeSize probes.value+6*(parent.val.length+victim.val.length)+7⟩
  else ⟨none,equality.cells+6*(parent.val.length+victim.val.length)+5⟩

theorem pair_value {n : Nat} (formula : CNFFormula n)
    (parent victim : { clause : CNFClause n // clause ∈ formula }) :
    (pair formula parent victim).value=Subsumption.inspectPair formula parent victim := by
  by_cases different : parent.val ≠ victim.val
  · have distinct : (clauseEqual parent.val victim.val).value=false := by simp [clauseEqual_value,different]
    by_cases covered : Subsumption.covers parent.val victim.val=true
    · simp [pair,Subsumption.inspectPair,distinct,different,covers_value,covered]
    · have absent : (Extract.subset parent.val victim.val).accepted=false := by
        rw [covers_value]
        exact Bool.eq_false_iff.mpr covered
      simp [pair,distinct,Subsumption.inspectPair,different,absent,covered,first_value,pivotCheck_value,pivotValue]
  · have same : parent.val=victim.val := not_not.mp different
    simp [pair,Subsumption.inspectPair,clauseEqual_value,same]

def scan {n : Nat} (formula : CNFFormula n) : Counted (Option (Subsumption.Change formula)) :=
  let inspected := first changeSize
    (fun parent => first changeSize (pair formula parent) formula.attach) formula.attach
  ⟨inspected.value,inspected.cells+4*size formula+2*payloadSize changeSize inspected.value+5⟩

theorem scan_value {n : Nat} (formula : CNFFormula n) : (scan formula).value=Subsumption.scan formula := by
  simp only [scan,first_value,pair_value,Subsumption.scan]

def pivotBudget (limit : Nat) : Nat :=
  2*eraseBudget limit+limit*(2*limit+2)+26*limit+30

theorem pivotCheck_cells {n : Nat} (formula : CNFFormula n)
    (parent victim : { clause : CNFClause n // clause ∈ formula }) (different : parent.val ≠ victim.val)
    (pivot : { literal : CNFLiteral n // literal ∈ parent.val }) :
    (pivotCheck formula parent victim different pivot).cells ≤ pivotBudget (size formula) := by
  have pSize := clause_length_le_size formula parent.val parent.property
  have vSize := clause_length_le_size formula victim.val victim.property
  have found := Extract.member_visits (Alias.negate pivot.val) victim.val
  have p := literalErase_cells pivot.val parent.val
  have v := literalErase_cells (Alias.negate pivot.val) victim.val
  have pLength := (literalErase_length pivot.val parent.val).trans pSize
  have vLength := (literalErase_length (Alias.negate pivot.val) victim.val).trans vSize
  have pCost : (literalErase pivot.val parent.val).cells ≤ eraseBudget (size formula) := by apply p.trans; unfold eraseBudget; gcongr
  have vCost : (literalErase (Alias.negate pivot.val) victim.val).cells ≤ eraseBudget (size formula) := by apply v.trans; unfold eraseBudget; gcongr
  have checked := Extract.subset_visits (literalErase pivot.val parent.val).value (literalErase (Alias.negate pivot.val) victim.val).value
  have checkedCost : (Extract.subset (literalErase pivot.val parent.val).value
      (literalErase (Alias.negate pivot.val) victim.val).value).visits ≤ size formula*(2*size formula+2)+1 := by
    apply checked.trans; gcongr
  have stored := payloadSize_bound (@changeSize n formula) (6*size formula+6) (changeSize_bound formula)
  simp only [pivotCheck]
  split
  · rename_i foundTrue
    split
    · rename_i included
      have resultSize := stored (some (Subsumption.Change.shorten parent.val victim.val pivot.val
        parent.property victim.property different pivot.property ((Extract.member_accepted _ _).mp foundTrue)
        (by simpa only [literalErase_value,covers_value] using included)))
      unfold pivotBudget
      nlinarith
    · have resultSize := stored none
      unfold pivotBudget
      nlinarith
  · dsimp only
    unfold pivotBudget
    omega

def pairBudget (limit : Nat) : Nat :=
  4*limit+1+limit*(2*limit+2)+1+
    limit*(pivotBudget limit+2*(6*limit+7)+3)+1+26*limit+30

theorem pair_cells {n : Nat} (formula : CNFFormula n)
    (parent victim : { clause : CNFClause n // clause ∈ formula }) :
    (pair formula parent victim).cells ≤ pairBudget (size formula) := by
  have pSize := clause_length_le_size formula parent.val parent.property
  have vSize := clause_length_le_size formula victim.val victim.property
  have equality := clauseEqual_cells parent.val victim.val
  have covered := Extract.subset_visits parent.val victim.val
  have coverCost : (Extract.subset parent.val victim.val).visits ≤ size formula*(2*size formula+2)+1 := by
    apply covered.trans; gcongr
  have payload := payloadSize_bound (@changeSize n formula) (6*size formula+6) (changeSize_bound formula)
  simp only [pair]
  split
  · rename_i distinct
    split
    · split
      · rename_i included positive
        have stored := payload (some (Subsumption.Change.absorb parent.val victim.val parent.property victim.property
          (by simpa only [clauseEqual_value,decide_eq_false_iff_not] using distinct) positive
          ((covers_value _ _).symm.trans included)))
        unfold pairBudget
        nlinarith
      · have stored := payload none
        unfold pairBudget
        nlinarith
    · have different : parent.val ≠ victim.val := by simpa only [clauseEqual_value,decide_eq_false_iff_not] using distinct
      have probed := first_cells changeSize (pivotCheck formula parent victim different) parent.val.attach
        (pivotBudget (size formula)) (6*size formula+6) (changeSize_bound formula)
        (fun pivot _ => pivotCheck_cells formula parent victim different pivot)
      rw [List.length_attach] at probed
      have probeCost : (first changeSize (pivotCheck formula parent victim different) parent.val.attach).cells ≤
          size formula*(pivotBudget (size formula)+2*(6*size formula+7)+3)+1 := by apply probed.trans; gcongr
      have stored := payload (first changeSize (pivotCheck formula parent victim different) parent.val.attach).value
      unfold pairBudget
      nlinarith
  · unfold pairBudget
    nlinarith

def scanBudget (limit : Nat) : Nat :=
  limit*(limit*(pairBudget limit+2*(6*limit+7)+3)+1+2*(6*limit+7)+3)+1+16*limit+19

theorem scan_cells {n : Nat} (formula : CNFFormula n) : (scan formula).cells ≤ scanBudget (size formula) := by
  have length := (size_measures formula).1
  have storage := changeSize_bound formula
  have victims (parent : { clause : CNFClause n // clause ∈ formula }) :=
    first_cells changeSize (pair formula parent) formula.attach (pairBudget (size formula))
      (6*size formula+6) storage (fun victim _ => pair_cells formula parent victim)
  have inner (parent : { clause : CNFClause n // clause ∈ formula }) :
      (first changeSize (pair formula parent) formula.attach).cells ≤
        size formula*(pairBudget (size formula)+2*(6*size formula+7)+3)+1 := by
    apply (victims parent).trans
    rw [List.length_attach]
    gcongr
  have outer := first_cells changeSize
    (fun parent => first changeSize (pair formula parent) formula.attach) formula.attach
    (size formula*(pairBudget (size formula)+2*(6*size formula+7)+3)+1) (6*size formula+6) storage (fun parent _ => inner parent)
  have total : (first changeSize (fun parent => first changeSize (pair formula parent) formula.attach) formula.attach).cells ≤
      size formula*(size formula*(pairBudget (size formula)+2*(6*size formula+7)+3)+1+2*(6*size formula+7)+3)+1 := by
    apply outer.trans
    rw [List.length_attach]
    gcongr
  have copied := payloadSize_bound (@changeSize n formula) (6*size formula+6) storage
    (first changeSize (fun parent => first changeSize (pair formula parent) formula.attach) formula.attach).value
  simp only [scan,scanBudget]
  omega

def rawUpdate {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) : Counted (CNFFormula n) :=
  match change with
  | .absorb _ victim _ _ _ _ _ =>
      let removed := formulaErase victim formula
      ⟨removed.value,removed.cells+2*(size formula+size removed.value)+changeSize change+5⟩
  | .shorten _ victim pivot _ _ _ _ _ _ =>
      let reduced := literalErase (Alias.negate pivot) victim
      let removed := formulaErase victim formula
      let result := reduced.value::removed.value
      ⟨result,reduced.cells+removed.cells+2*(size formula+size result)+changeSize change+5⟩

theorem rawUpdate_value {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) :
    (rawUpdate change).value=Subsumption.rawUpdate change := by
  cases change <;> simp only [rawUpdate,formulaErase_value,literalErase_value,Subsumption.rawUpdate]

theorem rawUpdate_size {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) :
    size (rawUpdate change).value ≤ size formula := by
  rw [rawUpdate_value]
  have literals : Extract.literalCount (Subsumption.rawUpdate change) < Extract.literalCount formula :=
    Subsumption.rawUpdate_literalCount_lt change
  have clauses := Subsumption.rawUpdate_length_le change
  unfold size CapacityMatching.RowCost.formulaCells
  omega

def rawBudget (limit : Nat) : Nat := limit*(12*limit+8)+1+eraseBudget limit+10*limit+11

theorem rawUpdate_cells {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) :
    (rawUpdate change).cells ≤ rawBudget (size formula) := by
  have sourceLength := (size_measures formula).1
  have outputSize := rawUpdate_size change
  have payload := changeSize_bound formula change
  cases change with
  | absorb parent victim hp hv different positive included =>
      have removed := formulaErase_cells victim formula (size formula) (Nat.le_refl _)
      have removal : (formulaErase victim formula).cells ≤ size formula*(12*size formula+8)+1 := by apply removed.trans; gcongr
      simp only [rawUpdate] at outputSize ⊢
      unfold rawBudget
      omega
  | shorten parent victim pivot hp hv different hpm hvm included =>
      have length := clause_length_le_size formula victim hv
      have reduced := literalErase_cells (Alias.negate pivot) victim
      have reduction : (literalErase (Alias.negate pivot) victim).cells ≤ eraseBudget (size formula) := by
        apply reduced.trans; unfold eraseBudget; gcongr
      have removed := formulaErase_cells victim formula (size formula) (Nat.le_refl _)
      have removal : (formulaErase victim formula).cells ≤ size formula*(12*size formula+8)+1 := by apply removed.trans; gcongr
      simp only [rawUpdate] at outputSize ⊢
      unfold rawBudget
      omega

def update {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) : Counted (CNFFormula n) :=
  let altered := rawUpdate change
  let normalized := normalize altered.value
  ⟨normalized.value,altered.cells+normalized.cells+2*(size altered.value+size normalized.value)+5⟩

theorem update_value {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) :
    (update change).value=Subsumption.update change := by
  simp only [update,normalize_value,rawUpdate_value,Subsumption.update]

theorem update_size {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) :
    size (update change).value ≤ size formula :=
  (normalize_size (rawUpdate change).value).trans (rawUpdate_size change)

theorem normalizeBudget_mono (small large : Nat) (bound : small ≤ large) : normalizeBudget small ≤ normalizeBudget large := by
  unfold normalizeBudget filterBudget clausesBudget formulaBudget literalsBudget
  gcongr

def updateBudget (limit : Nat) : Nat := rawBudget limit+normalizeBudget limit+4*limit+5

theorem update_cells {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) :
    (update change).cells ≤ updateBudget (size formula) := by
  have first := rawUpdate_cells change
  have raw := rawUpdate_size change
  have second := (normalize_cells (rawUpdate change).value).trans (normalizeBudget_mono _ _ raw)
  have result := (normalize_size (rawUpdate change).value).trans raw
  simp only [update,updateBudget]
  omega

def reduceFuel {n : Nat} : Nat → CNFFormula n → Counted (CNFFormula n)
  | 0,formula => ⟨formula,2*size formula+1⟩
  | fuel+1,formula =>
      let scanned := scan formula
      match scanned.value with
      | none => ⟨formula,scanned.cells+2*size formula+3⟩
      | some change =>
          let updated := update change
          let tail := reduceFuel fuel updated.value
          ⟨tail.value,scanned.cells+updated.cells+tail.cells+
            2*(size formula+size updated.value+size tail.value)+2*changeSize change+7⟩

theorem reduceFuel_value {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    (reduceFuel fuel formula).value=Subsumption.reduceFuel fuel formula := by
  induction fuel generalizing formula with
  | zero => rfl
  | succ fuel ih =>
      cases scanned : Subsumption.scan formula <;>
        simp only [reduceFuel,scan_value,scanned,ih,update_value,Subsumption.reduceFuel]

theorem reduceFuel_size {n : Nat} (fuel : Nat) (formula : CNFFormula n) :
    size (reduceFuel fuel formula).value ≤ size formula := by
  rw [reduceFuel_value]
  have clauses := Subsumption.reduceFuel_length_le fuel formula
  have literals : Extract.literalCount (Subsumption.reduceFuel fuel formula) ≤ Extract.literalCount formula :=
    Subsumption.reduceFuel_literalCount_le fuel formula
  unfold size CapacityMatching.RowCost.formulaCells
  omega

def roundBudget (limit : Nat) : Nat := scanBudget limit+updateBudget limit+18*limit+19

theorem scanBudget_mono (small large : Nat) (bound : small ≤ large) : scanBudget small ≤ scanBudget large := by
  unfold scanBudget pairBudget pivotBudget eraseBudget
  gcongr

theorem updateBudget_mono (small large : Nat) (bound : small ≤ large) : updateBudget small ≤ updateBudget large := by
  unfold updateBudget rawBudget normalizeBudget filterBudget clausesBudget formulaBudget literalsBudget eraseBudget
  gcongr

theorem reduceFuel_cells {n : Nat} (fuel : Nat) (formula : CNFFormula n) (limit : Nat) (bounded : size formula ≤ limit) :
    (reduceFuel fuel formula).cells ≤ fuel*roundBudget limit+2*limit+1 := by
  induction fuel generalizing formula with
  | zero => simp only [reduceFuel]; omega
  | succ fuel ih =>
      have scanned := (scan_cells formula).trans (scanBudget_mono _ _ bounded)
      cases found : (scan formula).value with
      | none =>
          simp only [reduceFuel,found]
          unfold roundBudget
          nlinarith
      | some change =>
          have updatedSize := (update_size change).trans bounded
          have updated := (update_cells change).trans (updateBudget_mono _ _ bounded)
          have tail := ih (update change).value updatedSize
          have last := (reduceFuel_size fuel (update change).value).trans updatedSize
          have payload := (changeSize_bound formula change).trans (by omega : 6*size formula+6 ≤ 6*limit+6)
          simp only [reduceFuel,found]
          unfold roundBudget at tail ⊢
          nlinarith

def reduce {n : Nat} (formula : CNFFormula n) : Counted (CNFFormula n) :=
  let prepared := normalize formula
  let result := reduceFuel (Extract.literalCount prepared.value) prepared.value
  ⟨result.value,prepared.cells+result.cells+2*(size formula+size prepared.value+size result.value)+5⟩

theorem reduce_value {n : Nat} (formula : CNFFormula n) : (reduce formula).value=Subsumption.reduce formula := by
  simp only [reduce,reduceFuel_value,normalize_value,Subsumption.reduce]
  rfl

theorem reduce_size {n : Nat} (formula : CNFFormula n) : size (reduce formula).value ≤ size formula :=
  (reduceFuel_size _ (normalize formula).value).trans (normalize_size formula)

def reduceBudget (limit : Nat) : Nat := normalizeBudget limit+limit*roundBudget limit+8*limit+6

theorem reduce_cells {n : Nat} (formula : CNFFormula n) : (reduce formula).cells ≤ reduceBudget (size formula) := by
  have prepared := normalize_cells formula
  have normalized := normalize_size formula
  have fuel := (size_measures (normalize formula).value).2.trans normalized
  have executed := reduceFuel_cells (Extract.literalCount (normalize formula).value) (normalize formula).value (size formula) normalized
  have final := (reduceFuel_size (Extract.literalCount (normalize formula).value) (normalize formula).value).trans normalized
  have runtime : (reduceFuel (Extract.literalCount (normalize formula).value) (normalize formula).value).cells ≤
      size formula*roundBudget (size formula)+2*size formula+1 := by apply executed.trans; gcongr
  simp only [reduce,reduceBudget]
  omega

theorem reduce_stopped {n : Nat} (formula : CNFFormula n) : (scan (reduce formula).value).value=none := by
  rw [scan_value,reduce_value]
  exact Subsumption.reduce_exhausted formula

theorem update_decreases {n : Nat} {formula : CNFFormula n} (change : Subsumption.Change formula) :
    Extract.literalCount (update change).value < Extract.literalCount formula := by
  rw [update_value]
  exact Subsumption.update_literalCount_lt change

end SaturationMonoid.ComplexityProjection.SATSource.AffineRelationExtractionCost

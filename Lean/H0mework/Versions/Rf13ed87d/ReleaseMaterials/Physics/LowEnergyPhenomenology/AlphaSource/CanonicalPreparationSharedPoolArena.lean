import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSharedPoolPrefix

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSharedPool
open PreparationVacuumDAGCoefficient PreparationVacuumPoleCancellation PreparationVacuumMoyalNormalization
open PreparationVacuumClockSymbol PreparationVacuumCanonicalMoyal
open scoped BigOperators
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

inductive RawKind where
  | source (degree : Fin 2) (slot : Fin 14)
  | clock (level : ℕ) (axis : Fin 4)
  | moyal (order left right : ℕ)
  deriving DecidableEq

structure RawNode where
  kind : RawKind
  central : Bool
  deriving DecidableEq

structure RawRow where
  coefficient : NormalizedCoefficient
  word : List ℕ

structure RawArena where
  nodes : List RawNode := []
  polynomials : List (List RawRow) := []

abbrev RawAction := RawArena → ℕ × RawArena

def rawRows (state : RawArena) (id : ℕ) : List RawRow := state.polynomials.getD id []

def rawInsertRow (row : RawRow) (rows : List RawRow) : List RawRow :=
  List.rec (motive:=fun _=>RawRow → List RawRow) (fun row=>[row])
    (fun head tail next row=>if row.word=head.word then
      ⟨cancelCoefficient (addCoefficient row.coefficient head.coefficient),head.word⟩::tail
      else head::next row) rows row

def rawRowLess (left right : RawRow) : Bool :=
  decide (List.Lex (· < ·) left.word right.word ∨ left.word=right.word)

-- Arena.poly cancels each coefficient, collects equal words, removes zeros,
-- and sorts the complete row list by the lexicographic tuple of node IDs.
def rawDropZero (rows : List RawRow) : List RawRow := by
  classical
  exact rows.filter (fun row=>decide (row.coefficient.numerator≠0))

def rawNormalize (rows : List RawRow) : List RawRow := by
  classical
  let canceled:=rows.map (fun row=>{row with coefficient:=cancelCoefficient row.coefficient})
  let collected:=canceled.foldr rawInsertRow []
  exact (rawDropZero collected).mergeSort rawRowLess

def rawPoly (rows : List RawRow) : RawAction := fun state=>by
  classical
  let normalized:=rawNormalize rows
  let pool:=PreparationVacuumSourceSerialization.intern normalized state.polynomials
  exact (pool.idxOf normalized,{state with polynomials:=pool})

def rawScalar (c : NormalizedCoefficient) : RawAction := rawPoly [⟨c,[]⟩]

def rawAdd (ids : List ℕ) : RawAction := fun state=>rawPoly (ids.flatMap (rawRows state)) state

def rawScale (c : NormalizedCoefficient) (id : ℕ) : RawAction := fun state=>
  rawPoly ((rawRows state id).map (fun row=>⟨multiplyCoefficient c row.coefficient,row.word⟩)) state

def rawCentral (state : RawArena) (id : ℕ) : Bool :=
  (rawRows state id).all (fun row=>row.word.all (fun i=>(state.nodes.getD i ⟨.source 0 0,false⟩).central))

def rawAtom (kind : RawKind) (central : Bool := false) : RawAction := fun state=>
  let node : RawNode:=⟨kind,central⟩
  let nodes:=PreparationVacuumSourceSerialization.intern node state.nodes
  rawPoly [⟨polynomialCoefficient 1,[nodes.idxOf node]⟩] {state with nodes:=nodes}

def rawOrderWord (state : RawArena) (word : List ℕ) : List ℕ :=
  let central:=fun i=>(state.nodes.getD i ⟨.source 0 0,false⟩).central
  (word.filter central).mergeSort (· ≤ ·)++word.filter (fun i=> !central i)

def rawMultiply (left right : ℕ) : RawAction := fun state=>
  rawPoly ((rawRows state left).flatMap (fun a=>(rawRows state right).map (fun b=>
    ⟨multiplyCoefficient a.coefficient b.coefficient,rawOrderWord state (a.word++b.word)⟩))) state

def rawNumber (row : RawRow) : ℚ := by
  classical
  exact if numericCoefficient row.coefficient then MvPolynomial.constantCoeff row.coefficient.numerator else 1

def rawStrip (id : ℕ) (row : RawRow) : RawAction := fun state=>by
  classical
  exact if numericCoefficient row.coefficient then rawPoly [⟨polynomialCoefficient 1,row.word⟩] state else (id,state)

-- This is the one-row positive-order branch, including constant stripping,
-- the identity-zero rule, the two original swap cases, and the odd diagonal.
def rawPair (r left right : ℕ) : RawAction := fun state=>
  let a:=(rawRows state left).getD 0 ⟨polynomialCoefficient 0,[]⟩
  let b:=(rawRows state right).getD 0 ⟨polynomialCoefficient 0,[]⟩
  let one:=rawStrip left a state
  let two:=rawStrip right b one.2
  let scalar:=rawNumber a*rawNumber b
  if one.1=1 ∨ two.1=1 then (0,two.2) else
    let ca:=rawCentral two.2 one.1
    let cb:=rawCentral two.2 two.1
    let swap:=(!ca && cb)||(ca && cb && decide (one.1>two.1))
    let first:=if swap then two.1 else one.1
    let second:=if swap then one.1 else two.1
    let factor:=if swap then scalar*(-1)^r else scalar
    if decide (first=second) && ca && decide (r%2=1) then (0,two.2) else
      let atom:=rawAtom (.moyal r first second) (ca && cb) two.2
      rawScale (polynomialCoefficient (MvPolynomial.C factor)) atom.1 atom.2

-- Arguments are run from left to right before a single final Arena.add call.
def rawSequence (actions : List RawAction) : RawArena → List ℕ × RawArena :=
  List.rec (motive:=fun _=>RawArena → List ℕ × RawArena)
    (fun state=>([],state))
    (fun action _ rest state=>let one:=action state;let next:=rest one.2;(one.1::next.1,next.2)) actions

def rawMoyal (r left right : ℕ) : RawAction := fun state=>
  if r=0 then rawMultiply left right state else
  if left=0 ∨ right=0 then (0,state) else
    let ls:=rawRows state left
    let rs:=rawRows state right
    if ls.length>1 ∨ rs.length>1 then
      let actions:=ls.flatMap (fun a=>rs.map (fun b=>fun current=>
        let one:=rawPoly [a] current
        let two:=rawPoly [b] one.2
        if one.1=0 ∨ two.1=0 then (0,two.2) else rawPair r one.1 two.1 two.2))
      let expanded:=rawSequence actions state
      rawAdd expanded.1 expanded.2
    else rawPair r left right state

def rawJordan (r left right : ℕ) : RawAction := fun state=>
  let one:=rawMoyal r left right state
  let two:=rawMoyal r right left one.2
  let added:=rawAdd [one.1,two.1] two.2
  rawScale (polynomialCoefficient (MvPolynomial.C (1/2))) added.1 added.2

def rawInitial : RawArena :=
  let zero:=rawScalar (polynomialCoefficient 0) ⟨[],[]⟩
  (rawScalar (polynomialCoefficient 1) zero.2).2


def rawRowValue (atoms : ℕ → ℂ) (row : RawRow) (x : Phase) : ℂ :=
  (coefficientValue row.coefficient x : ℂ)*(row.word.map atoms).prod

def rawRowsValue (atoms : ℕ → ℂ) (rows : List RawRow) (x : Phase) : ℂ :=
  (rows.map (fun row=>rawRowValue atoms row x)).sum

theorem rawInsertRow_value (atoms : ℕ → ℂ) (row : RawRow) (rows : List RawRow)
    (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rawInsertRow row rows) x=rawRowValue atoms row x+rawRowsValue atoms rows x := by
  induction rows with
  | nil=>simp [rawInsertRow,rawRowsValue]
  | cons head tail ih=>
    by_cases same : row.word=head.word
    · simp only [rawInsertRow,if_pos same,rawRowsValue,List.map_cons,List.sum_cons,rawRowValue,
        cancelCoefficient_source _ x hx,addCoefficient_source _ _ x hx,Complex.ofReal_add]
      rw [same]
      ring
    · simp only [rawInsertRow,if_neg same,rawRowsValue,List.map_cons,List.sum_cons]
      change rawRowValue atoms head x+rawRowsValue atoms (rawInsertRow row tail) x=_
      rw [ih]
      simp only [rawRowsValue]
      ring

theorem rawCollect_value (atoms : ℕ → ℂ) (rows : List RawRow) (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rows.foldr rawInsertRow []) x=rawRowsValue atoms rows x := by
  induction rows with
  | nil=>rfl
  | cons row rows ih=>
    change rawRowsValue atoms (rawInsertRow row (rows.foldr rawInsertRow [])) x=_
    rw [rawInsertRow_value _ _ _ x hx,ih]
    rfl

theorem rawCancel_value (atoms : ℕ → ℂ) (rows : List RawRow) (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rows.map (fun row=>{row with coefficient:=cancelCoefficient row.coefficient})) x=
      rawRowsValue atoms rows x := by
  simp only [rawRowsValue,List.map_map,Function.comp_def,rawRowValue,cancelCoefficient_source _ x hx]

theorem rawFilter_value (atoms : ℕ → ℂ) (rows : List RawRow) (x : Phase) :
    rawRowsValue atoms (rawDropZero rows) x=rawRowsValue atoms rows x := by
  classical
  induction rows with
  | nil=>rfl
  | cons row rows ih=>
    by_cases zero : row.coefficient.numerator=0
    · simp only [rawDropZero,List.filter_cons,zero,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,
        if_false,rawRowsValue,List.map_cons,List.sum_cons] at ih ⊢
      have vanished : rawRowValue atoms row x=0 := by
        simp only [rawRowValue,PreparationVacuumSourceCacheRules.zeroCoefficient_value _ zero,Complex.ofReal_zero,zero_mul]
      rw [vanished,zero_add]
      exact ih
    · simp only [rawDropZero,List.filter_cons,zero,ne_eq,not_false_eq_true,decide_true,if_true,
        rawRowsValue,List.map_cons,List.sum_cons] at ih ⊢
      rw [ih]

theorem rawNormalize_value (atoms : ℕ → ℂ) (rows : List RawRow) (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rawNormalize rows) x=rawRowsValue atoms rows x := by
  classical
  unfold rawNormalize
  rw [show ∀ rs : List RawRow,rawRowsValue atoms (rs.mergeSort rawRowLess) x=rawRowsValue atoms rs x from
    fun rs=>((List.mergeSort_perm rs rawRowLess).map (fun row=>rawRowValue atoms row x)).sum_eq]
  rw [rawFilter_value,rawCollect_value _ _ x hx,rawCancel_value _ _ x hx]

theorem rawPoly_bound (rows : List RawRow) (state : RawArena) :
    (rawPoly rows state).1 < (rawPoly rows state).2.polynomials.length := by
  classical
  exact List.idxOf_lt_length_of_mem (PreparationVacuumSourceSerialization.intern_member _ _)

theorem rawPoly_reference (rows : List RawRow) (state : RawArena) :
    rawRows (rawPoly rows state).2 (rawPoly rows state).1=rawNormalize rows := by
  classical
  exact (List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem (PreparationVacuumSourceSerialization.intern_member _ _))).trans
    (List.getElem_idxOf _)

theorem rawPoly_value (rows : List RawRow) (state : RawArena) (atoms : ℕ → ℂ)
    (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rawRows (rawPoly rows state).2 (rawPoly rows state).1) x=rawRowsValue atoms rows x := by
  rw [rawPoly_reference,rawNormalize_value _ _ x hx]


structure RawExtends (old next : RawArena) : Prop where
  nodes : old.nodes.IsPrefix next.nodes
  polynomials : old.polynomials.IsPrefix next.polynomials

theorem RawExtends.refl (state : RawArena) : RawExtends state state := ⟨List.prefix_refl _,List.prefix_refl _⟩

theorem RawExtends.trans {a b c : RawArena} (left : RawExtends a b) (right : RawExtends b c) : RawExtends a c :=
  ⟨left.nodes.trans right.nodes,left.polynomials.trans right.polynomials⟩

theorem rawPoly_extends (rows : List RawRow) (state : RawArena) : RawExtends state (rawPoly rows state).2 :=
  ⟨List.prefix_refl _,intern_prefix _ _⟩

theorem rawRows_preserved {old next : RawArena} (extension : RawExtends old next)
    (id : ℕ) (bound : id < old.polynomials.length) : rawRows next id=rawRows old id := by
  rw [rawRows,List.getD_eq_getElem _ _ (lt_of_lt_of_le bound extension.polynomials.length_le),
    rawRows,List.getD_eq_getElem _ _ bound]
  exact (extension.polynomials.getElem bound).symm

theorem intern_present {α : Type} (entry : α) (pool : List α) (present : entry∈pool) :
    PreparationVacuumSourceSerialization.intern entry pool=pool := by
  classical
  simp only [PreparationVacuumSourceSerialization.intern,if_pos present]

-- Replaying Arena.poly is a lookup after its first emission, with no new rows.
theorem rawPoly_replay (rows : List RawRow) (state : RawArena) :
    rawPoly rows (rawPoly rows state).2=((rawPoly rows state).1,(rawPoly rows state).2) := by
  classical
  have present:=PreparationVacuumSourceSerialization.intern_member (rawNormalize rows) state.polynomials
  simp only [rawPoly,intern_present _ _ present]

theorem rawScalar_extends (c : NormalizedCoefficient) (state : RawArena) : RawExtends state (rawScalar c state).2 :=
  rawPoly_extends _ _

theorem rawAdd_extends (ids : List ℕ) (state : RawArena) : RawExtends state (rawAdd ids state).2 := rawPoly_extends _ _

theorem rawScale_extends (c : NormalizedCoefficient) (id : ℕ) (state : RawArena) :
    RawExtends state (rawScale c id state).2 := rawPoly_extends _ _

theorem rawMultiply_extends (left right : ℕ) (state : RawArena) :
    RawExtends state (rawMultiply left right state).2 := rawPoly_extends _ _

theorem rawAtom_extends (kind : RawKind) (central : Bool) (state : RawArena) :
    RawExtends state (rawAtom kind central state).2 := by
  exact (show RawExtends state {state with nodes:=PreparationVacuumSourceSerialization.intern ⟨kind,central⟩ state.nodes}
    from ⟨intern_prefix _ _,List.prefix_refl _⟩).trans (rawPoly_extends _ _)

theorem rawStrip_extends (id : ℕ) (row : RawRow) (state : RawArena) : RawExtends state (rawStrip id row state).2 := by
  classical
  unfold rawStrip
  split_ifs
  · exact rawPoly_extends _ _
  · exact RawExtends.refl _

theorem rawPair_extends (r left right : ℕ) (state : RawArena) : RawExtends state (rawPair r left right state).2 := by
  classical
  dsimp only [rawPair]
  split_ifs
  all_goals first
    | exact (rawStrip_extends _ _ _).trans (rawStrip_extends _ _ _)
    | exact (((rawStrip_extends _ _ _).trans (rawStrip_extends _ _ _)).trans (rawAtom_extends _ _ _)).trans (rawScale_extends _ _ _)

theorem rawSequence_extends (actions : List RawAction)
    (grows : ∀ action,action∈actions → ∀ state,RawExtends state (action state).2) (state : RawArena) :
    RawExtends state (rawSequence actions state).2 := by
  induction actions generalizing state with
  | nil=>exact RawExtends.refl _
  | cons action actions ih=>
    exact (grows action (by simp) state).trans (ih (fun a h=>grows a (by simp [h])) (action state).2)

theorem rawSequence_length (actions : List RawAction) (state : RawArena) :
    (rawSequence actions state).1.length=actions.length := by
  induction actions generalizing state with
  | nil=>rfl
  | cons action actions ih=>
    change ((action state).1::(rawSequence actions (action state).2).1).length=_
    simp only [List.length_cons,ih]


theorem rawMoyal_extends (r left right : ℕ) (state : RawArena) : RawExtends state (rawMoyal r left right state).2 := by
  by_cases zero : r=0
  · simp only [rawMoyal,if_pos zero]
    exact rawMultiply_extends _ _ _
  · by_cases vanished : left=0 ∨ right=0
    · simp only [rawMoyal,if_neg zero,if_pos vanished]
      exact RawExtends.refl _
    · by_cases splitRows : (rawRows state left).length>1 ∨ (rawRows state right).length>1
      · simp only [rawMoyal,if_neg zero,if_neg vanished,if_pos splitRows]
        apply RawExtends.trans (rawSequence_extends _ ?_ state)
        · exact rawAdd_extends _ _
        · intro action member current
          obtain ⟨a,_,ha⟩:=List.mem_flatMap.mp member
          obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
          dsimp only
          split_ifs
          · exact (rawPoly_extends _ _).trans (rawPoly_extends _ _)
          · exact ((rawPoly_extends _ _).trans (rawPoly_extends _ _)).trans (rawPair_extends _ _ _ _)
      · simp only [rawMoyal,if_neg zero,if_neg vanished,if_neg splitRows]
        exact rawPair_extends _ _ _ _

theorem rawJordan_extends (r left right : ℕ) (state : RawArena) : RawExtends state (rawJordan r left right state).2 :=
  (((rawMoyal_extends _ _ _ state).trans (rawMoyal_extends _ _ _ _)).trans (rawAdd_extends _ _)).trans (rawScale_extends _ _ _)

theorem rawScalar_value (c : NormalizedCoefficient) (state : RawArena) (atoms : ℕ → ℂ)
    (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rawRows (rawScalar c state).2 (rawScalar c state).1) x=(coefficientValue c x : ℂ) := by
  rw [rawScalar,rawPoly_value _ _ _ x hx]
  simp only [rawRowsValue,rawRowValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.prod_nil,mul_one,add_zero]


private theorem complex_flatMap_sum {α : Type} (items : List α) (f : α → List ℂ) :
    (items.flatMap f).sum=(items.map (fun i=>(f i).sum)).sum := by
  induction items with
  | nil=>rfl
  | cons i items ih=>simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem rawAdd_value (ids : List ℕ) (state : RawArena) (atoms : ℕ → ℂ)
    (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rawRows (rawAdd ids state).2 (rawAdd ids state).1) x=
      (ids.map (fun id=>rawRowsValue atoms (rawRows state id) x)).sum := by
  rw [rawAdd,rawPoly_value _ _ _ x hx]
  simp only [rawRowsValue,List.map_flatMap,complex_flatMap_sum]

theorem rawScale_value (c : NormalizedCoefficient) (id : ℕ) (state : RawArena) (atoms : ℕ → ℂ)
    (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rawRows (rawScale c id state).2 (rawScale c id state).1) x=
      (coefficientValue c x : ℂ)*rawRowsValue atoms (rawRows state id) x := by
  rw [rawScale,rawPoly_value _ _ _ x hx]
  simp only [rawRowsValue,List.map_map,Function.comp_def,rawRowValue,multiplyCoefficient_source,
    Complex.ofReal_mul,mul_assoc,List.sum_map_mul_left]

theorem rawOrderWord_perm (state : RawArena) (word : List ℕ) : (rawOrderWord state word).Perm word := by
  exact ((List.mergeSort_perm _ _).append_right _).trans (List.filter_append_perm _ word)

theorem rawOrderWord_value (state : RawArena) (word : List ℕ) (atoms : ℕ → ℂ) :
    ((rawOrderWord state word).map atoms).prod=(word.map atoms).prod :=
  ((rawOrderWord_perm state word).map atoms).prod_eq

theorem rawMultiply_value (left right : ℕ) (state : RawArena) (atoms : ℕ → ℂ)
    (x : Phase) (hx : x∈poleDomain) :
    rawRowsValue atoms (rawRows (rawMultiply left right state).2 (rawMultiply left right state).1) x=
      rawRowsValue atoms (rawRows state left) x*rawRowsValue atoms (rawRows state right) x := by
  rw [rawMultiply,rawPoly_value _ _ _ x hx]
  simp only [rawRowsValue,List.map_flatMap,complex_flatMap_sum,List.map_map,Function.comp_def,
    rawRowValue,multiplyCoefficient_source,Complex.ofReal_mul,rawOrderWord_value,List.map_append,List.prod_append]
  have rearrange (a b : RawRow) :
      (coefficientValue a.coefficient x : ℂ)*(coefficientValue b.coefficient x : ℂ)*
        ((a.word.map atoms).prod*(b.word.map atoms).prod)=
      ((coefficientValue a.coefficient x : ℂ)*(a.word.map atoms).prod)*
        ((coefficientValue b.coefficient x : ℂ)*(b.word.map atoms).prod) := by ring
  simp only [rearrange,List.sum_map_mul_left,List.sum_map_mul_right]



def RawWords (P : ℕ → Prop) (rows : List RawRow) : Prop :=
  ∀ row,row∈rows → ∀ node,node∈row.word → P node

theorem rawInsertRow_words (P : ℕ → Prop) (row : RawRow) (rows : List RawRow)
    (head : ∀ node,node∈row.word → P node) (tail : RawWords P rows) : RawWords P (rawInsertRow row rows) := by
  induction rows with
  | nil=>
    intro out member node hn
    have same : out=row:=List.mem_singleton.mp member
    subst out
    exact head node hn
  | cons first rest ih=>
    by_cases same : row.word=first.word
    · simp only [rawInsertRow,if_pos same]
      intro out member node hn
      rcases List.mem_cons.mp member with h|h
      · subst out;exact tail first (by simp) node hn
      · exact tail out (by simp [h]) node hn
    · simp only [rawInsertRow,if_neg same]
      intro out member node hn
      rcases List.mem_cons.mp member with h|h
      · subst out;exact tail first (by simp) node hn
      · exact ih (fun r hr=>tail r (by simp [hr])) out h node hn

theorem rawCollect_words (P : ℕ → Prop) (rows : List RawRow) (paid : RawWords P rows) :
    RawWords P (rows.foldr rawInsertRow []) := by
  induction rows with
  | nil=>exact paid
  | cons row rows ih=>
    exact rawInsertRow_words P row _ (paid row (by simp)) (ih (fun r hr=>paid r (by simp [hr])))

theorem rawNormalize_words (P : ℕ → Prop) (rows : List RawRow) (paid : RawWords P rows) :
    RawWords P (rawNormalize rows) := by
  classical
  have canceled : RawWords P (rows.map (fun row=>{row with coefficient:=cancelCoefficient row.coefficient})) := by
    intro out member node hn
    obtain ⟨row,hr,rfl⟩:=List.mem_map.mp member
    exact paid row hr node hn
  have collected:=rawCollect_words P _ canceled
  intro row member node hn
  have filtered:= (List.mergeSort_perm _ rawRowLess).subset member
  have source:=List.mem_of_mem_filter filtered
  exact collected row source node hn

def RawKind.dependencies : RawKind → List ℕ
  | .source _ _=>[]
  | .clock _ _=>[]
  | .moyal _ left right=>[left,right]

def rawNode (state : RawArena) (id : ℕ) : RawNode := state.nodes.getD id ⟨.source 0 0,false⟩

structure RawMoyalClosed (state : RawArena) : Prop where
  words : ∀ rows,rows∈state.polynomials → RawWords (fun node=>node < state.nodes.length) rows
  nodes : ∀ node,node∈state.nodes → ∀ dep,dep∈node.kind.dependencies → dep < state.polynomials.length
  earlier : ∀ id,id < state.polynomials.length → ∀ row,row∈rawRows state id →
    ∀ node,node∈row.word → ∀ dep,dep∈(rawNode state node).kind.dependencies → dep < id

theorem rawNode_member (state : RawArena) (id : ℕ) (bound : id < state.nodes.length) : rawNode state id∈state.nodes := by
  rw [rawNode,List.getD_eq_getElem _ _ bound]
  exact List.getElem_mem _

theorem rawNode_preserved {old next : RawArena} (extension : RawExtends old next)
    (id : ℕ) (bound : id < old.nodes.length) : rawNode next id=rawNode old id := by
  rw [rawNode,List.getD_eq_getElem _ _ (lt_of_lt_of_le bound extension.nodes.length_le),
    rawNode,List.getD_eq_getElem _ _ bound]
  exact (extension.nodes.getElem bound).symm


theorem rawPoly_closed (rows : List RawRow) (state : RawArena) (closed : RawMoyalClosed state)
    (words : RawWords (fun node=>node < state.nodes.length) rows) : RawMoyalClosed (rawPoly rows state).2 := by
  classical
  by_cases present : rawNormalize rows∈state.polynomials
  · simpa only [rawPoly,intern_present _ _ present] using closed
  · have pool : PreparationVacuumSourceSerialization.intern (rawNormalize rows) state.polynomials=
        state.polynomials++[rawNormalize rows] := by
      simp only [PreparationVacuumSourceSerialization.intern,if_neg present]
    rw [show (rawPoly rows state).2={state with polynomials:=state.polynomials++[rawNormalize rows]} by
      simp only [rawPoly,pool]]
    let next : RawArena:={state with polynomials:=state.polynomials++[rawNormalize rows]}
    have extension : RawExtends state next:=⟨List.prefix_refl _,List.prefix_append _ _⟩
    have normalized:=rawNormalize_words _ rows words
    change RawMoyalClosed next
    constructor
    · intro stored member
      rcases List.mem_append.mp member with old|fresh
      · exact closed.words stored old
      · have same:=List.mem_singleton.mp fresh
        subst stored
        exact normalized
    · intro node member dep hd
      exact lt_of_lt_of_le (closed.nodes node member dep hd) extension.polynomials.length_le
    · intro id bound row member node hn dep hd
      by_cases old : id < state.polynomials.length
      · have prior : row∈rawRows state id := by
          rw [rawRows_preserved extension id old] at member
          exact member
        exact closed.earlier id old row prior node hn dep hd
      · have same : id=state.polynomials.length := by
          change id < (state.polynomials++[rawNormalize rows]).length at bound
          simp only [List.length_append,List.length_singleton] at bound
          omega
        subst id
        have read : rawRows next state.polynomials.length=rawNormalize rows := by
          change (state.polynomials++[rawNormalize rows]).getD state.polynomials.length []=_
          rw [List.getD_append_right _ _ _ _ (le_refl _),Nat.sub_self,List.getD_cons_zero]
        rw [read] at member
        exact closed.nodes (rawNode state node) (rawNode_member state node (normalized row member node hn)) dep hd


theorem rawRows_member (state : RawArena) (id : ℕ) (bound : id < state.polynomials.length) :
    rawRows state id∈state.polynomials := by
  rw [rawRows,List.getD_eq_getElem _ _ bound]
  exact List.getElem_mem _

def rawInternNode (node : RawNode) (state : RawArena) : RawArena :=
  {state with nodes:=PreparationVacuumSourceSerialization.intern node state.nodes}

theorem rawInternNode_extends (node : RawNode) (state : RawArena) : RawExtends state (rawInternNode node state) :=
  ⟨intern_prefix _ _,List.prefix_refl _⟩

theorem rawInternNode_closed (node : RawNode) (state : RawArena) (closed : RawMoyalClosed state)
    (dependencies : ∀ dep,dep∈node.kind.dependencies → dep < state.polynomials.length) :
    RawMoyalClosed (rawInternNode node state) := by
  classical
  let next:=rawInternNode node state
  have extension:=rawInternNode_extends node state
  change RawMoyalClosed next
  constructor
  · intro rows member row hr id hi
    exact lt_of_lt_of_le (closed.words rows member row hr id hi) extension.nodes.length_le
  · intro other member dep hd
    by_cases present : node∈state.nodes
    · have same : next=state := by simp only [next,rawInternNode,intern_present _ _ present]
      rw [same] at member
      exact closed.nodes other member dep hd
    · have same : next.nodes=state.nodes++[node] := by
        simp only [next,rawInternNode,PreparationVacuumSourceSerialization.intern,if_neg present]
      rw [same] at member
      rcases List.mem_append.mp member with old|fresh
      · exact closed.nodes other old dep hd
      · have equal:=List.mem_singleton.mp fresh
        subst other
        exact dependencies dep hd
  · intro id bound row hr nodeId hi dep hd
    have valid : nodeId < state.nodes.length :=
      closed.words (rawRows state id) (rawRows_member state id bound) row hr nodeId hi
    rw [rawNode_preserved extension nodeId valid] at hd
    exact closed.earlier id bound row hr nodeId hi dep hd

theorem rawAtom_closed (kind : RawKind) (central : Bool) (state : RawArena) (closed : RawMoyalClosed state)
    (dependencies : ∀ dep,dep∈kind.dependencies → dep < state.polynomials.length) :
    RawMoyalClosed (rawAtom kind central state).2 := by
  dsimp only [rawAtom]
  apply rawPoly_closed _ _ (rawInternNode_closed ⟨kind,central⟩ state closed dependencies)
  intro row member id hi
  have same:=List.mem_singleton.mp member
  subst row
  have equal:=List.mem_singleton.mp hi
  subst id
  exact List.idxOf_lt_length_of_mem (PreparationVacuumSourceSerialization.intern_member _ _)

theorem rawScalar_closed (c : NormalizedCoefficient) (state : RawArena) (closed : RawMoyalClosed state) :
    RawMoyalClosed (rawScalar c state).2 := by
  apply rawPoly_closed _ _ closed
  intro row member id hi
  have same:=List.mem_singleton.mp member
  subst row
  exact False.elim (List.not_mem_nil hi)

theorem raw_empty_closed : RawMoyalClosed (⟨[],[]⟩ : RawArena) := by
  constructor
  · intro rows member;exact False.elim (List.not_mem_nil member)
  · intro node member;exact False.elim (List.not_mem_nil member)
  · intro id bound;exact False.elim (Nat.not_lt_zero id bound)

theorem rawInitial_closed : RawMoyalClosed rawInitial :=
  rawScalar_closed _ _ (rawScalar_closed _ _ raw_empty_closed)


theorem rawRows_words (state : RawArena) (closed : RawMoyalClosed state) (id : ℕ) :
    RawWords (fun node=>node < state.nodes.length) (rawRows state id) := by
  by_cases inside : id < state.polynomials.length
  · exact closed.words _ (rawRows_member state id inside)
  · rw [rawRows,List.getD_eq_default _ _ (by omega)]
    intro row member;exact False.elim (List.not_mem_nil member)

theorem rawAdd_closed (ids : List ℕ) (state : RawArena) (closed : RawMoyalClosed state) :
    RawMoyalClosed (rawAdd ids state).2 := by
  apply rawPoly_closed _ _ closed
  intro row member node hn
  obtain ⟨id,_,hr⟩:=List.mem_flatMap.mp member
  exact rawRows_words state closed id row hr node hn

theorem rawScale_closed (c : NormalizedCoefficient) (id : ℕ) (state : RawArena) (closed : RawMoyalClosed state) :
    RawMoyalClosed (rawScale c id state).2 := by
  apply rawPoly_closed _ _ closed
  intro row member node hn
  obtain ⟨old,ho,rfl⟩:=List.mem_map.mp member
  exact rawRows_words state closed id old ho node hn

theorem rawMultiply_closed (left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state) :
    RawMoyalClosed (rawMultiply left right state).2 := by
  apply rawPoly_closed _ _ closed
  intro row member node hn
  obtain ⟨a,ha,hmap⟩:=List.mem_flatMap.mp member
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hmap
  have original:= (rawOrderWord_perm state (a.word++b.word)).subset hn
  rcases List.mem_append.mp original with h|h
  · exact rawRows_words state closed left a ha node h
  · exact rawRows_words state closed right b hb node h

theorem rawHead_words (state : RawArena) (closed : RawMoyalClosed state) (id : ℕ) :
    ∀ node,node∈((rawRows state id).getD 0 ⟨polynomialCoefficient 0,[]⟩).word → node < state.nodes.length := by
  have words:=rawRows_words state closed id
  cases h : rawRows state id with
  | nil=>simp only [List.getD_nil,List.not_mem_nil,false_implies,implies_true]
  | cons row rows=>
    intro node hn
    simp only [List.getD_cons_zero] at hn
    exact words row (by rw [h];simp) node hn

theorem rawStrip_nodes (id : ℕ) (row : RawRow) (state : RawArena) :
    (rawStrip id row state).2.nodes=state.nodes := by
  classical
  unfold rawStrip
  split_ifs <;> rfl

theorem rawStrip_bound (id : ℕ) (row : RawRow) (state : RawArena) (bound : id < state.polynomials.length) :
    (rawStrip id row state).1 < (rawStrip id row state).2.polynomials.length := by
  classical
  unfold rawStrip
  split_ifs
  · exact rawPoly_bound _ _
  · exact bound

theorem rawStrip_closed (id : ℕ) (row : RawRow) (state : RawArena) (closed : RawMoyalClosed state)
    (words : ∀ node,node∈row.word → node < state.nodes.length) : RawMoyalClosed (rawStrip id row state).2 := by
  classical
  unfold rawStrip
  split_ifs
  · apply rawPoly_closed _ _ closed
    intro other member node hn
    have same:=List.mem_singleton.mp member
    subst other
    exact words node hn
  · exact closed


theorem rawPair_closed (r left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (leftBound : left < state.polynomials.length) (rightBound : right < state.polynomials.length) :
    RawMoyalClosed (rawPair r left right state).2 := by
  classical
  let a:=(rawRows state left).getD 0 ⟨polynomialCoefficient 0,[]⟩
  let b:=(rawRows state right).getD 0 ⟨polynomialCoefficient 0,[]⟩
  let one:=rawStrip left a state
  let two:=rawStrip right b one.2
  have firstClosed : RawMoyalClosed one.2:=rawStrip_closed left a state closed (rawHead_words state closed left)
  have bWords : ∀ node,node∈b.word → node < one.2.nodes.length := by
    rw [show one.2.nodes=state.nodes from rawStrip_nodes _ _ _]
    exact rawHead_words state closed right
  have secondClosed : RawMoyalClosed two.2:=rawStrip_closed right b one.2 firstClosed bWords
  have rightOld : right < one.2.polynomials.length:=
    lt_of_lt_of_le rightBound (rawStrip_extends left a state).polynomials.length_le
  have boundOne : one.1 < two.2.polynomials.length:=
    lt_of_lt_of_le (rawStrip_bound left a state leftBound) (rawStrip_extends right b one.2).polynomials.length_le
  have boundTwo : two.1 < two.2.polynomials.length:=rawStrip_bound right b one.2 rightOld
  dsimp only [rawPair]
  split_ifs
  all_goals first
    | exact secondClosed
    | apply rawScale_closed
      apply rawAtom_closed _ _ _ secondClosed
      intro dep member
      simp only [RawKind.dependencies,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with h|h
      · subst dep;first | exact boundOne | exact boundTwo
      · subst dep;first | exact boundOne | exact boundTwo


theorem rawSequence_closed (base current : RawArena) (actions : List RawAction)
    (extension : RawExtends base current) (closed : RawMoyalClosed current)
    (grows : ∀ action,action∈actions → ∀ state,RawExtends state (action state).2)
    (step : ∀ action,action∈actions → ∀ state,RawExtends base state → RawMoyalClosed state → RawMoyalClosed (action state).2) :
    RawMoyalClosed (rawSequence actions current).2 := by
  induction actions generalizing current with
  | nil=>exact closed
  | cons action actions ih=>
    exact ih (action current).2 (extension.trans (grows action (by simp) current))
      (step action (by simp) current extension closed)
      (fun a h=>grows a (by simp [h])) (fun a h=>step a (by simp [h]))

theorem rawMoyal_closed (r left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (leftBound : left < state.polynomials.length) (rightBound : right < state.polynomials.length) :
    RawMoyalClosed (rawMoyal r left right state).2 := by
  by_cases zero : r=0
  · simp only [rawMoyal,if_pos zero]
    exact rawMultiply_closed _ _ _ closed
  · by_cases vanished : left=0 ∨ right=0
    · simp only [rawMoyal,if_neg zero,if_pos vanished]
      exact closed
    · by_cases splitRows : (rawRows state left).length>1 ∨ (rawRows state right).length>1
      · simp only [rawMoyal,if_neg zero,if_neg vanished,if_pos splitRows]
        apply rawAdd_closed
        apply rawSequence_closed state state _ (RawExtends.refl state) closed
        · intro action member current
          obtain ⟨a,_,ha⟩:=List.mem_flatMap.mp member
          obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
          dsimp only
          split_ifs
          · exact (rawPoly_extends _ _).trans (rawPoly_extends _ _)
          · exact ((rawPoly_extends _ _).trans (rawPoly_extends _ _)).trans (rawPair_extends _ _ _ _)
        · intro action member current extension currentClosed
          obtain ⟨a,ha,hmap⟩:=List.mem_flatMap.mp member
          obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hmap
          have aWords : RawWords (fun node=>node < current.nodes.length) [a] := by
            intro row member node hn
            have same:=List.mem_singleton.mp member
            subst row
            exact lt_of_lt_of_le (rawRows_words state closed left a ha node hn) extension.nodes.length_le
          have firstClosed:=rawPoly_closed [a] current currentClosed aWords
          have secondExtension:=extension.trans (rawPoly_extends [a] current)
          have bWords : RawWords (fun node=>node < (rawPoly [a] current).2.nodes.length) [b] := by
            intro row member node hn
            have same:=List.mem_singleton.mp member
            subst row
            exact lt_of_lt_of_le (rawRows_words state closed right b hb node hn) secondExtension.nodes.length_le
          have secondClosed:=rawPoly_closed [b] (rawPoly [a] current).2 firstClosed bWords
          dsimp only
          split_ifs
          · exact secondClosed
          · exact rawPair_closed _ _ _ _ secondClosed
              (lt_of_lt_of_le (rawPoly_bound [a] current) (rawPoly_extends [b] (rawPoly [a] current).2).polynomials.length_le)
              (rawPoly_bound [b] (rawPoly [a] current).2)
      · simp only [rawMoyal,if_neg zero,if_neg vanished,if_neg splitRows]
        exact rawPair_closed _ _ _ _ closed leftBound rightBound


open PreparationVacuumDAGSemantic

def rawNodeExpression (K : ℕ) (previous : ℕ → ArenaExpression K) (kind : RawKind) : ArenaExpression K :=
  match kind with
  | .source d j=>.source (Fin.castSucc d) j
  | .clock level axis=>if h : level < K then .clock (Fin.succ ⟨level,h⟩) axis else .literal 0
  | .moyal r left right=>.moyal r (previous left) (previous right)

def rawExpandStep (K : ℕ) (state : RawArena) (previous : ℕ → ArenaExpression K) (id : ℕ) : ArenaExpression K :=
  (rawRows state id).foldr (fun row out=>.add
    (.row row.coefficient (row.word.map (fun node=>rawNodeExpression K previous (rawNode state node).kind))) out) (.literal 0)

def rawExpand (K fuel : ℕ) (state : RawArena) : ℕ → ArenaExpression K :=
  Nat.rec (fun _=>.literal 0) (fun _ previous=>rawExpandStep K state previous) fuel

theorem rawNodeExpression_congr (K : ℕ) (kind : RawKind) (left right : ℕ → ArenaExpression K)
    (same : ∀ dep,dep∈kind.dependencies → left dep=right dep) :
    rawNodeExpression K left kind=rawNodeExpression K right kind := by
  cases kind with
  | source d j=>rfl
  | clock l a=>rfl
  | moyal r a b=>simp only [rawNodeExpression,same a (by simp [RawKind.dependencies]),same b (by simp [RawKind.dependencies])]

theorem rawExpandStep_congr (K : ℕ) (state : RawArena) (id : ℕ) (left right : ℕ → ArenaExpression K)
    (same : ∀ row,row∈rawRows state id → ∀ node,node∈row.word →
      ∀ dep,dep∈(rawNode state node).kind.dependencies → left dep=right dep) :
    rawExpandStep K state left id=rawExpandStep K state right id := by
  have fold (rows : List RawRow)
      (paid : ∀ row,row∈rows → ∀ node,node∈row.word → ∀ dep,dep∈(rawNode state node).kind.dependencies → left dep=right dep) :
      rows.foldr (fun row out=>ArenaExpression.add (.row row.coefficient
        (row.word.map (fun node=>rawNodeExpression K left (rawNode state node).kind))) out) (.literal 0)=
      rows.foldr (fun row out=>ArenaExpression.add (.row row.coefficient
        (row.word.map (fun node=>rawNodeExpression K right (rawNode state node).kind))) out) (.literal 0) := by
    induction rows with
    | nil=>rfl
    | cons row rows ih=>
      simp only [List.foldr_cons]
      apply congrArg₂ ArenaExpression.add
      · apply congrArg (ArenaExpression.row row.coefficient)
        apply List.map_congr_left
        intro node hn
        exact rawNodeExpression_congr K _ left right (paid row (by simp) node hn)
      · exact ih (fun r hr=>paid r (by simp [hr]))
  exact fold _ same

theorem rawExpand_stable (K fuel : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (id : ℕ) (valid : id < state.polynomials.length) (paid : id < fuel) :
    rawExpand K (fuel+1) state id=rawExpand K fuel state id := by
  induction fuel generalizing id with
  | zero=>omega
  | succ fuel ih=>
    change rawExpandStep K state (rawExpand K (fuel+1) state) id=
      rawExpandStep K state (rawExpand K fuel state) id
    apply rawExpandStep_congr
    intro row hr node hn dep hd
    have earlier:=closed.earlier id valid row hr node hn dep hd
    exact ih dep (earlier.trans valid) (by omega)

theorem rawExpand_equation (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (id : ℕ) (valid : id < state.polynomials.length) :
    rawExpand K state.polynomials.length state id=
      rawExpandStep K state (rawExpand K state.polynomials.length state) id :=
  (rawExpand_stable K state.polynomials.length state closed id valid valid).symm


theorem rawNormalize_zero : rawNormalize [⟨polynomialCoefficient 0,[]⟩]=[] := by
  simp [rawNormalize,rawDropZero,rawInsertRow,cancelCoefficient,cancelAt,polynomialCoefficient]

theorem rawNormalize_one : rawNormalize [⟨polynomialCoefficient 1,[]⟩]=[⟨polynomialCoefficient 1,[]⟩] := by
  simp [rawNormalize,rawDropZero,rawInsertRow,cancelCoefficient,cancelAt,polynomialCoefficient]

theorem rawInitial_nodes : rawInitial.nodes=[] := rfl

theorem rawInitial_polynomials : rawInitial.polynomials=[[],[⟨polynomialCoefficient 1,[]⟩]] := by
  classical
  simp [rawInitial,rawScalar,rawPoly,rawNormalize_zero,rawNormalize_one,PreparationVacuumSourceSerialization.intern]


theorem rawExpandStep_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (id : ℕ) (valid : id < old.polynomials.length)
    (left right : ℕ → ArenaExpression K) (same : ∀ dep,dep < old.polynomials.length → left dep=right dep) :
    rawExpandStep K next left id=rawExpandStep K old right id := by
  unfold rawExpandStep
  rw [rawRows_preserved extension id valid]
  have fold (rows : List RawRow) (contained : ∀ row,row∈rows → row∈rawRows old id) :
      rows.foldr (fun row out=>ArenaExpression.add (.row row.coefficient
        (row.word.map (fun node=>rawNodeExpression K left (rawNode next node).kind))) out) (.literal 0)=
      rows.foldr (fun row out=>ArenaExpression.add (.row row.coefficient
        (row.word.map (fun node=>rawNodeExpression K right (rawNode old node).kind))) out) (.literal 0) := by
    induction rows with
    | nil=>rfl
    | cons row rows ih=>
      simp only [List.foldr_cons]
      apply congrArg₂ ArenaExpression.add
      · apply congrArg (ArenaExpression.row row.coefficient)
        apply List.map_congr_left
        intro node hn
        have bound:=closed.words (rawRows old id) (rawRows_member old id valid) row (contained row (by simp)) node hn
        rw [rawNode_preserved extension node bound]
        apply rawNodeExpression_congr
        intro dep hd
        exact same dep (closed.nodes (rawNode old node) (rawNode_member old node bound) dep hd)
      · exact ih (fun r hr=>contained r (by simp [hr]))
  exact fold _ (fun _ h=>h)

theorem rawExpand_prefix (K fuel : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (id : ℕ) (valid : id < old.polynomials.length) :
    rawExpand K fuel next id=rawExpand K fuel old id := by
  induction fuel generalizing id with
  | zero=>rfl
  | succ fuel ih=>exact rawExpandStep_prefix K extension closed id valid _ _ ih


def RawInitialized (state : RawArena) : Prop := RawExtends rawInitial state

theorem rawInitialized_positive (state : RawArena) (initialized : RawInitialized state) :
    0 < state.polynomials.length := by
  have size:=initialized.polynomials.length_le
  rw [rawInitial_polynomials] at size
  simp only [List.length_cons,List.length_nil] at size
  omega

theorem rawInitialized_zero (state : RawArena) (initialized : RawInitialized state) : rawRows state 0=[] := by
  rw [rawRows_preserved initialized 0 (by simp [rawInitial_polynomials]),rawRows,rawInitial_polynomials,List.getD_cons_zero]

theorem rawInitialized_one (state : RawArena) (initialized : RawInitialized state) :
    rawRows state 1=[⟨polynomialCoefficient 1,[]⟩] := by
  rw [rawRows_preserved initialized 1 (by simp [rawInitial_polynomials]),rawRows,rawInitial_polynomials]
  rfl

theorem rawPair_bound (r left right : ℕ) (state : RawArena) (initialized : RawInitialized state) :
    (rawPair r left right state).1 < (rawPair r left right state).2.polynomials.length := by
  classical
  have positive:=rawInitialized_positive state initialized
  have zeroBound : 0 < (rawStrip right ((rawRows state right).getD 0 ⟨polynomialCoefficient 0,[]⟩)
      (rawStrip left ((rawRows state left).getD 0 ⟨polynomialCoefficient 0,[]⟩) state).2).2.polynomials.length :=
    lt_of_lt_of_le positive ((rawStrip_extends _ _ _).trans (rawStrip_extends _ _ _)).polynomials.length_le
  dsimp only [rawPair]
  split_ifs
  all_goals first | exact zeroBound | exact rawPoly_bound _ _

theorem rawMoyal_bound (r left right : ℕ) (state : RawArena) (initialized : RawInitialized state) :
    (rawMoyal r left right state).1 < (rawMoyal r left right state).2.polynomials.length := by
  by_cases zero : r=0
  · simp only [rawMoyal,if_pos zero]
    exact rawPoly_bound _ _
  · by_cases vanished : left=0 ∨ right=0
    · simp only [rawMoyal,if_neg zero,if_pos vanished]
      exact rawInitialized_positive _ initialized
    · by_cases splitRows : (rawRows state left).length>1 ∨ (rawRows state right).length>1
      · simp only [rawMoyal,if_neg zero,if_neg vanished,if_pos splitRows]
        exact rawPoly_bound _ _
      · simp only [rawMoyal,if_neg zero,if_neg vanished,if_neg splitRows]
        exact rawPair_bound _ _ _ _ initialized

theorem rawJordan_bound (r left right : ℕ) (state : RawArena) :
    (rawJordan r left right state).1 < (rawJordan r left right state).2.polynomials.length := rawPoly_bound _ _

theorem rawJordan_closed (r left right : ℕ) (state : RawArena)
    (closed : RawMoyalClosed state) (leftBound : left < state.polynomials.length)
    (rightBound : right < state.polynomials.length) : RawMoyalClosed (rawJordan r left right state).2 := by
  apply rawScale_closed
  apply rawAdd_closed
  exact rawMoyal_closed r right left (rawMoyal r left right state).2 (rawMoyal_closed r left right state closed leftBound rightBound)
    (lt_of_lt_of_le rightBound (rawMoyal_extends _ _ _ _).polynomials.length_le)
    (lt_of_lt_of_le leftBound (rawMoyal_extends _ _ _ _).polynomials.length_le)

end LowEnergy.PreparationVacuumSharedPool

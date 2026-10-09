import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationExecutionSourceNative

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeMemo
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumDAGSemantic
open PreparationVacuumDAGCoefficient PreparationVacuumClockSymbol PreparationVacuumCanonicalMoyal
open PreparationVacuumMoyalNormalization PreparationVacuumArenaBudget PreparationVacuumArenaRows PreparationVacuumArenaCollect
open scoped BigOperators Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def interpretedRow (K : ℕ) (state : RawArena) (row : RawRow) : Row K :=
  ⟨row.coefficient,row.word.map (expandedNode K state)⟩

def rowTerm (K : ℕ) (state : RawArena) (row : RawRow) : ArenaExpression K := rowExpression (interpretedRow K state row)

theorem rowTerm_value (K : ℕ) (state : RawArena) (row : RawRow) (x : Phase) :
    arenaEvaluate (rowTerm K state row) x=rawRowValue (fun node=>nativeNode K state node x) row x := by
  simp only [rowTerm,rowExpression,interpretedRow,arenaEvaluate_row,rawRowValue,List.foldr_map,
    nativeNode,List.prod_eq_foldr]

theorem rowsExpression_interpreted (K : ℕ) (state : RawArena) (rows : List RawRow) (x : Phase) :
    arenaEvaluate (rowsExpression (rows.map (interpretedRow K state))) x=
      rawRowsValue (fun node=>nativeNode K state node x) rows x := by
  induction rows with
  | nil=>rfl
  | cons row rows ih=>
    change arenaEvaluate (rowTerm K state row) x+arenaEvaluate (rowsExpression (rows.map (interpretedRow K state))) x=_
    rw [rowTerm_value,ih]
    rfl

theorem nativePolynomial_rowsExpression (K : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (id : ℕ) (valid : Handle state id) :
    nativePolynomial K state id=arenaEvaluate (rowsExpression ((rawRows state id).map (interpretedRow K state))) := by
  funext x
  rw [nativePolynomial_rows K state closed id valid x,rowsExpression_interpreted]

theorem rowTerm_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (row : RawRow) (words : ∀ node,node∈row.word → node < old.nodes.length) :
    rowTerm K next row=rowTerm K old row := by
  unfold rowTerm interpretedRow
  congr 2
  apply List.map_congr_left
  intro node member
  exact expandedNode_prefix K extension closed node (words node member)

theorem rightExpansion_sum {K : ℕ} (r : ℕ) (left : Row K) (right : List (Row K))
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rightExpansion r left right) x=
      (right.map (fun row=>complexMoyal r (arenaEvaluate (rowExpression left)) (arenaEvaluate (rowExpression row)) x)).sum := by
  induction right with
  | nil=>rfl
  | cons row rows ih=>
    change arenaEvaluate (rowPair r left row) x+arenaEvaluate (rightExpansion r left rows) x=_
    rw [rowPair_source r left row x hx,ih]
    rfl

theorem pairExpansion_sum {K : ℕ} (r : ℕ) (left right : List (Row K))
    (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (pairExpansion r left right) x=
      (left.map (fun a=>(right.map (fun b=>complexMoyal r (arenaEvaluate (rowExpression a)) (arenaEvaluate (rowExpression b)) x)).sum)).sum := by
  induction left with
  | nil=>rfl
  | cons row rows ih=>
    change arenaEvaluate (rightExpansion r row right) x+arenaEvaluate (pairExpansion r rows right) x=_
    rw [rightExpansion_sum r row right x hx,ih]
    rfl

theorem native_moyal_rows (K r left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (leftValid : Handle state left) (rightValid : Handle state right) (x : Phase) (hx : x∈poleDomain) :
    complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) x=
      ((rawRows state left).map (fun a=>((rawRows state right).map
        (fun b=>complexMoyal r (arenaEvaluate (rowTerm K state a)) (arenaEvaluate (rowTerm K state b)) x)).sum)).sum := by
  rw [nativePolynomial_rowsExpression K state closed left leftValid,
    nativePolynomial_rowsExpression K state closed right rightValid,←pairExpansion_source r _ _ x hx,
    pairExpansion_sum r _ _ x hx]
  simp only [List.map_map,Function.comp_def,rowTerm]

theorem rawNormalize_singleton_length (row : RawRow) : (rawNormalize [row]).length ≤ 1 := by
  classical
  unfold rawNormalize rawDropZero
  simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,rawInsertRow]
  rw [List.length_mergeSort]
  exact (List.length_filter_le _ _).trans (by rfl)

theorem rawPoly_single_length (row : RawRow) (state : RawArena) :
    (rawRows (rawPoly [row] state).2 (rawPoly [row] state).1).length ≤ 1 := by
  rw [rawPoly_reference]
  exact rawNormalize_singleton_length row

theorem rawPoly_row_native (K : ℕ) (row : RawRow) (state : RawArena) (closed : RawMoyalClosed state)
    (words : ∀ node,node∈row.word → node < state.nodes.length) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawPoly [row] state).2 (rawPoly [row] state).1 x=arenaEvaluate (rowTerm K state row) x := by
  rw [rawPoly_native K [row] state closed (by
    intro other member node present
    have same:=List.mem_singleton.mp member
    subst other
    exact words node present) x hx,rowTerm_value]
  simp only [rawRowsValue,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]

theorem rawPoly_row_germ (K : ℕ) (row : RawRow) (state : RawArena) (closed : RawMoyalClosed state)
    (words : ∀ node,node∈row.word → node < state.nodes.length) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawPoly [row] state).2 (rawPoly [row] state).1=ᶠ[𝓝 x]arenaEvaluate (rowTerm K state row) := by
  filter_upwards [poleDomain_open.mem_nhds hx] with y hy
  exact rawPoly_row_native K row state closed words y hy


def rawSplitPair (r : ℕ) (a b : RawRow) : RawAction := fun current=>
  let one:=rawPoly [a] current
  let two:=rawPoly [b] one.2
  if one.1=0 ∨ two.1=0 then (0,two.2) else rawPair r one.1 two.1 two.2

theorem rawSplitPair_extends (r : ℕ) (a b : RawRow) (state : RawArena) : RawExtends state (rawSplitPair r a b state).2 := by
  dsimp only [rawSplitPair]
  split_ifs
  · exact (rawPoly_extends _ _).trans (rawPoly_extends _ _)
  · exact ((rawPoly_extends _ _).trans (rawPoly_extends _ _)).trans (rawPair_extends _ _ _ _)

theorem rawSplitPair_closed_bound (r : ℕ) (a b : RawRow) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state)
    (aWords : ∀ node,node∈a.word → node < state.nodes.length)
    (bWords : ∀ node,node∈b.word → node < state.nodes.length) :
    RawMoyalClosed (rawSplitPair r a b state).2 ∧ Handle (rawSplitPair r a b state).2 (rawSplitPair r a b state).1 := by
  let one:=rawPoly [a] state
  let two:=rawPoly [b] one.2
  have hOne : RawMoyalClosed one.2 := rawPoly_closed _ _ closed (by
    intro row member node hn
    have equal:=List.mem_singleton.mp member
    subst row;exact aWords node hn)
  have hTwo : RawMoyalClosed two.2 := rawPoly_closed _ _ hOne (by
    intro row member node hn
    have equal:=List.mem_singleton.mp member
    subst row;exact bWords node hn)
  have initializedTwo : RawInitialized two.2 := (initialized.trans (rawPoly_extends _ _)).trans (rawPoly_extends _ _)
  dsimp only [rawSplitPair]
  split_ifs
  · exact ⟨hTwo,rawInitialized_positive _ initializedTwo⟩
  · exact ⟨rawPair_closed r one.1 two.1 two.2 hTwo
      (handle_extend (rawPoly_extends [b] one.2) (rawPoly_bound [a] state)) (rawPoly_bound [b] one.2),
      rawPair_bound r one.1 two.1 two.2 initializedTwo⟩

theorem rawSplitPair_native (K r : ℕ) (a b : RawRow) (state : RawArena)
    (closed : RawMoyalClosed state) (initialized : RawInitialized state)
    (aWords : ∀ node,node∈a.word → node < state.nodes.length)
    (bWords : ∀ node,node∈b.word → node < state.nodes.length)
    (positive : r≠0) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawSplitPair r a b state).2 (rawSplitPair r a b state).1 x=
      complexMoyal r (arenaEvaluate (rowTerm K state a)) (arenaEvaluate (rowTerm K state b)) x := by
  let one:=rawPoly [a] state
  let two:=rawPoly [b] one.2
  have hOne : RawMoyalClosed one.2 := rawPoly_closed _ _ closed (by
    intro row member node hn
    have equal:=List.mem_singleton.mp member
    subst row;exact aWords node hn)
  have hTwo : RawMoyalClosed two.2 := rawPoly_closed _ _ hOne (by
    intro row member node hn
    have equal:=List.mem_singleton.mp member
    subst row;exact bWords node hn)
  have initializedTwo : RawInitialized two.2 := (initialized.trans (rawPoly_extends _ _)).trans (rawPoly_extends _ _)
  have leftValid : Handle two.2 one.1 := handle_extend (rawPoly_extends [b] one.2) (rawPoly_bound [a] state)
  have rightValid : Handle two.2 two.1 := rawPoly_bound [b] one.2
  have leftGerm : nativePolynomial K two.2 one.1=ᶠ[𝓝 x]arenaEvaluate (rowTerm K state a) := by
    rw [nativePolynomial_prefix K (rawPoly_extends [b] one.2) hOne one.1 (rawPoly_bound [a] state)]
    exact rawPoly_row_germ K a state closed aWords x hx
  have rightGerm : nativePolynomial K two.2 two.1=ᶠ[𝓝 x]arenaEvaluate (rowTerm K state b) := by
    have h:=rawPoly_row_germ K b one.2 hOne bWords x hx
    rw [rowTerm_prefix K (rawPoly_extends [a] state) closed b bWords] at h
    exact h
  have splitValue : nativePolynomial K (rawSplitPair r a b state).2 (rawSplitPair r a b state).1 x=
      complexMoyal r (nativePolynomial K two.2 one.1) (nativePolynomial K two.2 two.1) x := by
    dsimp only [rawSplitPair]
    split_ifs with zero
    · rw [native_zero K two.2 hTwo initializedTwo]
      rcases zero with hl|hr
      · change one.1=0 at hl
        rw [hl,native_zero K two.2 hTwo initializedTwo]
        exact (moyal_zero_left r (nativePolynomial K two.2 two.1) x).symm
      · change two.1=0 at hr
        rw [hr,native_zero K two.2 hTwo initializedTwo]
        exact (moyal_zero_right r (nativePolynomial K two.2 one.1) x).symm
    · apply rawPair_native K r one.1 two.1 two.2 hTwo initializedTwo leftValid rightValid ?_ ?_ positive x hx
      · rw [rawRows_preserved (rawPoly_extends [b] one.2) one.1 (rawPoly_bound [a] state)]
        exact rawPoly_single_length a state
      · exact rawPoly_single_length b one.2
  exact splitValue.trans (moyal_germ r _ _ _ _ x leftGerm rightGerm)

-- Ordinary sequencing law. Every use below supplies source-owned primitive
-- proofs; the generated source consumers take no realization argument.
theorem rawSequence_native_values {α : Type} (K : ℕ) (base current : RawArena) (items : List α)
    (action : α → RawAction) (value : α → Phase → ℂ)
    (extension : RawExtends base current) (closed : RawMoyalClosed current) (initialized : RawInitialized current)
    (grows : ∀ a,a∈items → ∀ state,RawExtends state (action a state).2)
    (preserves : ∀ a,a∈items → ∀ state,RawExtends base state → RawMoyalClosed state → RawInitialized state →
      RawMoyalClosed (action a state).2 ∧ Handle (action a state).2 (action a state).1)
    (readback : ∀ a,a∈items → ∀ state,RawExtends base state → RawMoyalClosed state → RawInitialized state →
      ∀ x,x∈poleDomain → nativePolynomial K (action a state).2 (action a state).1 x=value a x) :
    let result:=rawSequence (items.map action) current
    RawMoyalClosed result.2 ∧ RawInitialized result.2 ∧ ListHandles result.2 result.1 ∧
      ∀ x,x∈poleDomain → (result.1.map (fun id=>nativePolynomial K result.2 id x))=items.map (fun a=>value a x) := by
  induction items generalizing current with
  | nil=>exact ⟨closed,initialized,fun id member=>False.elim (List.not_mem_nil member),fun _ _=>rfl⟩
  | cons a items ih=>
    have one:=preserves a (by simp) current extension closed initialized
    have tail:=ih (action a current).2 (extension.trans (grows a (by simp) current)) one.1
      (initialized.trans (grows a (by simp) current))
      (fun b h=>grows b (List.mem_cons_of_mem _ h))
      (fun b h=>preserves b (List.mem_cons_of_mem _ h))
      (fun b h=>readback b (List.mem_cons_of_mem _ h))
    have tailGrow : RawExtends (action a current).2 (rawSequence (items.map action) (action a current).2).2 := by
      apply rawSequence_extends
      intro f member state
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp member
      exact grows b (List.mem_cons_of_mem _ hb) state
    refine ⟨tail.1,tail.2.1,?_,?_⟩
    · intro id member
      rcases List.mem_cons.mp member with equal|old
      · subst id;exact handle_extend tailGrow one.2
      · exact tail.2.2.1 id old
    · intro x hx
      change nativePolynomial K (rawSequence (items.map action) (action a current).2).2 (action a current).1 x::
        ((rawSequence (items.map action) (action a current).2).1.map (fun id=>nativePolynomial K
          (rawSequence (items.map action) (action a current).2).2 id x))=_
      rw [nativePolynomial_prefix K tailGrow one.1 (action a current).1 one.2,
        readback a (by simp) current extension closed initialized x hx,tail.2.2.2 x hx]
      rfl


def rowPairs (left right : List RawRow) : List (RawRow × RawRow) :=
  left.flatMap (fun a=>right.map (fun b=>(a,b)))

theorem rowPairs_sum (left right : List RawRow) (value : RawRow × RawRow → ℂ) :
    ((rowPairs left right).map value).sum=(left.map (fun a=>(right.map (fun b=>value (a,b))).sum)).sum := by
  induction left with
  | nil=>rfl
  | cons a left ih=>
    simp only [rowPairs,List.flatMap_cons,List.map_append,List.sum_append,List.map_map,Function.comp_def,
      List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]

theorem rawMoyal_split (r left right : ℕ) (state : RawArena) (positive : r≠0) (nonzero : ¬(left=0 ∨ right=0))
    (many : (rawRows state left).length>1 ∨ (rawRows state right).length>1) :
    rawMoyal r left right state=
      let result:=rawSequence ((rowPairs (rawRows state left) (rawRows state right)).map (fun pair=>rawSplitPair r pair.1 pair.2)) state
      rawAdd result.1 result.2 := by
  simp only [rawMoyal,if_neg positive,if_neg nonzero,if_pos many,rowPairs,List.map_flatMap,List.map_map,
    Function.comp_def]
  rfl

theorem rawMoyal_native (K r left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (initialized : RawInitialized state) (leftValid : Handle state left) (rightValid : Handle state right)
    (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawMoyal r left right state).2 (rawMoyal r left right state).1 x=
      complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) x := by
  by_cases zeroOrder : r=0
  · subst r
    change nativePolynomial K (rawMultiply left right state).2 (rawMultiply left right state).1 x=complexMoyal 0 _ _ x
    rw [rawMultiply_native K left right state closed leftValid rightValid x hx,complexMoyal_zero]
  · by_cases zero : left=0 ∨ right=0
    · simp only [rawMoyal,if_neg zeroOrder,if_pos zero]
      rw [native_zero K state closed initialized]
      rcases zero with hl|hr
      · subst left
        rw [native_zero K state closed initialized]
        exact (moyal_zero_left r (nativePolynomial K state right) x).symm
      · subst right
        rw [native_zero K state closed initialized]
        exact (moyal_zero_right r (nativePolynomial K state left) x).symm
    · by_cases many : (rawRows state left).length>1 ∨ (rawRows state right).length>1
      · let pairs:=rowPairs (rawRows state left) (rawRows state right)
        let action:=fun pair : RawRow × RawRow=>rawSplitPair r pair.1 pair.2
        let value:=fun pair : RawRow × RawRow=>complexMoyal r
          (arenaEvaluate (rowTerm K state pair.1)) (arenaEvaluate (rowTerm K state pair.2))
        have emitted:=rawSequence_native_values K state state pairs action value (RawExtends.refl _) closed initialized
          (fun pair _ current=>rawSplitPair_extends r pair.1 pair.2 current) (by
            intro pair member current extension currentClosed currentInitialized
            obtain ⟨a,ha,hm⟩:=List.mem_flatMap.mp member
            obtain ⟨b,hb,same⟩:=List.mem_map.mp hm
            subst pair
            exact rawSplitPair_closed_bound r a b current currentClosed currentInitialized
              (fun node hn=>lt_of_lt_of_le (rawRows_words state closed left a ha node hn) extension.nodes.length_le)
              (fun node hn=>lt_of_lt_of_le (rawRows_words state closed right b hb node hn) extension.nodes.length_le)) (by
            intro pair member current extension currentClosed currentInitialized y hy
            obtain ⟨a,ha,hm⟩:=List.mem_flatMap.mp member
            obtain ⟨b,hb,same⟩:=List.mem_map.mp hm
            subst pair
            have aWords:=rawRows_words state closed left a ha
            have bWords:=rawRows_words state closed right b hb
            rw [rawSplitPair_native K r a b current currentClosed currentInitialized
              (fun node hn=>lt_of_lt_of_le (aWords node hn) extension.nodes.length_le)
              (fun node hn=>lt_of_lt_of_le (bWords node hn) extension.nodes.length_le) zeroOrder y hy,
              rowTerm_prefix K extension closed a aWords,rowTerm_prefix K extension closed b bWords])
        rw [rawMoyal_split r left right state zeroOrder zero many]
        rw [rawAdd_native K _ _ emitted.1 emitted.2.2.1 x hx,emitted.2.2.2 x hx]
        rw [rowPairs_sum,native_moyal_rows K r left right state closed leftValid rightValid x hx]
      · have leftSingle : (rawRows state left).length ≤ 1 := by omega
        have rightSingle : (rawRows state right).length ≤ 1 := by omega
        simp only [rawMoyal,if_neg zeroOrder,if_neg zero,if_neg many]
        exact rawPair_native K r left right state closed initialized leftValid rightValid leftSingle rightSingle zeroOrder x hx

theorem rawMoyal_native_germ (K r left right : ℕ) (state : RawArena) (closed : RawMoyalClosed state)
    (initialized : RawInitialized state) (leftValid : Handle state left) (rightValid : Handle state right)
    (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (rawMoyal r left right state).2 (rawMoyal r left right state).1=ᶠ[𝓝 x]
      complexMoyal r (nativePolynomial K state left) (nativePolynomial K state right) := by
  filter_upwards [poleDomain_open.mem_nhds hx] with y hy
  exact rawMoyal_native K r left right state closed initialized leftValid rightValid y hy

theorem actual_moyal_native_all_jets (order r : ℕ)
    (left right : Fin (originalEngine order).runtime.arena.polynomials.length)
    (x : Phase) (hx : x∈poleDomain) (directions : List Phase) :
    complexListJet directions
      (nativePolynomial order (rawMoyal r left.val right.val (originalEngine order).runtime.arena).2
        (rawMoyal r left.val right.val (originalEngine order).runtime.arena).1) x=
      complexListJet directions (complexMoyal r
        (nativePolynomial order (originalEngine order).runtime.arena left.val)
        (nativePolynomial order (originalEngine order).runtime.arena right.val)) x :=
  (complexListJet_germ (rawMoyal_native_germ order r left.val right.val (originalEngine order).runtime.arena
    (originalEngine_graph_closed order) (originalEngine_initialized order) left.isLt right.isLt x hx) directions).eq_of_nhds

end LowEnergy.PreparationVacuumNativeMemo

import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationMemoRowExpansion

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeMemo
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumDAGSemantic
open PreparationVacuumDAGCoefficient PreparationVacuumClockSymbol PreparationVacuumCanonicalMoyal
open PreparationVacuumMoyalNormalization PreparationVacuumArenaBudget PreparationVacuumArenaRows
open scoped BigOperators Topology

structure CachedNative (K : ℕ) (runtime : RawRuntime) : Prop where
  handles : RuntimeHandles runtime
  moyal : ∀ entry,entry∈runtime.moyalMemo →
    Handle runtime.arena entry.1.2.1 ∧ Handle runtime.arena entry.1.2.2 ∧
    ∀ x,x∈poleDomain → nativePolynomial K runtime.arena entry.2 x=
      complexMoyal entry.1.1 (nativePolynomial K runtime.arena entry.1.2.1)
        (nativePolynomial K runtime.arena entry.1.2.2) x

theorem initial_cachedNative (K : ℕ) : CachedNative K (⟨rawInitial,[],[],[],[]⟩ : RawRuntime) :=
  ⟨initial_handles,fun _entry member=>False.elim (List.not_mem_nil member)⟩

theorem CachedNative.withArena {K : ℕ} {runtime : RawRuntime} (valid : CachedNative K runtime)
    (next : RawArena) (extension : RawExtends runtime.arena next) (closed : RawMoyalClosed next) :
    CachedNative K {runtime with arena:=next} := by
  refine ⟨valid.handles.withArena next extension closed,?_⟩
  intro entry member
  have old:=valid.moyal entry member
  refine ⟨handle_extend extension old.1,handle_extend extension old.2.1,?_⟩
  intro x hx
  rw [nativePolynomial_prefix K extension valid.handles.closed entry.2 (valid.handles.moyal entry member),
    nativePolynomial_prefix K extension valid.handles.closed entry.1.2.1 old.1,
    nativePolynomial_prefix K extension valid.handles.closed entry.1.2.2 old.2.1]
  exact old.2.2 x hx

theorem memoLookup_entry {κ α : Type} [DecidableEq κ] (key : κ) (entries : List (κ × α))
    (value : α) (found : memoLookup key entries=some value) : (key,value)∈entries := by
  unfold memoLookup at found
  obtain ⟨entry,hentry,heq⟩:=Option.map_eq_some_iff.mp found
  have keyEq : entry.1=key := by simpa only [decide_eq_true_eq] using List.find?_some hentry
  have same : entry=(key,value) := Prod.ext keyEq heq
  rw [←same]
  exact List.mem_of_find?_eq_some hentry

theorem runArena_cached {K : ℕ} (action : RawAction)
    (grows : ∀ state,RawExtends state (action state).2)
    (preserves : ∀ state,RawMoyalClosed state → RawMoyalClosed (action state).2)
    (returns : ∀ state,RawInitialized state → Handle (action state).2 (action state).1)
    (runtime : RawRuntime) (valid : CachedNative K runtime) :
    CachedNative K (runArena action runtime).2 ∧ Handle (runArena action runtime).2.arena (runArena action runtime).1 :=
  ⟨valid.withArena _ (grows _) (preserves _ valid.handles.closed),returns _ valid.handles.initialized⟩

theorem runPoly_cached {K : ℕ} (rows : List RawRow) (runtime : RawRuntime) (valid : CachedNative K runtime)
    (words : RawWords (fun node=>node < runtime.arena.nodes.length) rows) :
    CachedNative K (runArena (rawPoly rows) runtime).2 ∧ Handle (runArena (rawPoly rows) runtime).2.arena (runArena (rawPoly rows) runtime).1 :=
  ⟨valid.withArena _ (rawPoly_extends _ _) (rawPoly_closed _ _ valid.handles.closed words),rawPoly_bound _ _⟩

-- Cache admission consumes the primitive operation's proved native law and the
-- actual extending runtime; it does not choose a replacement stored value.
theorem cacheMoyalResult_native (K r left right : ℕ) (before : RawRuntime) (result : ℕ × RawRuntime)
    (validBefore : CachedNative K before) (validResult : CachedNative K result.2)
    (extension : RawExtends before.arena result.2.arena)
    (leftValid : Handle before.arena left) (rightValid : Handle before.arena right)
    (resultValid : Handle result.2.arena result.1)
    (operation : ∀ x,x∈poleDomain → nativePolynomial K result.2.arena result.1 x=
      complexMoyal r (nativePolynomial K before.arena left) (nativePolynomial K before.arena right) x) :
    CachedNative K (cacheMoyalResult (r,left,right) result).2 ∧
      Handle (cacheMoyalResult (r,left,right) result).2.arena (cacheMoyalResult (r,left,right) result).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (cacheMoyalResult (r,left,right) result).2.arena
        (cacheMoyalResult (r,left,right) result).1 x=
        complexMoyal r (nativePolynomial K before.arena left) (nativePolynomial K before.arena right) x := by
  refine ⟨⟨(cacheMoyalResult_handles _ result validResult.handles resultValid).1,?_⟩,resultValid,operation⟩
  intro entry member
  rcases List.mem_cons.mp member with equal|old
  · subst entry
    refine ⟨handle_extend extension leftValid,handle_extend extension rightValid,?_⟩
    intro x hx
    change nativePolynomial K result.2.arena result.1 x=complexMoyal r
      (nativePolynomial K result.2.arena left) (nativePolynomial K result.2.arena right) x
    rw [nativePolynomial_prefix K extension validBefore.handles.closed left leftValid,
      nativePolynomial_prefix K extension validBefore.handles.closed right rightValid]
    exact operation x hx
  · exact validResult.moyal entry old

theorem memoPair_native (K r left right : ℕ) (runtime : RawRuntime) (valid : CachedNative K runtime)
    (leftValid : Handle runtime.arena left) (rightValid : Handle runtime.arena right)
    (leftSingle : (rawRows runtime.arena left).length ≤ 1) (rightSingle : (rawRows runtime.arena right).length ≤ 1)
    (positive : r≠0) :
    CachedNative K (memoPair r left right runtime).2 ∧
      Handle (memoPair r left right runtime).2.arena (memoPair r left right runtime).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (memoPair r left right runtime).2.arena (memoPair r left right runtime).1 x=
        complexMoyal r (nativePolynomial K runtime.arena left) (nativePolynomial K runtime.arena right) x := by
  dsimp only [memoPair]
  split
  · rename_i id found
    have member:=memoLookup_entry (r,left,right) runtime.moyalMemo id found
    exact ⟨valid,valid.handles.moyal _ member,(valid.moyal _ member).2.2⟩
  · by_cases zero : left=0 ∨ right=0
    · simp only [if_pos zero]
      apply cacheMoyalResult_native K r left right runtime (0,runtime) valid valid (RawExtends.refl _)
        leftValid rightValid (zero_handle valid.handles)
      intro x hx
      rw [native_zero K runtime.arena valid.handles.closed valid.handles.initialized]
      rcases zero with hl|hr
      · subst left
        rw [native_zero K runtime.arena valid.handles.closed valid.handles.initialized]
        exact (moyal_zero_left r (nativePolynomial K runtime.arena right) x).symm
      · subst right
        rw [native_zero K runtime.arena valid.handles.closed valid.handles.initialized]
        exact (moyal_zero_right r (nativePolynomial K runtime.arena left) x).symm
    · simp only [if_neg zero]
      have resultClosed:=rawPair_closed r left right runtime.arena valid.handles.closed leftValid rightValid
      have resultValid:=rawPair_bound r left right runtime.arena valid.handles.initialized
      apply cacheMoyalResult_native K r left right runtime (runArena (rawPair r left right) runtime) valid
        (valid.withArena _ (rawPair_extends _ _ _ _) resultClosed) (rawPair_extends _ _ _ _)
        leftValid rightValid resultValid
      exact fun x hx=>rawPair_native K r left right runtime.arena valid.handles.closed valid.handles.initialized
        leftValid rightValid leftSingle rightSingle positive x hx


def memoSplitPair (r : ℕ) (a b : RawRow) : RuntimeAction ℕ := fun current=>
  let one:=runArena (rawPoly [a]) current
  let two:=runArena (rawPoly [b]) one.2
  memoPair r one.1 two.1 two.2

theorem memoSplitPair_grows (r : ℕ) (a b : RawRow) : RuntimeGrows (memoSplitPair r a b) := by
  intro runtime
  let one:=runArena (rawPoly [a]) runtime
  let two:=runArena (rawPoly [b]) one.2
  exact ((rawPoly_extends [a] runtime.arena).trans (rawPoly_extends [b] one.2.arena)).trans
    (memoPair_grows r one.1 two.1 two.2)

theorem memoSplitPair_native (K r : ℕ) (a b : RawRow) (runtime : RawRuntime) (valid : CachedNative K runtime)
    (aWords : ∀ node,node∈a.word → node < runtime.arena.nodes.length)
    (bWords : ∀ node,node∈b.word → node < runtime.arena.nodes.length) (positive : r≠0) :
    CachedNative K (memoSplitPair r a b runtime).2 ∧
      Handle (memoSplitPair r a b runtime).2.arena (memoSplitPair r a b runtime).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (memoSplitPair r a b runtime).2.arena (memoSplitPair r a b runtime).1 x=
        complexMoyal r (arenaEvaluate (rowTerm K runtime.arena a)) (arenaEvaluate (rowTerm K runtime.arena b)) x := by
  let one:=runArena (rawPoly [a]) runtime
  let two:=runArena (rawPoly [b]) one.2
  have first:=runPoly_cached [a] runtime valid (by
    intro row member node hn
    have equal:=List.mem_singleton.mp member
    subst row;exact aWords node hn)
  have second:=runPoly_cached [b] one.2 first.1 (by
    intro row member node hn
    have equal:=List.mem_singleton.mp member
    subst row;exact bWords node hn)
  have oneGrow : RawExtends runtime.arena one.2.arena := rawPoly_extends [a] runtime.arena
  have twoGrow : RawExtends one.2.arena two.2.arena := rawPoly_extends [b] one.2.arena
  have leftValid : Handle two.2.arena one.1 := handle_extend (rawPoly_extends [b] one.2.arena) first.2
  have leftSingle : (rawRows two.2.arena one.1).length ≤ 1 := by
    rw [rawRows_preserved twoGrow one.1 first.2]
    exact rawPoly_single_length a runtime.arena
  have result:=memoPair_native K r one.1 two.1 two.2 second.1 leftValid second.2 leftSingle
    (rawPoly_single_length b one.2.arena) positive
  refine ⟨result.1,result.2.1,?_⟩
  intro x hx
  rw [show nativePolynomial K (memoSplitPair r a b runtime).2.arena (memoSplitPair r a b runtime).1 x=
    complexMoyal r (nativePolynomial K two.2.arena one.1) (nativePolynomial K two.2.arena two.1) x from result.2.2 x hx]
  apply moyal_germ r _ _ _ _ x
  · rw [nativePolynomial_prefix K twoGrow first.1.handles.closed one.1 first.2]
    exact rawPoly_row_germ K a runtime.arena valid.handles.closed aWords x hx
  · have h:=rawPoly_row_germ K b one.2.arena first.1.handles.closed bWords x hx
    rw [rowTerm_prefix K oneGrow valid.handles.closed b bWords] at h
    exact h

theorem runtimeSequence_native_values {α : Type} (K : ℕ) (base current : RawRuntime) (items : List α)
    (action : α → RuntimeAction ℕ) (value : α → Phase → ℂ)
    (extension : RawExtends base.arena current.arena) (valid : CachedNative K current)
    (grows : ∀ a,a∈items → RuntimeGrows (action a))
    (step : ∀ a,a∈items → ∀ state,RawExtends base.arena state.arena → CachedNative K state →
      CachedNative K (action a state).2 ∧ Handle (action a state).2.arena (action a state).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (action a state).2.arena (action a state).1 x=value a x) :
    let result:=runtimeSequence (items.map action) current
    CachedNative K result.2 ∧ ListHandles result.2.arena result.1 ∧
      ∀ x,x∈poleDomain → (result.1.map (fun id=>nativePolynomial K result.2.arena id x))=items.map (fun a=>value a x) := by
  induction items generalizing current with
  | nil=>exact ⟨valid,fun id member=>False.elim (List.not_mem_nil member),fun _ _=>rfl⟩
  | cons a items ih=>
    have one:=step a (by simp) current extension valid
    have tail:=ih (action a current).2 (extension.trans (grows a (by simp) current)) one.1
      (fun b h=>grows b (List.mem_cons_of_mem _ h))
      (fun b h=>step b (List.mem_cons_of_mem _ h))
    have tailGrow : RawExtends (action a current).2.arena (runtimeSequence (items.map action) (action a current).2).2.arena := by
      apply runtimeSequence_grows
      intro f member state
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp member
      exact grows b (List.mem_cons_of_mem _ hb) state
    refine ⟨tail.1,?_,?_⟩
    · intro id member
      rcases List.mem_cons.mp member with equal|old
      · subst id;exact handle_extend tailGrow one.2.1
      · exact tail.2.1 id old
    · intro x hx
      change nativePolynomial K (runtimeSequence (items.map action) (action a current).2).2.arena (action a current).1 x::
        ((runtimeSequence (items.map action) (action a current).2).1.map (fun id=>nativePolynomial K
          (runtimeSequence (items.map action) (action a current).2).2.arena id x))=_
      rw [nativePolynomial_prefix K tailGrow one.1.handles.closed (action a current).1 one.2.1,
        one.2.2 x hx,tail.2.2 x hx]
      rfl


def moyalMiss (r left right : ℕ) : RuntimeAction ℕ := fun runtime=>
  if r=0 then runArena (rawMultiply left right) runtime else
    if left=0 ∨ right=0 then (0,runtime) else
      let ls:=rawRows runtime.arena left
      let rs:=rawRows runtime.arena right
      if ls.length > 1 ∨ rs.length > 1 then
        let actions:=ls.flatMap (fun a=>rs.map (fun b=>memoSplitPair r a b))
        let expanded:=runtimeSequence actions runtime
        runArena (rawAdd expanded.1) expanded.2
      else runArena (rawPair r left right) runtime

theorem memoMoyal_miss (r left right : ℕ) (runtime : RawRuntime)
    (missing : memoLookup (r,left,right) runtime.moyalMemo=none) :
    memoMoyal r left right runtime=cacheMoyalResult (r,left,right) (moyalMiss r left right runtime) := by
  simp only [memoMoyal,missing]
  rfl

theorem moyalMiss_grows (r left right : ℕ) : RuntimeGrows (moyalMiss r left right) := by
  intro runtime
  dsimp only [moyalMiss]
  split_ifs
  · exact rawMultiply_extends _ _ _
  · exact RawExtends.refl _
  · apply RawExtends.trans (runtimeSequence_grows _ ?_ runtime)
    · exact rawAdd_extends _ _
    · intro action member current
      obtain ⟨a,_,hm⟩:=List.mem_flatMap.mp member
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp hm
      exact memoSplitPair_grows _ _ _ current
  · exact rawPair_extends _ _ _ _

theorem moyalMiss_split (r left right : ℕ) (runtime : RawRuntime) (positive : r≠0)
    (nonzero : ¬(left=0 ∨ right=0))
    (many : (rawRows runtime.arena left).length>1 ∨ (rawRows runtime.arena right).length>1) :
    moyalMiss r left right runtime=
      let result:=runtimeSequence ((rowPairs (rawRows runtime.arena left) (rawRows runtime.arena right)).map
        (fun pair=>memoSplitPair r pair.1 pair.2)) runtime
      runArena (rawAdd result.1) result.2 := by
  simp only [moyalMiss,if_neg positive,if_neg nonzero,if_pos many,rowPairs,List.map_flatMap,List.map_map,Function.comp_def]

theorem moyalMiss_native (K r left right : ℕ) (runtime : RawRuntime) (valid : CachedNative K runtime)
    (leftValid : Handle runtime.arena left) (rightValid : Handle runtime.arena right) :
    CachedNative K (moyalMiss r left right runtime).2 ∧
      Handle (moyalMiss r left right runtime).2.arena (moyalMiss r left right runtime).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (moyalMiss r left right runtime).2.arena (moyalMiss r left right runtime).1 x=
        complexMoyal r (nativePolynomial K runtime.arena left) (nativePolynomial K runtime.arena right) x := by
  by_cases zeroOrder : r=0
  · subst r
    have generated:=runArena_cached (rawMultiply left right) (rawMultiply_extends left right)
      (rawMultiply_closed left right) (fun _ _=>rawPoly_bound _ _) runtime valid
    change CachedNative K (runArena (rawMultiply left right) runtime).2 ∧
      Handle (runArena (rawMultiply left right) runtime).2.arena (runArena (rawMultiply left right) runtime).1 ∧ _
    refine ⟨generated.1,generated.2,?_⟩
    intro x hx
    change nativePolynomial K (rawMultiply left right runtime.arena).2 (rawMultiply left right runtime.arena).1 x=_
    rw [rawMultiply_native K left right runtime.arena valid.handles.closed leftValid rightValid x hx,complexMoyal_zero]
  · by_cases zero : left=0 ∨ right=0
    · simp only [moyalMiss,if_neg zeroOrder,if_pos zero]
      refine ⟨valid,zero_handle valid.handles,?_⟩
      intro x hx
      rw [native_zero K runtime.arena valid.handles.closed valid.handles.initialized]
      rcases zero with hl|hr
      · subst left
        rw [native_zero K runtime.arena valid.handles.closed valid.handles.initialized]
        exact (moyal_zero_left r (nativePolynomial K runtime.arena right) x).symm
      · subst right
        rw [native_zero K runtime.arena valid.handles.closed valid.handles.initialized]
        exact (moyal_zero_right r (nativePolynomial K runtime.arena left) x).symm
    · by_cases many : (rawRows runtime.arena left).length>1 ∨ (rawRows runtime.arena right).length>1
      · let pairs:=rowPairs (rawRows runtime.arena left) (rawRows runtime.arena right)
        let action:=fun pair : RawRow × RawRow=>memoSplitPair r pair.1 pair.2
        let value:=fun pair : RawRow × RawRow=>complexMoyal r
          (arenaEvaluate (rowTerm K runtime.arena pair.1)) (arenaEvaluate (rowTerm K runtime.arena pair.2))
        have generated:=runtimeSequence_native_values K runtime runtime pairs action value (RawExtends.refl _) valid
          (fun pair _=>memoSplitPair_grows r pair.1 pair.2) (by
            intro pair member current extension paid
            obtain ⟨a,ha,hm⟩:=List.mem_flatMap.mp member
            obtain ⟨b,hb,same⟩:=List.mem_map.mp hm
            subst pair
            have aWords:=rawRows_words runtime.arena valid.handles.closed left a ha
            have bWords:=rawRows_words runtime.arena valid.handles.closed right b hb
            have pairResult:=memoSplitPair_native K r a b current paid
              (fun node hn=>lt_of_lt_of_le (aWords node hn) extension.nodes.length_le)
              (fun node hn=>lt_of_lt_of_le (bWords node hn) extension.nodes.length_le) zeroOrder
            refine ⟨pairResult.1,pairResult.2.1,?_⟩
            intro x hx
            rw [show nativePolynomial K (action (a,b) current).2.arena (action (a,b) current).1 x=
              complexMoyal r (arenaEvaluate (rowTerm K current.arena a)) (arenaEvaluate (rowTerm K current.arena b)) x from pairResult.2.2 x hx,
              rowTerm_prefix K extension valid.handles.closed a aWords,rowTerm_prefix K extension valid.handles.closed b bWords])
        let result:=runtimeSequence (pairs.map action) runtime
        have added:=runArena_cached (rawAdd result.1) (rawAdd_extends result.1) (rawAdd_closed result.1)
          (fun _ _=>rawPoly_bound _ _) result.2 generated.1
        rw [moyalMiss_split r left right runtime zeroOrder zero many]
        refine ⟨added.1,added.2,?_⟩
        intro x hx
        change nativePolynomial K (rawAdd result.1 result.2.arena).2 (rawAdd result.1 result.2.arena).1 x=_
        rw [rawAdd_native K result.1 result.2.arena generated.1.handles.closed generated.2.1 x hx,generated.2.2 x hx]
        rw [rowPairs_sum,native_moyal_rows K r left right runtime.arena valid.handles.closed leftValid rightValid x hx]
      · have leftSingle : (rawRows runtime.arena left).length ≤ 1 := by omega
        have rightSingle : (rawRows runtime.arena right).length ≤ 1 := by omega
        simp only [moyalMiss,if_neg zeroOrder,if_neg zero,if_neg many]
        refine ⟨valid.withArena _ (rawPair_extends _ _ _ _)
          (rawPair_closed _ _ _ _ valid.handles.closed leftValid rightValid),
          rawPair_bound _ _ _ _ valid.handles.initialized,?_⟩
        exact fun x hx=>rawPair_native K r left right runtime.arena valid.handles.closed valid.handles.initialized
          leftValid rightValid leftSingle rightSingle zeroOrder x hx

theorem memoMoyal_native (K r left right : ℕ) (runtime : RawRuntime) (valid : CachedNative K runtime)
    (leftValid : Handle runtime.arena left) (rightValid : Handle runtime.arena right) :
    CachedNative K (memoMoyal r left right runtime).2 ∧
      Handle (memoMoyal r left right runtime).2.arena (memoMoyal r left right runtime).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (memoMoyal r left right runtime).2.arena (memoMoyal r left right runtime).1 x=
        complexMoyal r (nativePolynomial K runtime.arena left) (nativePolynomial K runtime.arena right) x := by
  cases found : memoLookup (r,left,right) runtime.moyalMemo with
  | some id=>
    simp only [memoMoyal,found]
    have member:=memoLookup_entry (r,left,right) runtime.moyalMemo id found
    exact ⟨valid,valid.handles.moyal _ member,(valid.moyal _ member).2.2⟩
  | none=>
    rw [memoMoyal_miss r left right runtime found]
    have result:=moyalMiss_native K r left right runtime valid leftValid rightValid
    exact cacheMoyalResult_native K r left right runtime (moyalMiss r left right runtime) valid result.1
      (moyalMiss_grows r left right runtime) leftValid rightValid result.2.1 result.2.2


theorem memoJordan_native (K r left right : ℕ) (runtime : RawRuntime) (valid : CachedNative K runtime)
    (leftValid : Handle runtime.arena left) (rightValid : Handle runtime.arena right) :
    CachedNative K (memoJordan r left right runtime).2 ∧
      Handle (memoJordan r left right runtime).2.arena (memoJordan r left right runtime).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial K (memoJordan r left right runtime).2.arena (memoJordan r left right runtime).1 x=
        (1/2 : ℂ)*(complexMoyal r (nativePolynomial K runtime.arena left) (nativePolynomial K runtime.arena right) x+
          complexMoyal r (nativePolynomial K runtime.arena right) (nativePolynomial K runtime.arena left) x) := by
  let one:=memoMoyal r left right runtime
  let two:=memoMoyal r right left one.2
  let added:=runArena (rawAdd [one.1,two.1]) two.2
  let scaled:=runArena (rawScale (polynomialCoefficient (MvPolynomial.C (1/2))) added.1) added.2
  have first:=memoMoyal_native K r left right runtime valid leftValid rightValid
  have oneGrow : RawExtends runtime.arena one.2.arena := memoMoyal_grows _ _ _ _
  have second:=memoMoyal_native K r right left one.2 first.1 (handle_extend oneGrow rightValid) (handle_extend oneGrow leftValid)
  have twoGrow : RawExtends one.2.arena two.2.arena := memoMoyal_grows _ _ _ _
  have sum:=runArena_cached (rawAdd [one.1,two.1]) (rawAdd_extends _) (rawAdd_closed _)
    (fun _ _=>rawPoly_bound _ _) two.2 second.1
  have scaledResult:=runArena_cached (rawScale (polynomialCoefficient (MvPolynomial.C (1/2))) added.1)
    (rawScale_extends _ _) (rawScale_closed _ _) (fun _ _=>rawPoly_bound _ _) added.2 sum.1
  refine ⟨scaledResult.1,scaledResult.2,?_⟩
  intro x hx
  change nativePolynomial K (rawScale (polynomialCoefficient (MvPolynomial.C (1/2))) added.1 added.2.arena).2
    (rawScale (polynomialCoefficient (MvPolynomial.C (1/2))) added.1 added.2.arena).1 x=_
  rw [rawScale_native K _ added.1 added.2.arena sum.1.handles.closed sum.2 x hx]
  have bounds : ListHandles two.2.arena [one.1,two.1] := by
    intro id member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with equal|equal
    · subst id;exact handle_extend twoGrow first.2.1
    · subst id;exact second.2.1
  have addition : nativePolynomial K added.2.arena added.1 x=
      nativePolynomial K two.2.arena one.1 x+nativePolynomial K two.2.arena two.1 x := by
    rw [show nativePolynomial K added.2.arena added.1 x=
      ([one.1,two.1].map (fun id=>nativePolynomial K two.2.arena id x)).sum from
      rawAdd_native K [one.1,two.1] two.2.arena second.1.handles.closed bounds x hx]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [addition,nativePolynomial_prefix K twoGrow first.1.handles.closed one.1 first.2.1,first.2.2 x hx,second.2.2 x hx,
    nativePolynomial_prefix K oneGrow valid.handles.closed left leftValid,
    nativePolynomial_prefix K oneGrow valid.handles.closed right rightValid]
  have coefficient : (coefficientValue (polynomialCoefficient (MvPolynomial.C (1/2))) x : ℂ)=(1/2 : ℂ) := by
    simp [polynomialCoefficient_source,polynomialSymbol,evalAt]
  rw [coefficient]

end LowEnergy.PreparationVacuumNativeMemo

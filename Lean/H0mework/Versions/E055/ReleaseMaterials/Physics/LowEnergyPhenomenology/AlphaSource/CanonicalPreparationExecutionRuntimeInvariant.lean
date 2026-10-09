import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSharedPoolEngine

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumExecutionGraph
open PreparationVacuumSharedPool PreparationVacuumDAGCoefficient

abbrev Handle (state : RawArena) (id : ℕ) : Prop := id < state.polynomials.length

def AngularHandles (state : RawArena) (polynomial : RawAngular) : Prop :=
  ∀ row,row∈polynomial → Handle state row.2

def SeriesHandles (state : RawArena) (series : RawSeries) : Prop :=
  ∀ polynomial,polynomial∈series → AngularHandles state polynomial

structure RuntimeHandles (runtime : RawRuntime) : Prop where
  initialized : RawInitialized runtime.arena
  closed : RawMoyalClosed runtime.arena
  moyal : ∀ entry,entry∈runtime.moyalMemo → Handle runtime.arena entry.2
  resolvent : ∀ entry,entry∈runtime.rMemo → SeriesHandles runtime.arena entry.2
  jordan : ∀ entry,entry∈runtime.jMemo → SeriesHandles runtime.arena entry.2
  word : ∀ entry,entry∈runtime.wordMemo → SeriesHandles runtime.arena entry.2

theorem handle_extend {old next : RawArena} (h : RawExtends old next) {id : ℕ} (valid : Handle old id) :
    Handle next id := lt_of_lt_of_le valid h.polynomials.length_le

theorem angular_extend {old next : RawArena} (h : RawExtends old next) {polynomial : RawAngular}
    (valid : AngularHandles old polynomial) : AngularHandles next polynomial :=
  fun row member=>handle_extend h (valid row member)

theorem series_extend {old next : RawArena} (h : RawExtends old next) {series : RawSeries}
    (valid : SeriesHandles old series) : SeriesHandles next series :=
  fun polynomial member=>angular_extend h (valid polynomial member)

theorem RuntimeHandles.withArena {runtime : RawRuntime} (valid : RuntimeHandles runtime)
    (next : RawArena) (grows : RawExtends runtime.arena next) (closed : RawMoyalClosed next) :
    RuntimeHandles {runtime with arena:=next} where
  initialized:=valid.initialized.trans grows
  closed:=closed
  moyal:=fun entry member=>handle_extend grows (valid.moyal entry member)
  resolvent:=fun entry member=>series_extend grows (valid.resolvent entry member)
  jordan:=fun entry member=>series_extend grows (valid.jordan entry member)
  word:=fun entry member=>series_extend grows (valid.word entry member)

theorem initial_handles : RuntimeHandles (⟨rawInitial,[],[],[],[]⟩ : RawRuntime) := by
  refine ⟨RawExtends.refl _,rawInitial_closed,?_,?_,?_,?_⟩
  all_goals intro entry member;exact False.elim (List.not_mem_nil member)

theorem memoLookup_member {κ α : Type} [DecidableEq κ] (key : κ) (entries : List (κ × α))
    (value : α) (found : memoLookup key entries=some value) : ∃ entry∈entries,entry.2=value := by
  unfold memoLookup at found
  obtain ⟨entry,hentry,heq⟩:=Option.map_eq_some_iff.mp found
  exact ⟨entry,List.mem_of_find?_eq_some hentry,heq⟩

theorem zero_handle {runtime : RawRuntime} (valid : RuntimeHandles runtime) : Handle runtime.arena 0 :=
  rawInitialized_positive _ valid.initialized

theorem series_getD {state : RawArena} {series : RawSeries} (valid : SeriesHandles state series) (k : ℕ) :
    AngularHandles state (series.getD k []) := by
  by_cases h : k < series.length
  · rw [List.getD_eq_getElem _ _ h]
    exact valid _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro row member;exact False.elim (List.not_mem_nil member)

theorem angularLookup_handle {runtime : RawRuntime} (valid : RuntimeHandles runtime)
    (key : RawAngle) {polynomial : RawAngular} (entries : AngularHandles runtime.arena polynomial) :
    Handle runtime.arena (angularLookup key polynomial) := by
  classical
  unfold angularLookup
  cases h : polynomial.find? (fun row=>row.1=key) with
  | none=>exact zero_handle valid
  | some row=>exact entries row (List.mem_of_find?_eq_some h)

theorem angularInsert_handles {state : RawArena} {rows : RawAngular} (valid : AngularHandles state rows)
    (key : RawAngle) (id : ℕ) (bound : Handle state id) : AngularHandles state (angularInsert key id rows) := by
  classical
  induction rows with
  | nil=>
    intro row member
    simp only [angularInsert,List.mem_singleton] at member
    subst row;exact bound
  | cons head tail ih=>
    simp only [angularInsert]
    split_ifs with same
    · intro row member
      rcases List.mem_cons.mp member with equal|old
      · subst row;exact bound
      · exact valid row (List.mem_cons_of_mem _ old)
    · intro row member
      rcases List.mem_cons.mp member with equal|old
      · subst row;exact valid head (by simp)
      · exact ih (fun r hr=>valid r (List.mem_cons_of_mem _ hr)) row old

theorem angularNonzero_handles {state : RawArena} {rows : RawAngular} (valid : AngularHandles state rows) :
    AngularHandles state (angularNonzero rows) := fun row member=>valid row (List.mem_filter.mp member).1

theorem angularShift_handles {state : RawArena} {rows : RawAngular} (valid : AngularHandles state rows) (shift : RawAngle) :
    AngularHandles state (angularShift rows shift) := by
  intro row member
  obtain ⟨prior,hp,rfl⟩:=List.mem_map.mp member
  exact valid prior hp

theorem runArena_handles (action : RawAction)
    (grows : ∀ state,RawExtends state (action state).2)
    (preserves : ∀ state,RawMoyalClosed state → RawMoyalClosed (action state).2)
    (returns : ∀ state,RawInitialized state → Handle (action state).2 (action state).1)
    (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runArena action runtime).2 ∧ Handle (runArena action runtime).2.arena (runArena action runtime).1 :=
  ⟨valid.withArena _ (grows _) (preserves _ valid.closed),returns _ valid.initialized⟩

theorem runScalar_handles (c : NormalizedCoefficient) (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runArena (rawScalar c) runtime).2 ∧
      Handle (runArena (rawScalar c) runtime).2.arena (runArena (rawScalar c) runtime).1 :=
  runArena_handles _ (rawScalar_extends c) (rawScalar_closed c) (fun _ _=>rawPoly_bound _ _) runtime valid

theorem runAdd_handles (ids : List ℕ) (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runArena (rawAdd ids) runtime).2 ∧
      Handle (runArena (rawAdd ids) runtime).2.arena (runArena (rawAdd ids) runtime).1 :=
  runArena_handles _ (rawAdd_extends ids) (rawAdd_closed ids) (fun _ _=>rawPoly_bound _ _) runtime valid

theorem runScale_handles (c : NormalizedCoefficient) (id : ℕ) (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runArena (rawScale c id) runtime).2 ∧
      Handle (runArena (rawScale c id) runtime).2.arena (runArena (rawScale c id) runtime).1 :=
  runArena_handles _ (rawScale_extends c id) (rawScale_closed c id) (fun _ _=>rawPoly_bound _ _) runtime valid

theorem runMultiply_handles (left right : ℕ) (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runArena (rawMultiply left right) runtime).2 ∧
      Handle (runArena (rawMultiply left right) runtime).2.arena (runArena (rawMultiply left right) runtime).1 :=
  runArena_handles _ (rawMultiply_extends left right) (rawMultiply_closed left right)
    (fun _ _=>rawPoly_bound _ _) runtime valid

theorem runPoly_handles (rows : List RawRow) (runtime : RawRuntime) (valid : RuntimeHandles runtime)
    (words : RawWords (fun id=>id < runtime.arena.nodes.length) rows) :
    RuntimeHandles (runArena (rawPoly rows) runtime).2 ∧
      Handle (runArena (rawPoly rows) runtime).2.arena (runArena (rawPoly rows) runtime).1 :=
  ⟨valid.withArena _ (rawPoly_extends _ _) (rawPoly_closed _ _ valid.closed words),rawPoly_bound _ _⟩

theorem runPair_handles (r left right : ℕ) (runtime : RawRuntime) (valid : RuntimeHandles runtime)
    (leftValid : Handle runtime.arena left) (rightValid : Handle runtime.arena right) :
    RuntimeHandles (runArena (rawPair r left right) runtime).2 ∧
      Handle (runArena (rawPair r left right) runtime).2.arena (runArena (rawPair r left right) runtime).1 :=
  ⟨valid.withArena _ (rawPair_extends _ _ _ _) (rawPair_closed _ _ _ _ valid.closed leftValid rightValid),
    rawPair_bound _ _ _ _ valid.initialized⟩

theorem cacheMoyalResult_handles (key : ℕ × ℕ × ℕ) (result : ℕ × RawRuntime)
    (valid : RuntimeHandles result.2) (bound : Handle result.2.arena result.1) :
    RuntimeHandles (cacheMoyalResult key result).2 ∧
      Handle (cacheMoyalResult key result).2.arena (cacheMoyalResult key result).1 := by
  refine ⟨⟨valid.initialized,valid.closed,?_,valid.resolvent,valid.jordan,valid.word⟩,bound⟩
  intro entry member
  rcases List.mem_cons.mp member with equal|old
  · subst entry;exact bound
  · exact valid.moyal entry old

theorem memoPair_handles (r left right : ℕ) (runtime : RawRuntime) (valid : RuntimeHandles runtime)
    (leftValid : Handle runtime.arena left) (rightValid : Handle runtime.arena right) :
    RuntimeHandles (memoPair r left right runtime).2 ∧
      Handle (memoPair r left right runtime).2.arena (memoPair r left right runtime).1 := by
  dsimp only [memoPair]
  split
  · rename_i id found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ id found
    exact ⟨valid,equal ▸ valid.moyal entry member⟩
  · apply cacheMoyalResult_handles
    · split_ifs
      · exact valid
      · exact (runPair_handles r left right runtime valid leftValid rightValid).1
    · split_ifs
      · exact zero_handle valid
      · exact (runPair_handles r left right runtime valid leftValid rightValid).2

-- These hypotheses are ordinary local execution invariants; the source caller
-- below constructs them from the empty pool and emitted handles.
theorem runtimeSequence_handles {α : Type} (P : RawArena → α → Prop)
    (monotone : ∀ {old next},RawExtends old next → ∀ value,P old value → P next value)
    (base current : RawRuntime) (actions : List (RuntimeAction α))
    (extension : RawExtends base.arena current.arena) (valid : RuntimeHandles current)
    (grows : ∀ action,action∈actions → RuntimeGrows action)
    (step : ∀ action,action∈actions → ∀ state,RawExtends base.arena state.arena → RuntimeHandles state →
      RuntimeHandles (action state).2 ∧ P (action state).2.arena (action state).1) :
    RuntimeHandles (runtimeSequence actions current).2 ∧
      ∀ value,value∈(runtimeSequence actions current).1 → P (runtimeSequence actions current).2.arena value := by
  induction actions generalizing current with
  | nil=>exact ⟨valid,fun value member=>False.elim (List.not_mem_nil member)⟩
  | cons action actions ih=>
    have one:=step action (by simp) current extension valid
    have next:=ih (action current).2 (extension.trans (grows action (by simp) current)) one.1
      (fun a h=>grows a (by simp [h])) (fun a h=>step a (by simp [h]))
    refine ⟨next.1,?_⟩
    intro value member
    rcases List.mem_cons.mp member with equal|old
    · subst value
      exact monotone (runtimeSequence_grows actions (fun a h=>grows a (by simp [h])) (action current).2) _ one.2
    · exact next.2 value old


theorem rawRow_words_extended {base current : RawArena} (extension : RawExtends base current)
    (closed : RawMoyalClosed base) (id : ℕ) (row : RawRow) (member : row∈rawRows base id) :
    RawWords (fun node=>node < current.nodes.length) [row] := by
  intro other present node hn
  have equal:=List.mem_singleton.mp present
  subst other
  exact lt_of_lt_of_le (rawRows_words base closed id row member node hn) extension.nodes.length_le

theorem memoMoyal_handles (r left right : ℕ) (runtime : RawRuntime) (valid : RuntimeHandles runtime)
    (leftValid : Handle runtime.arena left) (rightValid : Handle runtime.arena right) :
    RuntimeHandles (memoMoyal r left right runtime).2 ∧
      Handle (memoMoyal r left right runtime).2.arena (memoMoyal r left right runtime).1 := by
  dsimp only [memoMoyal]
  split
  · rename_i id found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ id found
    exact ⟨valid,equal ▸ valid.moyal entry member⟩
  · have finish (result : ℕ × RawRuntime) (paid : RuntimeHandles result.2 ∧ Handle result.2.arena result.1) :=
      cacheMoyalResult_handles (r,left,right) result paid.1 paid.2
    apply finish
    split_ifs
    · exact runMultiply_handles _ _ _ valid
    · exact ⟨valid,zero_handle valid⟩
    · apply runAdd_handles
      apply (runtimeSequence_handles Handle (fun h _ hval=>handle_extend h hval)
        runtime runtime _ (RawExtends.refl _) valid ?_ ?_).1
      · intro action member current
        obtain ⟨a,_,ha⟩:=List.mem_flatMap.mp member
        obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
        let one:=runArena (rawPoly [a]) current
        let two:=runArena (rawPoly [b]) one.2
        exact ((rawPoly_extends [a] current.arena).trans (rawPoly_extends [b] one.2.arena)).trans
          (memoPair_grows r one.1 two.1 two.2)
      · intro action member current extension currentValid
        obtain ⟨a,ha,hrow⟩:=List.mem_flatMap.mp member
        obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hrow
        let one:=runArena (rawPoly [a]) current
        let two:=runArena (rawPoly [b]) one.2
        have first:=runPoly_handles [a] current currentValid
          (rawRow_words_extended extension valid.closed left a ha)
        have second:=runPoly_handles [b] one.2 first.1
          (rawRow_words_extended (extension.trans (rawPoly_extends [a] current.arena)) valid.closed right b hb)
        exact memoPair_handles r one.1 two.1 two.2 second.1
          (handle_extend (rawPoly_extends [b] one.2.arena) first.2) second.2
    · exact runPair_handles _ _ _ _ valid leftValid rightValid

theorem memoJordan_handles (r left right : ℕ) (runtime : RawRuntime) (valid : RuntimeHandles runtime)
    (leftValid : Handle runtime.arena left) (rightValid : Handle runtime.arena right) :
    RuntimeHandles (memoJordan r left right runtime).2 ∧
      Handle (memoJordan r left right runtime).2.arena (memoJordan r left right runtime).1 := by
  let one:=memoMoyal r left right runtime
  let two:=memoMoyal r right left one.2
  let added:=runArena (rawAdd [one.1,two.1]) two.2
  have first:=memoMoyal_handles r left right runtime valid leftValid rightValid
  have second:=memoMoyal_handles r right left one.2 first.1
    (handle_extend (memoMoyal_grows r left right runtime) rightValid)
    (handle_extend (memoMoyal_grows r left right runtime) leftValid)
  have third:=runAdd_handles [one.1,two.1] two.2 second.1
  exact runScale_handles (polynomialCoefficient (MvPolynomial.C (1/2))) added.1 added.2 third.1


theorem fold_invariant {α β : Type} (items : List α) (step : β → α → β) (P : β → Prop)
    (closed : ∀ out,P out → ∀ item,item∈items → P (step out item)) (initial : β) (valid : P initial) :
    P (items.foldl step initial) := by
  induction items generalizing initial with
  | nil=>exact valid
  | cons item items ih=>
    exact ih (fun out ho i hi=>closed out ho i (List.mem_cons_of_mem _ hi)) _
      (closed initial valid item (by simp))

theorem angularAdd_closed_handles (inputs : List RawAngular) (state : RawArena) (closed : RawMoyalClosed state) :
    RawMoyalClosed (angularAdd inputs state).2 ∧ AngularHandles (angularAdd inputs state).2 (angularAdd inputs state).1 := by
  let step:=fun (out : RawAngular × RawArena) (row : RawAngle × ℕ)=>
    let added:=rawAdd [angularLookup row.1 out.1,row.2] out.2
    (angularInsert row.1 added.1 out.1,added.2)
  have result:=fold_invariant inputs.flatten step
    (fun out=>RawMoyalClosed out.2 ∧ AngularHandles out.2 out.1) (by
      intro out valid row member
      exact ⟨rawAdd_closed _ _ valid.1,
        angularInsert_handles (angular_extend (rawAdd_extends _ _) valid.2) _ _ (rawPoly_bound _ _)⟩)
    ([],state) ⟨closed,fun row member=>False.elim (List.not_mem_nil member)⟩
  exact ⟨result.1,angularNonzero_handles result.2⟩

theorem angularScale_closed_handles (c : NormalizedCoefficient) (input : RawAngular) (state : RawArena)
    (closed : RawMoyalClosed state) : RawMoyalClosed (angularScale c input state).2 ∧
      AngularHandles (angularScale c input state).2 (angularScale c input state).1 := by
  dsimp only [angularScale]
  refine fold_invariant input _ (fun out=>RawMoyalClosed out.2 ∧ AngularHandles out.2 out.1) ?_
    ([],state) ⟨closed,fun row member=>False.elim (List.not_mem_nil member)⟩
  intro out valid row member
  split_ifs
  · exact ⟨rawScale_closed _ _ _ valid.1,angular_extend (rawScale_extends _ _ _) valid.2⟩
  · refine ⟨rawScale_closed _ _ _ (rawScale_closed _ _ _ valid.1),?_⟩
    intro result present
    rcases List.mem_append.mp present with old|fresh
    · exact angular_extend ((rawScale_extends _ _ _).trans (rawScale_extends _ _ _)) valid.2 result old
    · have same:=List.mem_singleton.mp fresh
      subst result
      exact rawPoly_bound _ _

theorem runAngular_handles (action : AngularAction)
    (grows : ∀ state,RawExtends state (action state).2)
    (preserves : ∀ state,RawMoyalClosed state → RawMoyalClosed (action state).2 ∧ AngularHandles (action state).2 (action state).1)
    (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runAngular action runtime).2 ∧ AngularHandles (runAngular action runtime).2.arena (runAngular action runtime).1 :=
  ⟨valid.withArena _ (grows _) (preserves _ valid.closed).1,(preserves _ valid.closed).2⟩

theorem runAngularAdd_handles (inputs : List RawAngular) (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runAngular (angularAdd inputs) runtime).2 ∧
      AngularHandles (runAngular (angularAdd inputs) runtime).2.arena (runAngular (angularAdd inputs) runtime).1 :=
  runAngular_handles _ (angularAdd_grows inputs) (angularAdd_closed_handles inputs) runtime valid

theorem runAngularScale_handles (c : NormalizedCoefficient) (input : RawAngular) (runtime : RawRuntime)
    (valid : RuntimeHandles runtime) : RuntimeHandles (runAngular (angularScale c input) runtime).2 ∧
      AngularHandles (runAngular (angularScale c input) runtime).2.arena (runAngular (angularScale c input) runtime).1 :=
  runAngular_handles _ (angularScale_grows c input) (angularScale_closed_handles c input) runtime valid

theorem angularAverage_closed_handles (input : RawAngular) (state : RawArena) (closed : RawMoyalClosed state) :
    RawMoyalClosed (angularAverage input state).2 ∧ Handle (angularAverage input state).2 (angularAverage input state).1 := by
  refine ⟨?_,rawPoly_bound _ _⟩
  apply rawAdd_closed
  apply rawSequence_closed state state _ (RawExtends.refl _) closed
  · intro action member current
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_extends _ _ _
  · intro action member current extension paid
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_closed _ _ _ paid

theorem runAverage_handles (input : RawAngular) (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runArena (angularAverage input) runtime).2 ∧
      Handle (runArena (angularAverage input) runtime).2.arena (runArena (angularAverage input) runtime).1 :=
  ⟨valid.withArena _ (angularAverage_grows _ _) (angularAverage_closed_handles _ _ valid.closed).1,
    (angularAverage_closed_handles _ _ valid.closed).2⟩

theorem runtimeWeighted_handles (r : ℕ) (left right : RawAngular) (runtime : RawRuntime)
    (valid : RuntimeHandles runtime) (leftValid : AngularHandles runtime.arena left)
    (rightValid : AngularHandles runtime.arena right) :
    RuntimeHandles (runtimeWeighted r left right runtime).2 ∧
      AngularHandles (runtimeWeighted r left right runtime).2.arena (runtimeWeighted r left right runtime).1 := by
  let pairs:=left.flatMap (fun a=>right.map (fun b=>(a,b)))
  let step:=fun (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ))=>
    let key:=pair.1.1+pair.2.1
    let product:=memoJordan r pair.1.2 pair.2.2 out.2
    let added:=runArena (rawAdd [angularLookup key out.1,product.1]) product.2
    (angularInsert key added.1 out.1,added.2)
  have result:=fold_invariant pairs step
    (fun out=>RawExtends runtime.arena out.2.arena ∧ RuntimeHandles out.2 ∧ AngularHandles out.2.arena out.1) (by
      intro out paid pair member
      obtain ⟨a,ha,hr⟩:=List.mem_flatMap.mp member
      obtain ⟨b,hb,same⟩:=List.mem_map.mp hr
      subst pair
      let product:=memoJordan r a.2 b.2 out.2
      let added:=runArena (rawAdd [angularLookup (a.1+b.1) out.1,product.1]) product.2
      have hp:=memoJordan_handles r a.2 b.2 out.2 paid.2.1
        (handle_extend paid.1 (leftValid a ha)) (handle_extend paid.1 (rightValid b hb))
      have hs:=runAdd_handles [angularLookup (a.1+b.1) out.1,product.1] product.2 hp.1
      have grow : RawExtends out.2.arena added.2.arena :=
        (memoJordan_grows r a.2 b.2 out.2).trans (rawAdd_extends _ _)
      exact ⟨paid.1.trans grow,hs.1,angularInsert_handles (angular_extend grow paid.2.2) _ _ hs.2⟩)
    ([],runtime) ⟨RawExtends.refl _,valid,fun row member=>False.elim (List.not_mem_nil member)⟩
  exact ⟨result.2.1,angularNonzero_handles result.2.2⟩


theorem runAtom_handles (kind : RawKind) (central : Bool) (runtime : RawRuntime) (valid : RuntimeHandles runtime)
    (dependencies : ∀ id,id∈kind.dependencies → Handle runtime.arena id) :
    RuntimeHandles (runArena (rawAtom kind central) runtime).2 ∧
      Handle (runArena (rawAtom kind central) runtime).2.arena (runArena (rawAtom kind central) runtime).1 :=
  ⟨valid.withArena _ (rawAtom_extends _ _ _) (rawAtom_closed _ _ _ valid.closed dependencies),rawPoly_bound _ _⟩

theorem angularConstant_handles {state : RawArena} (id : ℕ) (valid : Handle state id) :
    AngularHandles state (angularConstant id) := by
  unfold angularConstant
  split_ifs
  · intro row member;exact False.elim (List.not_mem_nil member)
  · intro row member
    have same:=List.mem_singleton.mp member
    subst row;exact valid

theorem originalSource_closed_handles (depth : ℕ) (slot : Fin 13) (state : RawArena)
    (initialized : RawInitialized state) (closed : RawMoyalClosed state) :
    RawMoyalClosed (originalSource depth slot state).2 ∧
      SeriesHandles (originalSource depth slot state).2 (originalSource depth slot state).1 := by
  let principal:=if slot.val=0 ∨ (4 ≤ slot.val ∧ slot.val ≤ 9) then
    rawScalar (principalCoefficient slot) state else (0,state)
  have hp : RawExtends state principal.2 ∧ RawMoyalClosed principal.2 ∧ Handle principal.2 principal.1 := by
    dsimp only [principal]
    split_ifs
    · exact ⟨rawScalar_extends _ _,rawScalar_closed _ _ closed,rawPoly_bound _ _⟩
    · exact ⟨RawExtends.refl _,closed,rawInitialized_positive _ initialized⟩
  let first:=rawAtom (.source 1 (Fin.castSucc slot)) false principal.2
  let lower:=rawAtom (.source 0 (Fin.castSucc slot)) false first.2
  have hf : RawMoyalClosed first.2 := rawAtom_closed _ _ _ hp.2.1 (by intro id member;cases member)
  have hl : RawMoyalClosed lower.2 := rawAtom_closed _ _ _ hf (by intro id member;cases member)
  let final:=if slot=0 then
    let extra:=rawAtom (.source 0 (Fin.last 13)) false lower.2
    rawAdd [lower.1,extra.1] extra.2 else lower
  have he : RawExtends lower.2 final.2 ∧ RawMoyalClosed final.2 ∧ Handle final.2 final.1 := by
    dsimp only [final]
    split_ifs
    · exact ⟨(rawAtom_extends _ _ _).trans (rawAdd_extends _ _),
        rawAdd_closed _ _ (rawAtom_closed _ _ _ hl (by intro id member;cases member)),rawPoly_bound _ _⟩
    · exact ⟨RawExtends.refl _,hl,rawPoly_bound _ _⟩
  refine ⟨he.2.1,?_⟩
  change SeriesHandles final.2
    ([angularConstant principal.1,[(angleZero,first.1)],[(angleZero,final.1)]].take (depth+1)++List.replicate (depth-2) [])
  intro polynomial member
  rcases List.mem_append.mp member with old|empty
  · have mem:=List.mem_of_mem_take old
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with equal|equal|equal
    · subst polynomial
      exact angularConstant_handles _ (handle_extend (((rawAtom_extends _ _ _).trans (rawAtom_extends _ _ _)).trans he.1) hp.2.2)
    · subst polynomial
      intro row hrow
      have same:=List.mem_singleton.mp hrow
      subst row
      exact handle_extend ((rawAtom_extends _ _ _).trans he.1) (rawPoly_bound _ _)
    · subst polynomial
      intro row hrow
      have same:=List.mem_singleton.mp hrow
      subst row
      exact he.2.2
  · have same:polynomial=[] := (List.mem_replicate.mp empty).2
    subst polynomial
    intro row member;exact False.elim (List.not_mem_nil member)

theorem runtimeSource_handles (depth : ℕ) (slot : Fin 13) (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runtimeSource depth slot runtime).2 ∧
      SeriesHandles (runtimeSource depth slot runtime).2.arena (runtimeSource depth slot runtime).1 :=
  ⟨valid.withArena _ (originalSource_grows _ _ _) (originalSource_closed_handles _ _ _ valid.initialized valid.closed).1,
    (originalSource_closed_handles _ _ _ valid.initialized valid.closed).2⟩

theorem angularSequence_closed_handles (actions : List AngularAction)
    (preserves : ∀ action,action∈actions → ∀ state,RawMoyalClosed state →
      RawMoyalClosed (action state).2 ∧ AngularHandles (action state).2 (action state).1)
    (grows : ∀ action,action∈actions → ∀ state,RawExtends state (action state).2)
    (state : RawArena) (closed : RawMoyalClosed state) :
    RawMoyalClosed (angularSequence actions state).2 ∧ SeriesHandles (angularSequence actions state).2 (angularSequence actions state).1 := by
  induction actions generalizing state with
  | nil=>exact ⟨closed,fun row member=>False.elim (List.not_mem_nil member)⟩
  | cons action actions ih=>
    have first:=preserves action (by simp) state closed
    have tail:=ih (fun a h=>preserves a (by simp [h])) (fun a h=>grows a (by simp [h])) (action state).2 first.1
    refine ⟨tail.1,?_⟩
    intro polynomial member
    rcases List.mem_cons.mp member with equal|old
    · subst polynomial
      exact angular_extend (angularSequence_grows actions (fun a h=>grows a (by simp [h])) (action state).2) first.2
    · exact tail.2 polynomial old

theorem originalSetup_closed_handles (depth : ℕ) (clocks : RawClocks) (state : RawArena)
    (initialized : RawInitialized state) (closed : RawMoyalClosed state)
    (clockValid : ∀ entry,entry∈clocks → Handle state entry.2) :
    RawMoyalClosed (originalSetup depth clocks state).2 ∧
      (∀ a,SeriesHandles (originalSetup depth clocks state).2 ((originalSetup depth clocks state).1.jclocks a)) ∧
      SeriesHandles (originalSetup depth clocks state).2 (originalSetup depth clocks state).1.ellclock := by
  have ell:=angularSequence_closed_handles
    ((List.range (depth+1)).map (fun k=>angularAdd
      [ (List.range (depth+1) |>.map (fun l=>angularConstant (clockLookup clocks l 0))).getD k [],
        angularShift ((List.range (depth+1) |>.map (fun l=>angularConstant (clockLookup clocks l 1))).getD k []) (angleUnit 0),
        angularShift ((List.range (depth+1) |>.map (fun l=>angularConstant (clockLookup clocks l 2))).getD k []) (angleUnit 1),
        angularShift ((List.range (depth+1) |>.map (fun l=>angularConstant (clockLookup clocks l 3))).getD k []) (angleUnit 2)]))
    (by intro action member current paid;obtain ⟨k,_,rfl⟩:=List.mem_map.mp member;exact angularAdd_closed_handles _ _ paid)
    (by intro action member current;obtain ⟨k,_,rfl⟩:=List.mem_map.mp member;exact angularAdd_grows _ _)
    state closed
  refine ⟨ell.1,?_,ell.2⟩
  intro a polynomial member
  obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
  apply angularConstant_handles
  apply handle_extend (originalSetup_grows depth clocks state)
  unfold clockLookup
  cases found : clocks.find? (fun row=>row.1=(k,a)) with
  | none=>exact rawInitialized_positive _ initialized
  | some entry=>exact clockValid entry (List.mem_of_find?_eq_some found)

structure SetupHandles (runtime : RawRuntime) (setup : RawSetup) : Prop where
  jclocks : ∀ a,SeriesHandles runtime.arena (setup.jclocks a)
  ellclock : SeriesHandles runtime.arena setup.ellclock

theorem SetupHandles.extend {old next : RawRuntime} (grows : RawExtends old.arena next.arena)
    {setup : RawSetup} (valid : SetupHandles old setup) : SetupHandles next setup :=
  ⟨fun a=>series_extend grows (valid.jclocks a),series_extend grows valid.ellclock⟩

theorem runtimeSetup_handles (depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime) (valid : RuntimeHandles runtime)
    (clockValid : ∀ entry,entry∈clocks → Handle runtime.arena entry.2) :
    RuntimeHandles (runtimeSetup depth clocks runtime).2 ∧
      SetupHandles (runtimeSetup depth clocks runtime).2 (runtimeSetup depth clocks runtime).1 := by
  have setup:=originalSetup_closed_handles depth clocks runtime.arena valid.initialized valid.closed clockValid
  refine ⟨⟨valid.initialized.trans (originalSetup_grows _ _ _),setup.1,?_,?_,?_,?_⟩,⟨setup.2.1,setup.2.2⟩⟩
  · intro entry member
    exact handle_extend (originalSetup_grows _ _ _) (valid.moyal entry member)
  all_goals intro entry member;exact False.elim (List.not_mem_nil member)


theorem RuntimeHandles.cacheJ {runtime : RawRuntime} (valid : RuntimeHandles runtime)
    (key : Fin 4 × SeriesKey) (value : RawSeries) (bound : SeriesHandles runtime.arena value) :
    RuntimeHandles {runtime with jMemo:=(key,value)::runtime.jMemo} := by
  refine ⟨valid.initialized,valid.closed,valid.moyal,valid.resolvent,?_,valid.word⟩
  intro entry member
  rcases List.mem_cons.mp member with equal|old
  · subst entry;exact bound
  · exact valid.jordan entry old

theorem RuntimeHandles.cacheR {runtime : RawRuntime} (valid : RuntimeHandles runtime)
    (key : SeriesKey) (value : RawSeries) (bound : SeriesHandles runtime.arena value) :
    RuntimeHandles {runtime with rMemo:=(key,value)::runtime.rMemo} := by
  refine ⟨valid.initialized,valid.closed,valid.moyal,?_,valid.jordan,valid.word⟩
  intro entry member
  rcases List.mem_cons.mp member with equal|old
  · subst entry;exact bound
  · exact valid.resolvent entry old

theorem RuntimeHandles.cacheWord {runtime : RawRuntime} (valid : RuntimeHandles runtime)
    (key : List PreparationVacuumEngineSource.Token × SeriesKey) (value : RawSeries)
    (bound : SeriesHandles runtime.arena value) :
    RuntimeHandles {runtime with wordMemo:=(key,value)::runtime.wordMemo} := by
  refine ⟨valid.initialized,valid.closed,valid.moyal,valid.resolvent,valid.jordan,?_⟩
  intro entry member
  rcases List.mem_cons.mp member with equal|old
  · subst entry;exact bound
  · exact valid.word entry old

theorem originalJS_handles (setup : RawSetup) (axis : Fin 4) (input : RawSeries)
    (runtime : RawRuntime) (valid : RuntimeHandles runtime) (setupValid : SetupHandles runtime setup)
    (inputValid : SeriesHandles runtime.arena input) :
    RuntimeHandles (originalJS setup axis input runtime).2 ∧
      SeriesHandles (originalJS setup axis input runtime).2.arena (originalJS setup axis input runtime).1 := by
  classical
  dsimp only [originalJS]
  split
  · rename_i output found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ output found
    exact ⟨valid,equal ▸ valid.jordan entry member⟩
  · have result:=runtimeSequence_handles AngularHandles (fun h _ hv=>angular_extend h hv)
      runtime runtime ((List.range (setup.depth+1)).map (fun k=>fun current=>
        let summands:=(List.range (k+1)).flatMap (fun i=>(List.range (k+1-i)).map (fun j=>
          runtimeWeighted (k-i-j) ((setup.jclocks axis).getD i []) (input.getD j [])))
        let generated:=runtimeSequence summands current
        runAngular (angularAdd generated.1) generated.2))
      (RawExtends.refl _) valid (by
        intro action member current
        obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
        apply RawExtends.trans (runtimeSequence_grows _ ?_ current)
        · exact angularAdd_grows _ _
        · intro action member current
          obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
          obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
          exact runtimeWeighted_grows _ _ _ current) (by
        intro action member current extension currentValid
        obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
        apply runAngularAdd_handles
        apply (runtimeSequence_handles AngularHandles (fun h _ hv=>angular_extend h hv)
          runtime current _ extension currentValid ?_ ?_).1
        · intro action member state
          obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
          obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
          exact runtimeWeighted_grows _ _ _ state
        · intro action member state extension2 paid
          obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
          obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
          exact runtimeWeighted_handles _ _ _ state paid
            (series_getD (series_extend extension2 (setupValid.jclocks axis)) i)
            (series_getD (series_extend extension2 inputValid) j))
    exact ⟨result.1.cacheJ _ _ result.2,result.2⟩

theorem series_append_handles {state : RawArena} {prior : RawSeries} {last : RawAngular}
    (valid : SeriesHandles state prior) (new : AngularHandles state last) : SeriesHandles state (prior++[last]) := by
  intro polynomial member
  rcases List.mem_append.mp member with old|fresh
  · exact valid polynomial old
  · have same:=List.mem_singleton.mp fresh
    subst polynomial;exact new

theorem originalResolvent_handles (setup : RawSetup) (input : RawSeries)
    (runtime : RawRuntime) (valid : RuntimeHandles runtime) (setupValid : SetupHandles runtime setup) :
    RuntimeHandles (originalResolvent setup input runtime).2 ∧
      SeriesHandles (originalResolvent setup input runtime).2.arena (originalResolvent setup input runtime).1 := by
  dsimp only [originalResolvent]
  split
  · rename_i output found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ output found
    exact ⟨valid,equal ▸ valid.resolvent entry member⟩
  · let step:=fun (out : RawSeries × RawRuntime) (k : ℕ)=>
      let lower:=(List.range (k+1)).flatMap (fun i=>(List.range (k+1-i)).filterMap (fun j=>
        if i=0 ∧ k-i-j=0 then none else
          some (runtimeWeighted (k-i-j) (setup.ellclock.getD i []) (out.1.getD j []))))
      let generated:=runtimeSequence lower out.2
      let summed:=runAngular (angularAdd generated.1) generated.2
      let negated:=runAngular (angularScale (polynomialCoefficient (-1)) summed.1) summed.2
      let residual:=runAngular (angularAdd [input.getD k [],negated.1]) negated.2
      let answer:=runAngular (angularScale (inversePoleCoefficient 0) residual.1) residual.2
      (out.1++[answer.1],answer.2)
    have result:=fold_invariant (List.range (setup.depth+1)) step
      (fun out=>RawExtends runtime.arena out.2.arena ∧ RuntimeHandles out.2 ∧ SeriesHandles out.2.arena out.1) (by
        intro out paid k member
        let lower:=(List.range (k+1)).flatMap (fun i=>(List.range (k+1-i)).filterMap (fun j=>
          if i=0 ∧ k-i-j=0 then none else
            some (runtimeWeighted (k-i-j) (setup.ellclock.getD i []) (out.1.getD j []))))
        let generated:=runtimeSequence lower out.2
        have grows : ∀ action,action∈lower → RuntimeGrows action := by
          intro action member current
          obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
          obtain ⟨j,_,hj⟩:=List.mem_filterMap.mp hi
          split_ifs at hj
          cases hj
          exact runtimeWeighted_grows _ _ _ current
        have hg:=runtimeSequence_handles AngularHandles (fun h _ hv=>angular_extend h hv)
          out.2 out.2 lower (RawExtends.refl _) paid.2.1 grows (by
            intro action member current extension currentValid
            obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
            obtain ⟨j,_,hj⟩:=List.mem_filterMap.mp hi
            split_ifs at hj
            cases hj
            exact runtimeWeighted_handles _ _ _ current currentValid
              (series_getD (series_extend (paid.1.trans extension) setupValid.ellclock) i)
              (series_getD (series_extend extension paid.2.2) j))
        let summed:=runAngular (angularAdd generated.1) generated.2
        let negated:=runAngular (angularScale (polynomialCoefficient (-1)) summed.1) summed.2
        let residual:=runAngular (angularAdd [input.getD k [],negated.1]) negated.2
        let answer:=runAngular (angularScale (inversePoleCoefficient 0) residual.1) residual.2
        have hs:=runAngularAdd_handles generated.1 generated.2 hg.1
        have hn:=runAngularScale_handles (polynomialCoefficient (-1)) summed.1 summed.2 hs.1
        have hr:=runAngularAdd_handles [input.getD k [],negated.1] negated.2 hn.1
        have ha:=runAngularScale_handles (inversePoleCoefficient 0) residual.1 residual.2 hr.1
        have grow : RawExtends out.2.arena answer.2.arena :=
          ((((runtimeSequence_grows lower grows out.2).trans (angularAdd_grows _ _)).trans
            (angularScale_grows _ _ _)).trans (angularAdd_grows _ _)).trans (angularScale_grows _ _ _)
        exact ⟨paid.1.trans grow,ha.1,series_append_handles (series_extend grow paid.2.2) ha.2⟩)
      ([],runtime) ⟨RawExtends.refl _,valid,fun row member=>False.elim (List.not_mem_nil member)⟩
    exact ⟨result.2.1.cacheR _ _ result.2.2,result.2.2⟩

theorem originalWord_handles (setup : RawSetup) (tokens : List PreparationVacuumEngineSource.Token) (input : RawSeries)
    (runtime : RawRuntime) (valid : RuntimeHandles runtime) (setupValid : SetupHandles runtime setup)
    (inputValid : SeriesHandles runtime.arena input) :
    RuntimeHandles (originalWord setup tokens input runtime).2 ∧
      SeriesHandles (originalWord setup tokens input runtime).2.arena (originalWord setup tokens input runtime).1 := by
  classical
  dsimp only [originalWord]
  split
  · rename_i output found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ output found
    exact ⟨valid,equal ▸ valid.word entry member⟩
  · let step:=fun (out : RawSeries × RawRuntime) (token : PreparationVacuumEngineSource.Token)=>
      match token with
      | .inverse=>originalResolvent setup out.1 out.2
      | .jordan a=>originalJS setup a out.1 out.2
    have result:=fold_invariant tokens.reverse step
      (fun out=>RawExtends runtime.arena out.2.arena ∧ RuntimeHandles out.2 ∧ SeriesHandles out.2.arena out.1) (by
        intro out paid token member
        cases token with
        | inverse=>exact ⟨paid.1.trans (originalResolvent_grows _ _ _),
            originalResolvent_handles _ _ out.2 paid.2.1 (setupValid.extend paid.1)⟩
        | jordan a=>exact ⟨paid.1.trans (originalJS_grows _ _ _ _),
            originalJS_handles _ _ _ out.2 paid.2.1 (setupValid.extend paid.1) paid.2.2⟩)
      (input,runtime) ⟨RawExtends.refl _,valid,inputValid⟩
    exact ⟨result.2.1.cacheWord _ _ result.2.2,result.2.2⟩


theorem originalTrace_closed_handles (depth : ℕ) (state : RawArena)
    (initialized : RawInitialized state) (closed : RawMoyalClosed state) :
    RawMoyalClosed (originalTrace depth state).2 ∧ SeriesHandles (originalTrace depth state).2 (originalTrace depth state).1 := by
  let four:=originalSource depth 4 state
  let five:=originalSource depth 5 four.2
  let six:=originalSource depth 6 five.2
  have hf:=originalSource_closed_handles depth 4 state initialized closed
  have hv:=originalSource_closed_handles depth 5 four.2 (initialized.trans (originalSource_grows _ _ _)) hf.1
  have hs:=originalSource_closed_handles depth 6 five.2
    ((initialized.trans (originalSource_grows _ _ _)).trans (originalSource_grows _ _ _)) hv.1
  apply angularSequence_closed_handles _ ?_ ?_ six.2 hs.1
  · intro action member current paid
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    exact angularAdd_closed_handles _ _ paid
  · intro action member current
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    exact angularAdd_grows _ _

theorem runtimeTrace_handles (depth : ℕ) (runtime : RawRuntime) (valid : RuntimeHandles runtime) :
    RuntimeHandles (runtimeTrace depth runtime).2 ∧
      SeriesHandles (runtimeTrace depth runtime).2.arena (runtimeTrace depth runtime).1 :=
  ⟨valid.withArena _ (originalTrace_grows _ _) (originalTrace_closed_handles _ _ valid.initialized valid.closed).1,
    (originalTrace_closed_handles _ _ valid.initialized valid.closed).2⟩

theorem series_set_handles {state : RawArena} {series : RawSeries} (valid : SeriesHandles state series)
    (k : ℕ) (polynomial : RawAngular) (new : AngularHandles state polynomial) : SeriesHandles state (series.set k polynomial) := by
  intro row member
  rcases List.mem_or_eq_of_mem_set member with old|equal
  · exact valid row old
  · subst row;exact new

theorem originalApplyT_handles (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4))
    (runtime : RawRuntime) (valid : RuntimeHandles runtime) (setupValid : SetupHandles runtime setup)
    (inputValid : SeriesHandles runtime.arena input) :
    RuntimeHandles (originalApplyT setup a b input equation runtime).2 ∧
      ∀ id,id∈(originalApplyT setup a b input equation runtime).1 → Handle (originalApplyT setup a b input equation runtime).2.arena id := by
  let step:=fun (out : RawSeries × RawRuntime) (term : RawTemporalTerm)=>
    let operated:=originalWord setup term.tokens input out.2
    (List.range (setup.depth+1)).foldl (fun (acc : RawSeries × RawRuntime) k=>
      let scaled:=runAngular (angularScale (polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent)) acc.2
      let added:=runAngular (angularAdd [acc.1.getD k [],scaled.1]) scaled.2
      (acc.1.set k added.1,added.2)) (out.1,operated.2)
  have result:=fold_invariant (rawTemporalTable a b equation) step
    (fun out=>RawExtends runtime.arena out.2.arena ∧ RuntimeHandles out.2 ∧ SeriesHandles out.2.arena out.1) (by
      intro out paid term member
      let operated:=originalWord setup term.tokens input out.2
      have ho:=originalWord_handles setup term.tokens input out.2 paid.2.1 (setupValid.extend paid.1)
        (series_extend paid.1 inputValid)
      have grow:=originalWord_grows setup term.tokens input out.2
      refine fold_invariant (List.range (setup.depth+1)) _
        (fun acc=>RawExtends runtime.arena acc.2.arena ∧ RuntimeHandles acc.2 ∧ SeriesHandles acc.2.arena acc.1) ?_
        (out.1,operated.2) ⟨paid.1.trans grow,ho.1,series_extend grow paid.2.2⟩
      intro acc current k member
      let scaled:=runAngular (angularScale (polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent)) acc.2
      let added:=runAngular (angularAdd [acc.1.getD k [],scaled.1]) scaled.2
      have hs:=runAngularScale_handles (polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent) acc.2 current.2.1
      have ha:=runAngularAdd_handles [acc.1.getD k [],scaled.1] scaled.2 hs.1
      have extension : RawExtends acc.2.arena added.2.arena := (angularScale_grows _ _ _).trans (angularAdd_grows _ _)
      exact ⟨current.1.trans extension,ha.1,series_set_handles (series_extend extension current.2.2) k added.1 ha.2⟩)
    (List.replicate (setup.depth+1) [],runtime) ⟨RawExtends.refl _,valid,by
      intro row member
      have same:row=[] := (List.mem_replicate.mp member).2
      subst row
      intro entry member;exact False.elim (List.not_mem_nil member)⟩
  apply runtimeSequence_handles Handle (fun h _ hv=>handle_extend h hv) _ _ _ (RawExtends.refl _) result.2.1
  · intro action member current
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact angularAverage_grows _ _
  · intro action member current extension currentValid
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact runAverage_handles row current currentValid

theorem originalAffine_handles (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime)
    (valid : RuntimeHandles runtime) (setupValid : SetupHandles runtime setup) :
    RuntimeHandles (originalAffine setup equation runtime).2 ∧
      ∀ id,id∈(originalAffine setup equation runtime).1 → Handle (originalAffine setup equation runtime).2.arena id := by
  cases equation with
  | none=>
    let actions:=(List.finRange 4).map (fun a=>fun current=>
      let source:=runtimeSource setup.depth (Fin.castAdd 9 a) current
      originalJS setup a source.1 source.2)
    have affine:=runtimeSequence_handles SeriesHandles (fun h _ hv=>series_extend h hv)
      runtime runtime actions (RawExtends.refl _) valid (by
        intro action member current
        obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
        exact (runtimeSource_grows _ _ current).trans
          (originalJS_grows setup a _ (runtimeSource setup.depth (Fin.castAdd 9 a) current).2)) (by
        intro action member current extension currentValid
        obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
        let source:=runtimeSource setup.depth (Fin.castAdd 9 a) current
        have hs:=runtimeSource_handles setup.depth (Fin.castAdd 9 a) current currentValid
        exact originalJS_handles setup a source.1 source.2 hs.1
          (setupValid.extend (extension.trans (runtimeSource_grows _ _ current))) hs.2)
    apply runtimeSequence_handles Handle (fun h _ hv=>handle_extend h hv) _ _ _ (RawExtends.refl _) affine.1
    · intro action member current
      obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
      exact rawAdd_extends _ _
    · intro action member current extension currentValid
      obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
      exact runAdd_handles _ current currentValid
  | some a=>
    have hs:=runtimeSource_handles setup.depth (Fin.castAdd 9 a) runtime valid
    apply runtimeSequence_handles Handle (fun h _ hv=>handle_extend h hv) _ _ _ (RawExtends.refl _) hs.1
    · intro action member current
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact rawScale_extends _ _ _
    · intro action member current extension currentValid
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact runScale_handles _ _ current currentValid


def ListHandles (state : RawArena) (ids : List ℕ) : Prop := ∀ id,id∈ids → Handle state id

theorem list_extend {old next : RawArena} (extension : RawExtends old next) {ids : List ℕ}
    (valid : ListHandles old ids) : ListHandles next ids := fun id member=>handle_extend extension (valid id member)

theorem sourceTemporal_handles (setup : RawSetup) (slot : Fin 13) (a b : Fin 4) (equation : Option (Fin 4))
    (runtime : RawRuntime) (valid : RuntimeHandles runtime) (setupValid : SetupHandles runtime setup) :
    let source:=runtimeSource setup.depth slot runtime
    RuntimeHandles (originalApplyT setup a b source.1 equation source.2).2 ∧
      ListHandles (originalApplyT setup a b source.1 equation source.2).2.arena
        (originalApplyT setup a b source.1 equation source.2).1 := by
  let source:=runtimeSource setup.depth slot runtime
  have hs:=runtimeSource_handles setup.depth slot runtime valid
  exact originalApplyT_handles setup a b source.1 equation source.2 hs.1
    (setupValid.extend (runtimeSource_grows setup.depth slot runtime)) hs.2

theorem originalForceOrEnergy_handles (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime)
    (valid : RuntimeHandles runtime) (setupValid : SetupHandles runtime setup) :
    RuntimeHandles (originalForceOrEnergy setup equation runtime).2 ∧
      ListHandles (originalForceOrEnergy setup equation runtime).2.arena (originalForceOrEnergy setup equation runtime).1 := by
  let affine:=originalAffine setup equation runtime
  let trace:=runtimeTrace setup.depth affine.2
  let first:=originalApplyT setup 0 0 trace.1 equation trace.2
  have ha:=originalAffine_handles setup equation runtime valid setupValid
  have ht:=runtimeTrace_handles setup.depth affine.2 ha.1
  have traceGrow : RawExtends runtime.arena trace.2.arena :=
    (originalAffine_grows setup equation runtime).trans (runtimeTrace_grows setup.depth affine.2)
  have hf:=originalApplyT_handles setup 0 0 trace.1 equation trace.2 ht.1 (setupValid.extend traceGrow) ht.2
  have firstGrow:=traceGrow.trans (originalApplyT_grows setup 0 0 trace.1 equation trace.2)
  let diagonalActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨4+i.val,by omega⟩ current
    originalApplyT setup (Fin.succ i) (Fin.succ i) source.1 equation source.2)
  let diagonal:=runtimeSequence diagonalActions first.2
  have diagonalGrows : ∀ action,action∈diagonalActions → RuntimeGrows action := by
    intro action member current
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact (runtimeSource_grows setup.depth ⟨4+i.val,by omega⟩ current).trans
      (originalApplyT_grows setup (Fin.succ i) (Fin.succ i) _ equation
        (runtimeSource setup.depth ⟨4+i.val,by omega⟩ current).2)
  have hd:=runtimeSequence_handles ListHandles (fun h _ hv=>list_extend h hv)
    runtime first.2 diagonalActions firstGrow hf.1 diagonalGrows (by
      intro action member current extension paid
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
      exact sourceTemporal_handles setup ⟨4+i.val,by omega⟩ (Fin.succ i) (Fin.succ i) equation current paid
        (setupValid.extend extension))
  have diagonalGrow:=firstGrow.trans (runtimeSequence_grows diagonalActions diagonalGrows first.2)
  let crossIndices : List (Fin 4 × Fin 4 × Fin 13):=[(1,2,7),(1,3,8),(2,3,9)]
  let crossActions : List (RuntimeAction (List ℕ)) := crossIndices.map (fun entry=>fun current=>
    let source:=runtimeSource setup.depth entry.2.2 current
    originalApplyT setup entry.1 entry.2.1 source.1 equation source.2)
  let cross:=runtimeSequence crossActions diagonal.2
  have crossGrows : ∀ action,action∈crossActions → RuntimeGrows action := by
    intro action member current
    obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
    exact (runtimeSource_grows setup.depth entry.2.2 current).trans
      (originalApplyT_grows setup entry.1 entry.2.1 _ equation (runtimeSource setup.depth entry.2.2 current).2)
  have hc:=runtimeSequence_handles ListHandles (fun h _ hv=>list_extend h hv)
    runtime diagonal.2 crossActions diagonalGrow hd.1 crossGrows (by
      intro action member current extension paid
      obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
      exact sourceTemporal_handles setup entry.2.2 entry.1 entry.2.1 equation current paid (setupValid.extend extension))
  have crossGrow:=diagonalGrow.trans (runtimeSequence_grows crossActions crossGrows diagonal.2)
  let timeActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨10+i.val,by omega⟩ current
    originalApplyT setup 0 (Fin.succ i) source.1 equation source.2)
  let time:=runtimeSequence timeActions cross.2
  have timeGrows : ∀ action,action∈timeActions → RuntimeGrows action := by
    intro action member current
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact (runtimeSource_grows setup.depth ⟨10+i.val,by omega⟩ current).trans
      (originalApplyT_grows setup 0 (Fin.succ i) _ equation (runtimeSource setup.depth ⟨10+i.val,by omega⟩ current).2)
  have htime:=runtimeSequence_handles ListHandles (fun h _ hv=>list_extend h hv)
    runtime cross.2 timeActions crossGrow hc.1 timeGrows (by
      intro action member current extension paid
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
      exact sourceTemporal_handles setup ⟨10+i.val,by omega⟩ 0 (Fin.succ i) equation current paid
        (setupValid.extend extension))
  apply runtimeSequence_handles Handle (fun h _ hv=>handle_extend h hv) time.2 time.2 _ (RawExtends.refl _) htime.1
  · intro action member current
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    apply RawExtends.trans (runtimeSequence_grows _ ?_ current)
    · exact rawAdd_extends _ _
    · intro action member current
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact rawScale_extends _ _ _
  · intro action member current extension paid
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    apply runAdd_handles
    apply (runtimeSequence_handles Handle (fun h _ hv=>handle_extend h hv) current current _ (RawExtends.refl _) paid ?_ ?_).1
    · intro action member state
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact rawScale_extends _ _ _
    · intro action member state grows valid
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact runScale_handles _ _ state valid

end LowEnergy.PreparationVacuumExecutionGraph

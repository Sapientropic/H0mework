import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSetupAngularConvolution

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSetupValues
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumNativeMemo
open PreparationVacuumDAGSemantic PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open PreparationVacuumMoyalNormalization PreparationVacuumArenaBudget PreparationVacuumArenaRows
open PreparationVacuumClockSymbol
open scoped BigOperators Topology
local instance : DecidableEq (Fin 4 × SeriesKey) := Classical.decEq _

theorem readAngular_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (rows : RawAngular) (valid : AngularHandles old rows) :
    readAngular K next rows=readAngular K old rows := by
  unfold readAngular
  rw [angularValue_prefix K extension closed rows valid]

theorem runtimeSequence_angular_values {α : Type} (K : ℕ) (base current : RawRuntime) (items : List α)
    (action : α → RuntimeAction RawAngular) (value : α → AngularField)
    (extension : RawExtends base.arena current.arena) (cached : CachedNative K current)
    (grows : ∀ item,item∈items → RuntimeGrows (action item))
    (step : ∀ item,item∈items → ∀ runtime,RawExtends base.arena runtime.arena → CachedNative K runtime →
      CachedNative K (action item runtime).2 ∧ AngularHandles (action item runtime).2.arena (action item runtime).1 ∧
        AngularAgrees (readAngular K (action item runtime).2.arena (action item runtime).1) (value item)) :
    let result:=runtimeSequence (items.map action) current
    CachedNative K result.2 ∧ SeriesHandles result.2.arena result.1 ∧
      ∀ u x,x∈poleDomain → (result.1.map (fun rows=>readAngular K result.2.arena rows u x))=items.map (fun item=>value item u x) := by
  induction items generalizing current with
  | nil=>exact ⟨cached,fun rows member=>False.elim (List.not_mem_nil member),fun _ _ _=>rfl⟩
  | cons item items ih=>
    have one:=step item (by simp) current extension cached
    have tail:=ih (action item current).2 (extension.trans (grows item (by simp) current)) one.1
      (fun a h=>grows a (List.mem_cons_of_mem _ h)) (fun a h=>step a (List.mem_cons_of_mem _ h))
    have growth : RawExtends (action item current).2.arena (runtimeSequence (items.map action) (action item current).2).2.arena := by
      apply runtimeSequence_grows
      intro a member state
      obtain ⟨entry,h,rfl⟩:=List.mem_map.mp member
      exact grows entry (List.mem_cons_of_mem _ h) state
    refine ⟨tail.1,?_,?_⟩
    · intro rows member
      rcases List.mem_cons.mp member with equal|old
      · subst rows
        exact angular_extend growth one.2.1
      · exact tail.2.1 rows old
    · intro u x hx
      change readAngular K (runtimeSequence (items.map action) (action item current).2).2.arena (action item current).1 u x::
        ((runtimeSequence (items.map action) (action item current).2).1.map (fun rows=>readAngular K
          (runtimeSequence (items.map action) (action item current).2).2.arena rows u x))=_
      rw [readAngular_prefix K growth one.1.handles.closed _ one.2.1,one.2.2 u hx,tail.2.2 u x hx]
      rfl

def jordanIndices (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n+1)).flatMap (fun i=>(List.range (n+1-i)).map (fun j=>(i,j)))

def jordanDegreeAction (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (n : ℕ) : RuntimeAction RawAngular := fun runtime=>
  let actions:=(jordanIndices n).map (fun pair=>runtimeWeighted (n-pair.1-pair.2)
    ((setup.jclocks axis).getD pair.1 []) (input.getD pair.2 []))
  let generated:=runtimeSequence actions runtime
  runAngular (angularAdd generated.1) generated.2

def jordanDegreeValue (K : ℕ) (state : RawArena) (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (n : ℕ) : AngularField :=
  fun u x=>((jordanIndices n).map (fun pair=>convolution (n-pair.1-pair.2)
    (readAngular K state ((setup.jclocks axis).getD pair.1 [])) (readAngular K state (input.getD pair.2 [])) u x)).sum

def jordanGenerated (setup : RawSetup) (axis : Fin 4) (input : RawSeries) : RuntimeAction RawSeries :=
  runtimeSequence ((List.range (setup.depth+1)).map (jordanDegreeAction setup axis input))

theorem originalJS_execution (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime) :
    originalJS setup axis input runtime=
      match memoLookup (axis,seriesKey input) runtime.jMemo with
      | some result=>(result,runtime)
      | none=>let result:=jordanGenerated setup axis input runtime
        (result.1,{result.2 with jMemo:=((axis,seriesKey input),result.1)::result.2.jMemo}) := by
  classical
  unfold originalJS jordanGenerated jordanDegreeAction jordanIndices
  simp only [List.map_flatMap,List.map_map,Function.comp_def]
  rfl

theorem jordanDegree_grows (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (n : ℕ) :
    RuntimeGrows (jordanDegreeAction setup axis input n) := by
  intro runtime
  apply RawExtends.trans (runtimeSequence_grows _ ?_ runtime)
  · exact angularAdd_grows _ _
  · intro action member current
    obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
    exact runtimeWeighted_grows _ _ _ current

theorem jordanDegree_native (K : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (n : ℕ)
    (base current : RawRuntime) (extension : RawExtends base.arena current.arena)
    (baseClosed : RawMoyalClosed base.arena) (cached : CachedNative K current)
    (setupValid : SetupHandles base setup) (inputValid : SeriesHandles base.arena input) :
    CachedNative K (jordanDegreeAction setup axis input n current).2 ∧
      AngularHandles (jordanDegreeAction setup axis input n current).2.arena (jordanDegreeAction setup axis input n current).1 ∧
        AngularAgrees (readAngular K (jordanDegreeAction setup axis input n current).2.arena
          (jordanDegreeAction setup axis input n current).1) (jordanDegreeValue K base.arena setup axis input n) := by
  let action:=fun pair : ℕ × ℕ=>runtimeWeighted (n-pair.1-pair.2)
    ((setup.jclocks axis).getD pair.1 []) (input.getD pair.2 [])
  let value:=fun pair : ℕ × ℕ=>convolution (n-pair.1-pair.2)
    (readAngular K base.arena ((setup.jclocks axis).getD pair.1 [])) (readAngular K base.arena (input.getD pair.2 []))
  have generated:=runtimeSequence_angular_values K base current (jordanIndices n) action value extension cached
    (fun _ _=>runtimeWeighted_grows _ _ _) (by
      intro pair member runtime growth paid
      have lv:=series_getD (setupValid.jclocks axis) pair.1
      have rv:=series_getD inputValid pair.2
      have result:=runtimeWeighted_cached K (n-pair.1-pair.2) _ _ runtime paid (angular_extend growth lv) (angular_extend growth rv)
      refine ⟨result.1,result.2,?_⟩
      intro u x hx
      rw [runtimeWeighted_convolution K _ _ _ runtime paid (angular_extend growth lv) (angular_extend growth rv) u x hx,
        readAngular_prefix K growth baseClosed _ lv,readAngular_prefix K growth baseClosed _ rv])
  let result:=runtimeSequence ((jordanIndices n).map action) current
  have summed:=runAngularAdd_cached result.1 result.2 generated.1
  refine ⟨summed.1,summed.2,?_⟩
  intro u x hx
  change angularValue K (angularAdd result.1 result.2.arena).2 (angularAdd result.1 result.2.arena).1 (fun j=>u j) x=_
  rw [(angularAdd_native K result.1 result.2.arena generated.1.handles.closed generated.1.handles.initialized generated.2.1).2 _ x hx]
  change (result.1.map (fun rows=>readAngular K result.2.arena rows u x)).sum=_
  rw [generated.2.2 u x hx]
  rfl

theorem jordanGenerated_native (K : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries)
    (runtime : RawRuntime) (cached : CachedNative K runtime)
    (setupValid : SetupHandles runtime setup) (inputValid : SeriesHandles runtime.arena input) :
    CachedNative K (jordanGenerated setup axis input runtime).2 ∧
      SeriesHandles (jordanGenerated setup axis input runtime).2.arena (jordanGenerated setup axis input runtime).1 ∧
        ∀ u x,x∈poleDomain → ((jordanGenerated setup axis input runtime).1.map (fun rows=>
          readAngular K (jordanGenerated setup axis input runtime).2.arena rows u x))=
            (List.range (setup.depth+1)).map (fun n=>jordanDegreeValue K runtime.arena setup axis input n u x) :=
  runtimeSequence_angular_values K runtime runtime _ _ _ (RawExtends.refl _) cached
    (fun _ _=>jordanDegree_grows _ _ _ _)
    (fun n _ current growth paid=>jordanDegree_native K setup axis input n runtime current growth cached.handles.closed paid setupValid inputValid)

theorem originalJS_miss_native (K : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries)
    (runtime : RawRuntime) (cached : CachedNative K runtime)
    (setupValid : SetupHandles runtime setup) (inputValid : SeriesHandles runtime.arena input)
    (miss : memoLookup (axis,seriesKey input) runtime.jMemo=none) :
    ∀ u x,x∈poleDomain → ((originalJS setup axis input runtime).1.map (fun rows=>
      readAngular K (originalJS setup axis input runtime).2.arena rows u x))=
        (List.range (setup.depth+1)).map (fun n=>jordanDegreeValue K runtime.arena setup axis input n u x) := by
  rw [originalJS_execution,miss]
  exact (jordanGenerated_native K setup axis input runtime cached setupValid inputValid).2.2

theorem runtimeSequence_jMemo {α : Type} (actions : List (RuntimeAction α))
    (preserves : ∀ action,action∈actions → ∀ runtime,(action runtime).2.jMemo=runtime.jMemo)
    (runtime : RawRuntime) : (runtimeSequence actions runtime).2.jMemo=runtime.jMemo := by
  induction actions generalizing runtime with
  | nil=>rfl
  | cons action actions ih=>
    change (runtimeSequence actions (action runtime).2).2.jMemo=_
    rw [ih (fun a h=>preserves a (List.mem_cons_of_mem _ h)),preserves action (by simp)]

theorem memoPair_jMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoPair r left right runtime).2.jMemo=runtime.jMemo := by
  unfold memoPair
  split
  · rfl
  · dsimp only [cacheMoyalResult]
    split_ifs <;> rfl

theorem memoMoyal_jMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoMoyal r left right runtime).2.jMemo=runtime.jMemo := by
  unfold memoMoyal
  split
  · rfl
  · dsimp only [cacheMoyalResult]
    split_ifs
    · rfl
    · rfl
    · apply runtimeSequence_jMemo
      intro action member current
      obtain ⟨a,_,ha⟩:=List.mem_flatMap.mp member
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
      rw [memoPair_jMemo]
      rfl
    · rfl

theorem memoJordan_jMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoJordan r left right runtime).2.jMemo=runtime.jMemo := by
  change (memoMoyal r right left (memoMoyal r left right runtime).2).2.jMemo=runtime.jMemo
  rw [memoMoyal_jMemo,memoMoyal_jMemo]

theorem weightedStep_jMemo (r : ℕ) (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ)) :
    (weightedStep r out pair).2.jMemo=out.2.jMemo := by
  change (memoJordan r pair.1.2 pair.2.2 out.2).2.jMemo=out.2.jMemo
  exact memoJordan_jMemo r pair.1.2 pair.2.2 out.2

theorem runtimeWeighted_jMemo (r : ℕ) (left right : RawAngular) (runtime : RawRuntime) :
    (runtimeWeighted r left right runtime).2.jMemo=runtime.jMemo := by
  rw [runtimeWeighted_as_fold]
  have invariant (pairs : List ((RawAngle × ℕ) × (RawAngle × ℕ))) (out : RawAngular × RawRuntime) :
      (pairs.foldl (weightedStep r) out).2.jMemo=out.2.jMemo := by
    induction pairs generalizing out with
    | nil=>rfl
    | cons pair pairs ih=>
      rw [List.foldl_cons,ih,weightedStep_jMemo]
  exact invariant _ _

theorem jordanDegree_jMemo (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (n : ℕ) (runtime : RawRuntime) :
    (jordanDegreeAction setup axis input n runtime).2.jMemo=runtime.jMemo := by
  apply runtimeSequence_jMemo
  intro action member current
  obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
  exact runtimeWeighted_jMemo _ _ _ _

theorem jordanGenerated_jMemo (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime) :
    (jordanGenerated setup axis input runtime).2.jMemo=runtime.jMemo := by
  apply runtimeSequence_jMemo
  intro action member current
  obtain ⟨n,_,rfl⟩:=List.mem_map.mp member
  exact jordanDegree_jMemo _ _ _ _ _

def JordanCacheNative (K : ℕ) (setup : RawSetup) (runtime : RawRuntime) : Prop :=
  ∀ entry,entry∈runtime.jMemo → ∃ input : RawSeries,
    seriesKey input=entry.1.2 ∧ SeriesHandles runtime.arena input ∧
      ∀ u x,x∈poleDomain → (entry.2.map (fun rows=>readAngular K runtime.arena rows u x))=
        (List.range (setup.depth+1)).map (fun n=>jordanDegreeValue K runtime.arena setup entry.1.1 input n u x)

theorem jordanDegree_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (n : ℕ)
    (clockValid : SeriesHandles old (setup.jclocks axis)) (inputValid : SeriesHandles old input) :
    jordanDegreeValue K next setup axis input n=jordanDegreeValue K old setup axis input n := by
  funext u x
  unfold jordanDegreeValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  rw [readAngular_prefix K extension closed _ (series_getD clockValid pair.1),
    readAngular_prefix K extension closed _ (series_getD inputValid pair.2)]

theorem key_readAngular (K : ℕ) (state : RawArena) (left right : RawSeries) (key : seriesKey left=seriesKey right) (n : ℕ) :
    readAngular K state (left.getD n [])=readAngular K state (right.getD n []) := by
  have same:=congrArg (fun values=>values.getD n (angularValue K state [])) (seriesKey_same_input K state left right key)
  change (left.map (angularValue K state)).getD n (angularValue K state [])=
    (right.map (angularValue K state)).getD n (angularValue K state []) at same
  rw [List.getD_map,List.getD_map] at same
  unfold readAngular
  rw [same]

theorem jordanDegree_key (K : ℕ) (state : RawArena) (setup : RawSetup) (axis : Fin 4)
    (left right : RawSeries) (key : seriesKey left=seriesKey right) (n : ℕ) :
    jordanDegreeValue K state setup axis left n=jordanDegreeValue K state setup axis right n := by
  funext u x
  unfold jordanDegreeValue
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  rw [key_readAngular K state left right key pair.2]

theorem JordanCacheNative.extend {K : ℕ} {setup : RawSetup} {old next : RawRuntime}
    (native : JordanCacheNative K setup old) (cached : CachedNative K old) (setupValid : SetupHandles old setup)
    (growth : RawExtends old.arena next.arena) (same : next.jMemo=old.jMemo) : JordanCacheNative K setup next := by
  intro entry member
  obtain ⟨input,key,inputValid,value⟩:=native entry (same ▸ member)
  refine ⟨input,key,series_extend growth inputValid,?_⟩
  intro u x hx
  have oldValid:=cached.handles.jordan entry (same ▸ member)
  have outputSame : (entry.2.map (fun rows=>readAngular K next.arena rows u x))=
      (entry.2.map (fun rows=>readAngular K old.arena rows u x)) := by
    apply List.map_congr_left
    intro rows hr
    rw [readAngular_prefix K growth cached.handles.closed rows (oldValid rows hr)]
  rw [outputSame,value u x hx]
  apply List.map_congr_left
  intro n _
  rw [jordanDegree_prefix K growth cached.handles.closed setup entry.1.1 input n
    (setupValid.jclocks entry.1.1) inputValid]

theorem memoLookup_source {κ α : Type} [DecidableEq κ] (key : κ) (entries : List (κ × α))
    (value : α) (found : memoLookup key entries=some value) :
    ∃ entry∈entries,entry.1=key ∧ entry.2=value := by
  unfold memoLookup at found
  obtain ⟨entry,hentry,heq⟩:=Option.map_eq_some_iff.mp found
  have tested : decide (entry.1=key)=true := List.find?_some (p:=fun e : κ × α=>decide (e.1=key)) hentry
  exact ⟨entry,List.mem_of_find?_eq_some hentry,of_decide_eq_true tested,heq⟩

theorem originalJS_native_cache (K : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries)
    (runtime : RawRuntime) (cached : CachedNative K runtime) (native : JordanCacheNative K setup runtime)
    (setupValid : SetupHandles runtime setup) (inputValid : SeriesHandles runtime.arena input) :
    JordanCacheNative K setup (originalJS setup axis input runtime).2 ∧
      ∀ u x,x∈poleDomain → ((originalJS setup axis input runtime).1.map (fun rows=>
        readAngular K (originalJS setup axis input runtime).2.arena rows u x))=
          (List.range (setup.depth+1)).map (fun n=>jordanDegreeValue K runtime.arena setup axis input n u x) := by
  rw [originalJS_execution]
  split
  · rename_i output found
    refine ⟨native,?_⟩
    obtain ⟨entry,member,key,equals⟩:=memoLookup_source _ _ output found
    obtain ⟨original,originalKey,originalValid,value⟩:=native entry member
    intro u x hx
    dsimp only
    rw [←equals,value u x hx]
    apply List.map_congr_left
    intro n _
    rw [show entry.1.1=axis from congrArg Prod.fst key,
      jordanDegree_key K runtime.arena setup axis original input (originalKey.trans (congrArg Prod.snd key)) n]
  · rename_i miss
    let result:=jordanGenerated setup axis input runtime
    have paid:=jordanGenerated_native K setup axis input runtime cached setupValid inputValid
    have growth : RawExtends runtime.arena result.2.arena := by
      apply runtimeSequence_grows
      intro action member current
      obtain ⟨n,_,rfl⟩:=List.mem_map.mp member
      exact jordanDegree_grows _ _ _ _ current
    have old:=native.extend cached setupValid growth (jordanGenerated_jMemo setup axis input runtime)
    refine ⟨?_,paid.2.2⟩
    intro entry member
    rcases List.mem_cons.mp member with equal|earlier
    · subst entry
      refine ⟨input,rfl,series_extend growth inputValid,?_⟩
      intro u x hx
      change (result.1.map (fun rows=>readAngular K result.2.arena rows u x))=_
      rw [paid.2.2 u x hx]
      apply List.map_congr_left
      intro n _
      rw [jordanDegree_prefix K growth cached.handles.closed setup axis input n (setupValid.jclocks axis) inputValid]
    · exact old entry earlier

theorem reset_jordan_native (K depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime) :
    JordanCacheNative K (runtimeSetup depth clocks runtime).1 (runtimeSetup depth clocks runtime).2 := by
  intro entry member
  exact False.elim (List.not_mem_nil member)

def jordanRequests (setup : RawSetup) (requests : List (Fin 4 × RawSeries)) : RuntimeAction (List RawSeries) :=
  runtimeSequence (requests.map (fun request=>originalJS setup request.1 request.2))

theorem jordanRequests_cache (K : ℕ) (setup : RawSetup) (requests : List (Fin 4 × RawSeries))
    (runtime : RawRuntime) (cached : CachedNative K runtime) (native : JordanCacheNative K setup runtime)
    (setupValid : SetupHandles runtime setup)
    (inputs : ∀ request,request∈requests → SeriesHandles runtime.arena request.2) :
    CachedNative K (jordanRequests setup requests runtime).2 ∧
      JordanCacheNative K setup (jordanRequests setup requests runtime).2 := by
  induction requests generalizing runtime with
  | nil=>exact ⟨cached,native⟩
  | cons request requests ih=>
    have inputValid:=inputs request (by simp)
    have one:=originalJS_cached K setup request.1 request.2 runtime cached setupValid inputValid
    have nv:=(originalJS_native_cache K setup request.1 request.2 runtime cached native setupValid inputValid).1
    have growth:=originalJS_grows setup request.1 request.2 runtime
    exact ih (originalJS setup request.1 request.2 runtime).2 one.1 nv (setupValid.extend growth)
      (fun request member=>series_extend growth (inputs request (List.mem_cons_of_mem _ member)))

def actualSetup (order depth : ℕ) : RawSetup × RawRuntime :=
  runtimeSetup depth (originalEngine order).clocks (originalEngine order).runtime

def actualSetupSeries (order depth : ℕ)
    (rows : List (List (RawAngle × Fin (actualSetup order depth).2.arena.polynomials.length))) : RawSeries :=
  rows.map (fun polynomial=>polynomial.map (fun row=>(row.1,row.2.val)))

theorem actualSetupSeries_handles (order depth : ℕ)
    (rows : List (List (RawAngle × Fin (actualSetup order depth).2.arena.polynomials.length))) :
    SeriesHandles (actualSetup order depth).2.arena (actualSetupSeries order depth rows) := by
  intro polynomial member
  obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
  intro row hr
  obtain ⟨entry,_,rfl⟩:=List.mem_map.mp hr
  exact entry.2.isLt

def actualJordanRequests (order depth : ℕ)
    (requests : List (Fin 4 × List (List (RawAngle × Fin (actualSetup order depth).2.arena.polynomials.length)))) :
    List (Fin 4 × RawSeries) := requests.map (fun request=>(request.1,actualSetupSeries order depth request.2))

theorem actual_jordan_cache (order depth : ℕ)
    (requests : List (Fin 4 × List (List (RawAngle × Fin (actualSetup order depth).2.arena.polynomials.length)))) :
    CachedNative (order+1) (jordanRequests (actualSetup order depth).1 (actualJordanRequests order depth requests) (actualSetup order depth).2).2 ∧
      JordanCacheNative (order+1) (actualSetup order depth).1
        (jordanRequests (actualSetup order depth).1 (actualJordanRequests order depth requests) (actualSetup order depth).2).2 := by
  have setupPaid:=runtimeSetup_cached depth (originalEngine order).clocks (originalEngine order).runtime
    (originalEngine_cached (order+1) order) (originalEngine_handles order).clocks
  apply jordanRequests_cache (order+1) _ _ _ setupPaid.1 (reset_jordan_native _ _ _ _) setupPaid.2
  intro request member
  obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
  exact actualSetupSeries_handles order depth source.2

theorem jordanRequests_grows (setup : RawSetup) (requests : List (Fin 4 × RawSeries)) (runtime : RawRuntime) :
    RawExtends runtime.arena (jordanRequests setup requests runtime).2.arena := by
  apply runtimeSequence_grows
  intro action member current
  obtain ⟨request,_,rfl⟩:=List.mem_map.mp member
  exact originalJS_grows setup request.1 request.2 current

def actualJordanRun (order depth : ℕ)
    (requests : List (Fin 4 × List (List (RawAngle × Fin (actualSetup order depth).2.arena.polynomials.length)))) : RawRuntime :=
  (jordanRequests (actualSetup order depth).1 (actualJordanRequests order depth requests) (actualSetup order depth).2).2

def poolSeries (runtime : RawRuntime) (rows : List (List (RawAngle × Fin runtime.arena.polynomials.length))) : RawSeries :=
  rows.map (fun polynomial=>polynomial.map (fun row=>(row.1,row.2.val)))

theorem poolSeries_handles (runtime : RawRuntime) (rows : List (List (RawAngle × Fin runtime.arena.polynomials.length))) :
    SeriesHandles runtime.arena (poolSeries runtime rows) := by
  intro polynomial member
  obtain ⟨source,_,rfl⟩:=List.mem_map.mp member
  intro row hr
  obtain ⟨entry,_,rfl⟩:=List.mem_map.mp hr
  exact entry.2.isLt

theorem actual_jordan_query_native (order depth : ℕ)
    (requests : List (Fin 4 × List (List (RawAngle × Fin (actualSetup order depth).2.arena.polynomials.length))))
    (axis : Fin 4)
    (query : List (List (RawAngle × Fin (actualJordanRun order depth requests).arena.polynomials.length))) :
    let setup:=(actualSetup order depth).1
    let runtime:=actualJordanRun order depth requests
    let input:=poolSeries runtime query
    JordanCacheNative (order+1) setup (originalJS setup axis input runtime).2 ∧
      ∀ u x,x∈poleDomain → ((originalJS setup axis input runtime).1.map (fun rows=>
        readAngular (order+1) (originalJS setup axis input runtime).2.arena rows u x))=
          (List.range (setup.depth+1)).map (fun n=>jordanDegreeValue (order+1) runtime.arena setup axis input n u x) := by
  have paid:=actual_jordan_cache order depth requests
  have setupPaid:=runtimeSetup_cached depth (originalEngine order).clocks (originalEngine order).runtime
    (originalEngine_cached (order+1) order) (originalEngine_handles order).clocks
  have growth:=jordanRequests_grows (actualSetup order depth).1 (actualJordanRequests order depth requests) (actualSetup order depth).2
  exact originalJS_native_cache (order+1) _ axis _ _ paid.1 paid.2 (setupPaid.2.extend growth) (poolSeries_handles _ query)

def readAngularSeries (K : ℕ) (state : RawArena) (rows : RawSeries) : List AngularField := rows.map (readAngular K state)

theorem readAngularSeries_getD (K : ℕ) (state : RawArena) (rows : RawSeries) (n : ℕ) :
    (readAngularSeries K state rows).getD n 0=readAngular K state (rows.getD n []) := by
  exact List.getD_map rows [] (readAngular K state)

theorem readAngularSeries_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (rows : RawSeries) (valid : SeriesHandles old rows) :
    readAngularSeries K next rows=readAngularSeries K old rows := by
  apply List.map_congr_left
  intro row member
  exact readAngular_prefix K extension closed row (valid row member)

def SeriesAgrees (left right : List AngularField) : Prop :=
  ∀ u x,x∈poleDomain → (left.map (fun f=>f u x))=right.map (fun f=>f u x)

theorem SeriesAgrees.getD {left right : List AngularField} (same : SeriesAgrees left right) (n : ℕ) :
    AngularAgrees (left.getD n 0) (right.getD n 0) := by
  intro u x hx
  have equal:=congrArg (fun values : List ℂ=>values.getD n 0) (same u x hx)
  change (left.map (fun f=>f u x)).getD n ((0 : AngularField) u x)=(right.map (fun f=>f u x)).getD n ((0 : AngularField) u x) at equal
  rw [List.getD_map,List.getD_map] at equal
  exact equal

def resolventIndices (n : ℕ) : List (ℕ × ℕ) :=
  (jordanIndices n).filter (fun pair=>¬(pair.1=0 ∧ n-pair.1-pair.2=0))

def resolventNextValue (ell input answers : List AngularField) (n : ℕ) : AngularField := fun u x=>
  (PreparationVacuumDAGCoefficient.coefficientValue (PreparationVacuumDAGCoefficient.inversePoleCoefficient 0) x : ℂ)*
    ((input.getD n 0) u x-((resolventIndices n).map (fun pair=>
      convolution (n-pair.1-pair.2) (ell.getD pair.1 0) (answers.getD pair.2 0) u x)).sum)

def resolventValues (depth : ℕ) (ell input : List AngularField) : List AngularField :=
  (List.range (depth+1)).foldl (fun answers n=>answers++[resolventNextValue ell input answers n]) []

def resolventDegreeAction (setup : RawSetup) (input : RawSeries) (out : RawSeries × RawRuntime) (n : ℕ) : RawSeries × RawRuntime :=
  let lower:=(resolventIndices n).map (fun pair=>runtimeWeighted (n-pair.1-pair.2) (setup.ellclock.getD pair.1 []) (out.1.getD pair.2 []))
  let generated:=runtimeSequence lower out.2
  let summed:=runAngular (angularAdd generated.1) generated.2
  let negated:=runAngular (angularScale (PreparationVacuumDAGCoefficient.polynomialCoefficient (-1)) summed.1) summed.2
  let residual:=runAngular (angularAdd [input.getD n [],negated.1]) negated.2
  let answer:=runAngular (angularScale (PreparationVacuumDAGCoefficient.inversePoleCoefficient 0) residual.1) residual.2
  (out.1++[answer.1],answer.2)

def resolventGenerated (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime) : RawSeries × RawRuntime :=
  (List.range (setup.depth+1)).foldl (resolventDegreeAction setup input) ([],runtime)

theorem filterMap_not_map {α β : Type} (items : List α) (p : α → Prop) [DecidablePred p] (f : α → β) :
    items.filterMap (fun a=>if p a then none else some (f a))=(items.filter (fun a=>¬p a)).map f := by
  induction items with
  | nil=>rfl
  | cons a items ih=>
    simp only [List.filterMap_cons,List.filter_cons]
    by_cases h : p a <;> simp [h,ih]

theorem originalResolvent_execution (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime) :
    originalResolvent setup input runtime=
      match memoLookup (seriesKey input) runtime.rMemo with
      | some result=>(result,runtime)
      | none=>let result:=resolventGenerated setup input runtime
        (result.1,{result.2 with rMemo:=(seriesKey input,result.1)::result.2.rMemo}) := by
  classical
  have lists (n : ℕ) (out : RawSeries × RawRuntime) :
      ((List.range (n+1)).flatMap (fun i=>(List.range (n+1-i)).filterMap (fun j=>
        if i=0 ∧ n-i-j=0 then none else some (runtimeWeighted (n-i-j) (setup.ellclock.getD i []) (out.1.getD j [])))))=
      (resolventIndices n).map (fun pair=>runtimeWeighted (n-pair.1-pair.2) (setup.ellclock.getD pair.1 []) (out.1.getD pair.2 [])) := by
    unfold resolventIndices jordanIndices
    rw [List.filter_flatMap,List.map_flatMap]
    apply congrArg (fun f=>List.flatMap f (List.range (n+1)))
    funext i
    simp only [List.filter_map,List.map_map,Function.comp_def]
    exact filterMap_not_map _ (fun j=>i=0 ∧ n-i-j=0) _
  unfold originalResolvent resolventGenerated resolventDegreeAction
  simp only [lists]
  rfl

theorem runAdd_angular_native (K : ℕ) (rows : List RawAngular) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (valid : SeriesHandles runtime.arena rows) (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) :
    readAngular K (runAngular (angularAdd rows) runtime).2.arena (runAngular (angularAdd rows) runtime).1 u x=
      (rows.map (fun row=>readAngular K runtime.arena row u x)).sum :=
  (angularAdd_native K rows runtime.arena cached.handles.closed cached.handles.initialized valid).2 _ x hx

theorem runScale_angular_native (K : ℕ) (c : PreparationVacuumDAGCoefficient.NormalizedCoefficient)
    (rows : RawAngular) (runtime : RawRuntime) (cached : CachedNative K runtime) (valid : AngularHandles runtime.arena rows)
    (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) :
    readAngular K (runAngular (angularScale c rows) runtime).2.arena (runAngular (angularScale c rows) runtime).1 u x=
      (PreparationVacuumDAGCoefficient.coefficientValue c x : ℂ)*readAngular K runtime.arena rows u x :=
  angularScale_native K c rows runtime.arena cached.handles.closed cached.handles.initialized valid _ x hx

theorem resolventDegree_grows (setup : RawSetup) (input : RawSeries) (out : RawSeries × RawRuntime) (n : ℕ) :
    RawExtends out.2.arena (resolventDegreeAction setup input out n).2.arena := by
  have base:=runtimeSequence_grows
    ((resolventIndices n).map (fun pair=>runtimeWeighted (n-pair.1-pair.2) (setup.ellclock.getD pair.1 []) (out.1.getD pair.2 [])))
    (by
      intro action member runtime
      obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
      exact runtimeWeighted_grows _ _ _ runtime) out.2
  exact (((base.trans (angularAdd_grows _ _)).trans (angularScale_grows _ _ _)).trans
    (angularAdd_grows _ _)).trans (angularScale_grows _ _ _)

theorem resolventDegree_native (K : ℕ) (setup : RawSetup) (input : RawSeries) (base : RawRuntime)
    (out : RawSeries × RawRuntime) (values : List AngularField) (n : ℕ)
    (baseClosed : RawMoyalClosed base.arena) (growth : RawExtends base.arena out.2.arena)
    (cached : CachedNative K out.2) (setupValid : SetupHandles base setup)
    (inputValid : SeriesHandles base.arena input) (answerValid : SeriesHandles out.2.arena out.1)
    (answers : SeriesAgrees (readAngularSeries K out.2.arena out.1) values) :
    CachedNative K (resolventDegreeAction setup input out n).2 ∧
      SeriesHandles (resolventDegreeAction setup input out n).2.arena (resolventDegreeAction setup input out n).1 ∧
        SeriesAgrees (readAngularSeries K (resolventDegreeAction setup input out n).2.arena
          (resolventDegreeAction setup input out n).1)
          (values++[resolventNextValue (readAngularSeries K base.arena setup.ellclock) (readAngularSeries K base.arena input) values n]) := by
  let action:=fun pair : ℕ × ℕ=>runtimeWeighted (n-pair.1-pair.2) (setup.ellclock.getD pair.1 []) (out.1.getD pair.2 [])
  let value:=fun pair : ℕ × ℕ=>convolution (n-pair.1-pair.2)
    (readAngular K base.arena (setup.ellclock.getD pair.1 [])) (values.getD pair.2 0)
  let generated:=runtimeSequence ((resolventIndices n).map action) out.2
  let summed:=runAngular (angularAdd generated.1) generated.2
  let negated:=runAngular (angularScale (PreparationVacuumDAGCoefficient.polynomialCoefficient (-1)) summed.1) summed.2
  let residual:=runAngular (angularAdd [input.getD n [],negated.1]) negated.2
  let answer:=runAngular (angularScale (PreparationVacuumDAGCoefficient.inversePoleCoefficient 0) residual.1) residual.2
  have generatedPaid:=runtimeSequence_angular_values K out.2 out.2 (resolventIndices n) action value (RawExtends.refl _) cached
    (fun _ _=>runtimeWeighted_grows _ _ _) (by
      intro pair member runtime extension paid
      have lv:=angular_extend (growth.trans extension) (series_getD setupValid.ellclock pair.1)
      have rv:=angular_extend extension (series_getD answerValid pair.2)
      have step:=runtimeWeighted_cached K (n-pair.1-pair.2) _ _ runtime paid lv rv
      refine ⟨step.1,step.2,?_⟩
      intro u x hx
      rw [runtimeWeighted_convolution K _ _ _ runtime paid lv rv u x hx,
        readAngular_prefix K (growth.trans extension) baseClosed _ (series_getD setupValid.ellclock pair.1),
        readAngular_prefix K extension cached.handles.closed _ (series_getD answerValid pair.2)]
      apply convolution_congr (n-pair.1-pair.2) _ _ _ _ (fun _ _ _=>rfl) ?_ u hx
      rw [←readAngularSeries_getD]
      exact answers.getD pair.2)
  have generatedGrow : RawExtends out.2.arena generated.2.arena := by
    apply runtimeSequence_grows
    intro act member runtime
    obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
    exact runtimeWeighted_grows _ _ _ runtime
  have summedPaid:=runAngularAdd_cached generated.1 generated.2 generatedPaid.1
  have summedGrow : RawExtends generated.2.arena summed.2.arena := angularAdd_grows _ _
  have negatedPaid:=runAngularScale_cached (PreparationVacuumDAGCoefficient.polynomialCoefficient (-1)) summed.1 summed.2 summedPaid.1
  have negatedGrow : RawExtends summed.2.arena negated.2.arena := angularScale_grows _ _ _
  have toNeg : RawExtends base.arena negated.2.arena := ((growth.trans generatedGrow).trans summedGrow).trans negatedGrow
  have residualValid : SeriesHandles negated.2.arena [input.getD n [],negated.1] := by
    intro rows member
    rcases List.mem_cons.mp member with first|last
    · subst rows;exact angular_extend toNeg (series_getD inputValid n)
    · have same:=List.mem_singleton.mp last
      subst rows;exact negatedPaid.2
  have residualPaid:=runAngularAdd_cached [input.getD n [],negated.1] negated.2 negatedPaid.1
  have answerPaid:=runAngularScale_cached (PreparationVacuumDAGCoefficient.inversePoleCoefficient 0) residual.1 residual.2 residualPaid.1
  have totalGrow : RawExtends out.2.arena answer.2.arena := resolventDegree_grows setup input out n
  refine ⟨answerPaid.1,?_,?_⟩
  · intro rows member
    rcases List.mem_append.mp member with old|fresh
    · exact angular_extend totalGrow (answerValid rows old)
    · have same:=List.mem_singleton.mp fresh
      subst rows;exact answerPaid.2
  · intro u x hx
    change ((out.1++[answer.1]).map (fun rows=>readAngular K answer.2.arena rows)).map (fun f=>f u x)=_
    simp only [List.map_append,List.map_cons,List.map_nil]
    have prefixValues : ((out.1.map (readAngular K answer.2.arena)).map (fun f=>f u x))=values.map (fun f=>f u x) := by
      rw [←readAngularSeries,readAngularSeries_prefix K totalGrow cached.handles.closed out.1 answerValid]
      exact answers u x hx
    rw [prefixValues]
    congr 2
    rw [runScale_angular_native K _ residual.1 residual.2 residualPaid.1 residualPaid.2 u x hx,
      runAdd_angular_native K _ negated.2 negatedPaid.1 residualValid u x hx]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [readAngular_prefix K toNeg baseClosed _ (series_getD inputValid n),
      runScale_angular_native K _ summed.1 summed.2 summedPaid.1 summedPaid.2 u x hx,
      runAdd_angular_native K _ generated.2 generatedPaid.1 generatedPaid.2.1 u x hx,
      generatedPaid.2.2 u x hx]
    have minus : PreparationVacuumDAGCoefficient.coefficientValue
        (PreparationVacuumDAGCoefficient.polynomialCoefficient (-1)) x=(-1 : ℝ) := by
      rw [PreparationVacuumDAGCoefficient.polynomialCoefficient_source]
      simp [PreparationVacuumDAGCoefficient.polynomialSymbol,PreparationVacuumDAGCoefficient.evalAt]
    simp only [resolventNextValue,readAngularSeries_getD,minus,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul,sub_eq_add_neg]
    rfl

theorem resolventFold_native (K : ℕ) (setup : RawSetup) (input : RawSeries) (base : RawRuntime)
    (indices : List ℕ) (out : RawSeries × RawRuntime) (values : List AngularField)
    (baseClosed : RawMoyalClosed base.arena) (growth : RawExtends base.arena out.2.arena)
    (cached : CachedNative K out.2) (setupValid : SetupHandles base setup)
    (inputValid : SeriesHandles base.arena input) (answerValid : SeriesHandles out.2.arena out.1)
    (answers : SeriesAgrees (readAngularSeries K out.2.arena out.1) values) :
    let result:=indices.foldl (resolventDegreeAction setup input) out
    let target:=indices.foldl (fun answers n=>answers++[resolventNextValue
      (readAngularSeries K base.arena setup.ellclock) (readAngularSeries K base.arena input) answers n]) values
    CachedNative K result.2 ∧ SeriesHandles result.2.arena result.1 ∧ SeriesAgrees (readAngularSeries K result.2.arena result.1) target := by
  induction indices generalizing out values with
  | nil=>exact ⟨cached,answerValid,answers⟩
  | cons n indices ih=>
    have step:=resolventDegree_native K setup input base out values n baseClosed growth cached setupValid inputValid answerValid answers
    exact ih (resolventDegreeAction setup input out n) _ (growth.trans (resolventDegree_grows setup input out n))
      step.1 step.2.1 step.2.2

theorem resolventGenerated_native (K : ℕ) (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (setupValid : SetupHandles runtime setup) (inputValid : SeriesHandles runtime.arena input) :
    CachedNative K (resolventGenerated setup input runtime).2 ∧
      SeriesHandles (resolventGenerated setup input runtime).2.arena (resolventGenerated setup input runtime).1 ∧
        SeriesAgrees (readAngularSeries K (resolventGenerated setup input runtime).2.arena (resolventGenerated setup input runtime).1)
          (resolventValues setup.depth (readAngularSeries K runtime.arena setup.ellclock) (readAngularSeries K runtime.arena input)) :=
  resolventFold_native K setup input runtime _ ([],runtime) [] cached.handles.closed (RawExtends.refl _) cached setupValid inputValid
    (fun _ member=>False.elim (List.not_mem_nil member)) (fun _ _ _=>rfl)

theorem originalResolvent_miss_native (K : ℕ) (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (setupValid : SetupHandles runtime setup) (inputValid : SeriesHandles runtime.arena input)
    (miss : memoLookup (seriesKey input) runtime.rMemo=none) :
    SeriesAgrees (readAngularSeries K (originalResolvent setup input runtime).2.arena (originalResolvent setup input runtime).1)
      (resolventValues setup.depth (readAngularSeries K runtime.arena setup.ellclock) (readAngularSeries K runtime.arena input)) := by
  rw [originalResolvent_execution,miss]
  exact (resolventGenerated_native K setup input runtime cached setupValid inputValid).2.2

theorem runtimeSequence_rMemo {α : Type} (actions : List (RuntimeAction α))
    (preserves : ∀ action,action∈actions → ∀ runtime,(action runtime).2.rMemo=runtime.rMemo)
    (runtime : RawRuntime) : (runtimeSequence actions runtime).2.rMemo=runtime.rMemo := by
  induction actions generalizing runtime with
  | nil=>rfl
  | cons action actions ih=>
    change (runtimeSequence actions (action runtime).2).2.rMemo=_
    rw [ih (fun a h=>preserves a (List.mem_cons_of_mem _ h)),preserves action (by simp)]

theorem memoPair_rMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoPair r left right runtime).2.rMemo=runtime.rMemo := by
  unfold memoPair
  split
  · rfl
  · dsimp only [cacheMoyalResult]
    split_ifs <;> rfl

theorem memoMoyal_rMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoMoyal r left right runtime).2.rMemo=runtime.rMemo := by
  unfold memoMoyal
  split
  · rfl
  · dsimp only [cacheMoyalResult]
    split_ifs
    · rfl
    · rfl
    · apply runtimeSequence_rMemo
      intro action member current
      obtain ⟨a,_,ha⟩:=List.mem_flatMap.mp member
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
      rw [memoPair_rMemo]
      rfl
    · rfl

theorem memoJordan_rMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoJordan r left right runtime).2.rMemo=runtime.rMemo := by
  change (memoMoyal r right left (memoMoyal r left right runtime).2).2.rMemo=runtime.rMemo
  rw [memoMoyal_rMemo,memoMoyal_rMemo]

theorem weightedStep_rMemo (r : ℕ) (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ)) :
    (weightedStep r out pair).2.rMemo=out.2.rMemo := by
  change (memoJordan r pair.1.2 pair.2.2 out.2).2.rMemo=out.2.rMemo
  exact memoJordan_rMemo r pair.1.2 pair.2.2 out.2

theorem runtimeWeighted_rMemo (r : ℕ) (left right : RawAngular) (runtime : RawRuntime) :
    (runtimeWeighted r left right runtime).2.rMemo=runtime.rMemo := by
  rw [runtimeWeighted_as_fold]
  have invariant (pairs : List ((RawAngle × ℕ) × (RawAngle × ℕ))) (out : RawAngular × RawRuntime) :
      (pairs.foldl (weightedStep r) out).2.rMemo=out.2.rMemo := by
    induction pairs generalizing out with
    | nil=>rfl
    | cons pair pairs ih=>
      rw [List.foldl_cons,ih,weightedStep_rMemo]
  exact invariant _ _

theorem resolventDegree_rMemo (setup : RawSetup) (input : RawSeries) (out : RawSeries × RawRuntime) (n : ℕ) :
    (resolventDegreeAction setup input out n).2.rMemo=out.2.rMemo := by
  apply runtimeSequence_rMemo
  intro action member runtime
  obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
  exact runtimeWeighted_rMemo _ _ _ _

theorem resolventGenerated_rMemo (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime) :
    (resolventGenerated setup input runtime).2.rMemo=runtime.rMemo := by
  have invariant (indices : List ℕ) (out : RawSeries × RawRuntime) :
      (indices.foldl (resolventDegreeAction setup input) out).2.rMemo=out.2.rMemo := by
    induction indices generalizing out with
    | nil=>rfl
    | cons n indices ih=>rw [List.foldl_cons,ih,resolventDegree_rMemo]
  exact invariant _ _

theorem resolventGenerated_grows (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime) :
    RawExtends runtime.arena (resolventGenerated setup input runtime).2.arena := by
  have invariant (indices : List ℕ) (out : RawSeries × RawRuntime) :
      RawExtends out.2.arena (indices.foldl (resolventDegreeAction setup input) out).2.arena := by
    induction indices generalizing out with
    | nil=>exact RawExtends.refl _
    | cons n indices ih=>exact (resolventDegree_grows setup input out n).trans (ih _)
  exact invariant (List.range (setup.depth+1)) ([],runtime)

theorem readAngularSeries_key (K : ℕ) (state : RawArena) (left right : RawSeries) (key : seriesKey left=seriesKey right) :
    readAngularSeries K state left=readAngularSeries K state right := by
  have same:=congrArg (fun rows=>rows.map (fun f=>fun u : AngularExponent=>f (fun j=>u j)))
    (seriesKey_same_input K state left right key)
  simp only [seriesValue,List.map_map,Function.comp_def] at same
  exact same

def ResolventCacheNative (K : ℕ) (setup : RawSetup) (runtime : RawRuntime) : Prop :=
  ∀ entry,entry∈runtime.rMemo → ∃ input : RawSeries,
    seriesKey input=entry.1 ∧ SeriesHandles runtime.arena input ∧
      SeriesAgrees (readAngularSeries K runtime.arena entry.2)
        (resolventValues setup.depth (readAngularSeries K runtime.arena setup.ellclock) (readAngularSeries K runtime.arena input))

theorem ResolventCacheNative.extend {K : ℕ} {setup : RawSetup} {old next : RawRuntime}
    (native : ResolventCacheNative K setup old) (cached : CachedNative K old) (setupValid : SetupHandles old setup)
    (growth : RawExtends old.arena next.arena) (same : next.rMemo=old.rMemo) : ResolventCacheNative K setup next := by
  intro entry member
  obtain ⟨input,key,inputValid,value⟩:=native entry (same ▸ member)
  refine ⟨input,key,series_extend growth inputValid,?_⟩
  rw [readAngularSeries_prefix K growth cached.handles.closed entry.2 (cached.handles.resolvent entry (same ▸ member)),
    readAngularSeries_prefix K growth cached.handles.closed setup.ellclock setupValid.ellclock,
    readAngularSeries_prefix K growth cached.handles.closed input inputValid]
  exact value

theorem originalResolvent_native_cache (K : ℕ) (setup : RawSetup) (input : RawSeries)
    (runtime : RawRuntime) (cached : CachedNative K runtime) (native : ResolventCacheNative K setup runtime)
    (setupValid : SetupHandles runtime setup) (inputValid : SeriesHandles runtime.arena input) :
    ResolventCacheNative K setup (originalResolvent setup input runtime).2 ∧
      SeriesAgrees (readAngularSeries K (originalResolvent setup input runtime).2.arena (originalResolvent setup input runtime).1)
        (resolventValues setup.depth (readAngularSeries K runtime.arena setup.ellclock) (readAngularSeries K runtime.arena input)) := by
  rw [originalResolvent_execution]
  split
  · rename_i output found
    refine ⟨native,?_⟩
    obtain ⟨entry,member,key,equals⟩:=memoLookup_source _ _ output found
    obtain ⟨original,originalKey,originalValid,value⟩:=native entry member
    dsimp only
    rw [←equals,←readAngularSeries_key K runtime.arena original input (originalKey.trans key)]
    exact value
  · rename_i miss
    let result:=resolventGenerated setup input runtime
    have paid:=resolventGenerated_native K setup input runtime cached setupValid inputValid
    have growth:=resolventGenerated_grows setup input runtime
    have old:=native.extend cached setupValid growth (resolventGenerated_rMemo setup input runtime)
    refine ⟨?_,paid.2.2⟩
    intro entry member
    rcases List.mem_cons.mp member with equal|earlier
    · subst entry
      refine ⟨input,rfl,series_extend growth inputValid,?_⟩
      change SeriesAgrees (readAngularSeries K result.2.arena result.1)
        (resolventValues setup.depth (readAngularSeries K result.2.arena setup.ellclock) (readAngularSeries K result.2.arena input))
      rw [readAngularSeries_prefix K growth cached.handles.closed setup.ellclock setupValid.ellclock,
        readAngularSeries_prefix K growth cached.handles.closed input inputValid]
      exact paid.2.2
    · exact old entry earlier

theorem reset_resolvent_native (K depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime) :
    ResolventCacheNative K (runtimeSetup depth clocks runtime).1 (runtimeSetup depth clocks runtime).2 := by
  intro entry member
  exact False.elim (List.not_mem_nil member)

theorem jordanDegree_rMemo (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (n : ℕ) (runtime : RawRuntime) :
    (jordanDegreeAction setup axis input n runtime).2.rMemo=runtime.rMemo := by
  apply runtimeSequence_rMemo
  intro action member current
  obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
  exact runtimeWeighted_rMemo _ _ _ _

theorem jordanGenerated_rMemo (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime) :
    (jordanGenerated setup axis input runtime).2.rMemo=runtime.rMemo := by
  apply runtimeSequence_rMemo
  intro action member current
  obtain ⟨n,_,rfl⟩:=List.mem_map.mp member
  exact jordanDegree_rMemo _ _ _ _ _

theorem resolventDegree_jMemo (setup : RawSetup) (input : RawSeries) (out : RawSeries × RawRuntime) (n : ℕ) :
    (resolventDegreeAction setup input out n).2.jMemo=out.2.jMemo := by
  apply runtimeSequence_jMemo
  intro action member runtime
  obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
  exact runtimeWeighted_jMemo _ _ _ _

theorem resolventGenerated_jMemo (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime) :
    (resolventGenerated setup input runtime).2.jMemo=runtime.jMemo := by
  have invariant (indices : List ℕ) (out : RawSeries × RawRuntime) :
      (indices.foldl (resolventDegreeAction setup input) out).2.jMemo=out.2.jMemo := by
    induction indices generalizing out with
    | nil=>rfl
    | cons n indices ih=>rw [List.foldl_cons,ih,resolventDegree_jMemo]
  exact invariant _ _

theorem originalJS_rMemo (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime) :
    (originalJS setup axis input runtime).2.rMemo=runtime.rMemo := by
  rw [originalJS_execution]
  split
  · rfl
  · exact jordanGenerated_rMemo setup axis input runtime

theorem originalResolvent_jMemo (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime) :
    (originalResolvent setup input runtime).2.jMemo=runtime.jMemo := by
  rw [originalResolvent_execution]
  split
  · rfl
  · exact resolventGenerated_jMemo setup input runtime

structure SetupNative (K : ℕ) (setup : RawSetup) (runtime : RawRuntime) : Prop where
  cached : CachedNative K runtime
  handles : SetupHandles runtime setup
  jordan : JordanCacheNative K setup runtime
  resolvent : ResolventCacheNative K setup runtime

theorem originalJS_setup_native (K : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime)
    (native : SetupNative K setup runtime) (valid : SeriesHandles runtime.arena input) :
    SetupNative K setup (originalJS setup axis input runtime).2 := by
  have growth:=originalJS_grows setup axis input runtime
  exact ⟨(originalJS_cached K setup axis input runtime native.cached native.handles valid).1,
    native.handles.extend growth,(originalJS_native_cache K setup axis input runtime native.cached native.jordan native.handles valid).1,
    native.resolvent.extend native.cached native.handles growth (originalJS_rMemo setup axis input runtime)⟩

theorem originalResolvent_setup_native (K : ℕ) (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime)
    (native : SetupNative K setup runtime) (valid : SeriesHandles runtime.arena input) :
    SetupNative K setup (originalResolvent setup input runtime).2 := by
  have growth:=originalResolvent_grows setup input runtime
  exact ⟨(originalResolvent_cached K setup input runtime native.cached native.handles).1,
    native.handles.extend growth,native.jordan.extend native.cached native.handles growth (originalResolvent_jMemo setup input runtime),
    (originalResolvent_native_cache K setup input runtime native.cached native.resolvent native.handles valid).1⟩

def jordanValues (depth : ℕ) (clock input : List AngularField) : List AngularField :=
  (List.range (depth+1)).map (fun n=>fun u x=>((jordanIndices n).map (fun pair=>
    convolution (n-pair.1-pair.2) (clock.getD pair.1 0) (input.getD pair.2 0) u x)).sum)

def operationValue (depth : ℕ) (clock : Fin 4 → List AngularField) (ell : List AngularField)
    (token : Token) (input : List AngularField) : List AngularField :=
  match token with
  | .inverse=>resolventValues depth ell input
  | .jordan a=>jordanValues depth (clock a) input

def operationOn (setup : RawSetup) (token : Token) (input : RawSeries) : RuntimeAction RawSeries := fun runtime=>
  match token with
  | .inverse=>originalResolvent setup input runtime
  | .jordan a=>originalJS setup a input runtime

theorem operationOn_grows (setup : RawSetup) (token : Token) (input : RawSeries) (runtime : RawRuntime) :
    RawExtends runtime.arena (operationOn setup token input runtime).2.arena := by
  cases token with
  | inverse=>exact originalResolvent_grows _ _ _
  | jordan a=>exact originalJS_grows _ _ _ _

theorem operationOn_native (K : ℕ) (setup : RawSetup) (token : Token) (input : RawSeries) (runtime : RawRuntime)
    (native : SetupNative K setup runtime) (valid : SeriesHandles runtime.arena input) :
    SetupNative K setup (operationOn setup token input runtime).2 ∧
      SeriesHandles (operationOn setup token input runtime).2.arena (operationOn setup token input runtime).1 ∧
        SeriesAgrees (readAngularSeries K (operationOn setup token input runtime).2.arena (operationOn setup token input runtime).1)
          (operationValue setup.depth (fun a=>readAngularSeries K runtime.arena (setup.jclocks a))
            (readAngularSeries K runtime.arena setup.ellclock) token (readAngularSeries K runtime.arena input)) := by
  cases token with
  | inverse=>
    exact ⟨originalResolvent_setup_native K setup input runtime native valid,
      (originalResolvent_cached K setup input runtime native.cached native.handles).2,
      (originalResolvent_native_cache K setup input runtime native.cached native.resolvent native.handles valid).2⟩
  | jordan a=>
    refine ⟨originalJS_setup_native K setup a input runtime native valid,
      (originalJS_cached K setup a input runtime native.cached native.handles valid).2,?_⟩
    intro u x hx
    have value:=(originalJS_native_cache K setup a input runtime native.cached native.jordan native.handles valid).2 u x hx
    change ((originalJS setup a input runtime).1.map (readAngular K (originalJS setup a input runtime).2.arena)).map (fun f=>f u x)=_
    rw [List.map_map]
    change ((originalJS setup a input runtime).1.map (fun rows=>readAngular K (originalJS setup a input runtime).2.arena rows u x))=_
    rw [value]
    simp only [operationValue,jordanValues,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro n _
    unfold jordanDegreeValue
    simp only [readAngularSeries_getD]

theorem SeriesAgrees.refl (values : List AngularField) : SeriesAgrees values values := fun _ _ _=>rfl

theorem SeriesAgrees.trans {a b c : List AngularField} (ab : SeriesAgrees a b) (bc : SeriesAgrees b c) : SeriesAgrees a c :=
  fun u x hx=>(ab u x hx).trans (bc u x hx)

theorem SeriesAgrees.append {a b c d : List AngularField} (ab : SeriesAgrees a b) (cd : SeriesAgrees c d) :
    SeriesAgrees (a++c) (b++d) := by
  intro u x hx
  simp only [List.map_append,ab u x hx,cd u x hx]

theorem resolventNext_congr (ell input input' answers answers' : List AngularField)
    (hi : SeriesAgrees input input') (ha : SeriesAgrees answers answers') (n : ℕ) :
    AngularAgrees (resolventNextValue ell input answers n) (resolventNextValue ell input' answers' n) := by
  intro u x hx
  unfold resolventNextValue
  rw [hi.getD n u hx]
  congr 2
  apply congrArg List.sum
  apply List.map_congr_left
  intro pair _
  exact convolution_congr _ _ _ _ _ (fun _ _ _=>rfl) (ha.getD pair.2) u hx

theorem resolventValues_congr (depth : ℕ) (ell input input' : List AngularField) (hi : SeriesAgrees input input') :
    SeriesAgrees (resolventValues depth ell input) (resolventValues depth ell input') := by
  have loop (indices : List ℕ) (answers answers' : List AngularField) (ha : SeriesAgrees answers answers') :
      SeriesAgrees (indices.foldl (fun out n=>out++[resolventNextValue ell input out n]) answers)
        (indices.foldl (fun out n=>out++[resolventNextValue ell input' out n]) answers') := by
    induction indices generalizing answers answers' with
    | nil=>exact ha
    | cons n indices ih=>
      apply ih
      apply ha.append
      intro u x hx
      simp only [List.map_cons,List.map_nil,resolventNext_congr ell input input' answers answers' hi ha n u hx]
  exact loop _ [] [] (SeriesAgrees.refl [])

theorem operationValue_congr (depth : ℕ) (clock : Fin 4 → List AngularField) (ell : List AngularField)
    (token : Token) (input input' : List AngularField) (same : SeriesAgrees input input') :
    SeriesAgrees (operationValue depth clock ell token input) (operationValue depth clock ell token input') := by
  cases token with
  | inverse=>exact resolventValues_congr depth ell input input' same
  | jordan a=>
    intro u x hx
    simp only [operationValue,jordanValues,List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro n _
    apply congrArg List.sum
    apply List.map_congr_left
    intro pair _
    exact convolution_congr _ _ _ _ _ (fun _ _ _=>rfl) (same.getD pair.2) u hx

theorem runtimeSequence_wordMemo {α : Type} (actions : List (RuntimeAction α))
    (preserves : ∀ action,action∈actions → ∀ runtime,(action runtime).2.wordMemo=runtime.wordMemo)
    (runtime : RawRuntime) : (runtimeSequence actions runtime).2.wordMemo=runtime.wordMemo := by
  induction actions generalizing runtime with
  | nil=>rfl
  | cons action actions ih=>
    change (runtimeSequence actions (action runtime).2).2.wordMemo=_
    rw [ih (fun a h=>preserves a (List.mem_cons_of_mem _ h)),preserves action (by simp)]

theorem memoPair_wordMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoPair r left right runtime).2.wordMemo=runtime.wordMemo := by
  unfold memoPair
  split
  · rfl
  · dsimp only [cacheMoyalResult]
    split_ifs <;> rfl

theorem memoMoyal_wordMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoMoyal r left right runtime).2.wordMemo=runtime.wordMemo := by
  unfold memoMoyal
  split
  · rfl
  · dsimp only [cacheMoyalResult]
    split_ifs
    · rfl
    · rfl
    · apply runtimeSequence_wordMemo
      intro action member current
      obtain ⟨a,_,ha⟩:=List.mem_flatMap.mp member
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
      rw [memoPair_wordMemo]
      rfl
    · rfl

theorem memoJordan_wordMemo (r left right : ℕ) (runtime : RawRuntime) :
    (memoJordan r left right runtime).2.wordMemo=runtime.wordMemo := by
  change (memoMoyal r right left (memoMoyal r left right runtime).2).2.wordMemo=runtime.wordMemo
  rw [memoMoyal_wordMemo,memoMoyal_wordMemo]

theorem weightedStep_wordMemo (r : ℕ) (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ)) :
    (weightedStep r out pair).2.wordMemo=out.2.wordMemo := by
  change (memoJordan r pair.1.2 pair.2.2 out.2).2.wordMemo=out.2.wordMemo
  exact memoJordan_wordMemo r pair.1.2 pair.2.2 out.2

theorem runtimeWeighted_wordMemo (r : ℕ) (left right : RawAngular) (runtime : RawRuntime) :
    (runtimeWeighted r left right runtime).2.wordMemo=runtime.wordMemo := by
  rw [runtimeWeighted_as_fold]
  have invariant (pairs : List ((RawAngle × ℕ) × (RawAngle × ℕ))) (out : RawAngular × RawRuntime) :
      (pairs.foldl (weightedStep r) out).2.wordMemo=out.2.wordMemo := by
    induction pairs generalizing out with
    | nil=>rfl
    | cons pair pairs ih=>
      rw [List.foldl_cons,ih,weightedStep_wordMemo]
  exact invariant _ _

theorem jordanDegree_wordMemo (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (n : ℕ) (runtime : RawRuntime) :
    (jordanDegreeAction setup axis input n runtime).2.wordMemo=runtime.wordMemo := by
  apply runtimeSequence_wordMemo
  intro action member current
  obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
  exact runtimeWeighted_wordMemo _ _ _ _

theorem jordanGenerated_wordMemo (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime) :
    (jordanGenerated setup axis input runtime).2.wordMemo=runtime.wordMemo := by
  apply runtimeSequence_wordMemo
  intro action member current
  obtain ⟨n,_,rfl⟩:=List.mem_map.mp member
  exact jordanDegree_wordMemo _ _ _ _ _

theorem resolventDegree_wordMemo (setup : RawSetup) (input : RawSeries) (out : RawSeries × RawRuntime) (n : ℕ) :
    (resolventDegreeAction setup input out n).2.wordMemo=out.2.wordMemo := by
  apply runtimeSequence_wordMemo
  intro action member runtime
  obtain ⟨pair,_,rfl⟩:=List.mem_map.mp member
  exact runtimeWeighted_wordMemo _ _ _ _

theorem resolventGenerated_wordMemo (setup : RawSetup) (input : RawSeries) (runtime : RawRuntime) :
    (resolventGenerated setup input runtime).2.wordMemo=runtime.wordMemo := by
  have invariant (indices : List ℕ) (out : RawSeries × RawRuntime) :
      (indices.foldl (resolventDegreeAction setup input) out).2.wordMemo=out.2.wordMemo := by
    induction indices generalizing out with
    | nil=>rfl
    | cons n indices ih=>rw [List.foldl_cons,ih,resolventDegree_wordMemo]
  exact invariant _ _

theorem operationOn_wordMemo (setup : RawSetup) (token : Token) (input : RawSeries) (runtime : RawRuntime) :
    (operationOn setup token input runtime).2.wordMemo=runtime.wordMemo := by
  cases token with
  | inverse=>
    change (originalResolvent setup input runtime).2.wordMemo=_
    rw [originalResolvent_execution]
    split
    · rfl
    · exact resolventGenerated_wordMemo setup input runtime
  | jordan a=>
    change (originalJS setup a input runtime).2.wordMemo=_
    rw [originalJS_execution]
    split
    · rfl
    · exact jordanGenerated_wordMemo setup a input runtime

def wordGenerated (setup : RawSetup) (tokens : List Token) (input : RawSeries) (runtime : RawRuntime) : RawSeries × RawRuntime :=
  tokens.reverse.foldl (fun out token=>operationOn setup token out.1 out.2) (input,runtime)

def wordValues (depth : ℕ) (clock : Fin 4 → List AngularField) (ell : List AngularField) (tokens : List Token)
    (input : List AngularField) : List AngularField := tokens.reverse.foldl (fun out token=>operationValue depth clock ell token out) input

local instance : DecidableEq (List Token × SeriesKey) := Classical.decEq _

theorem originalWord_execution (setup : RawSetup) (tokens : List Token) (input : RawSeries) (runtime : RawRuntime) :
    originalWord setup tokens input runtime=
      match memoLookup (tokens,seriesKey input) runtime.wordMemo with
      | some result=>(result,runtime)
      | none=>let result:=wordGenerated setup tokens input runtime
        (result.1,{result.2 with wordMemo:=((tokens,seriesKey input),result.1)::result.2.wordMemo}) := by
  unfold originalWord wordGenerated operationOn
  rfl

theorem wordGenerated_grows (setup : RawSetup) (tokens : List Token) (input : RawSeries) (runtime : RawRuntime) :
    RawExtends runtime.arena (wordGenerated setup tokens input runtime).2.arena := by
  have loop (tokens : List Token) (out : RawSeries × RawRuntime) :
      RawExtends out.2.arena (tokens.foldl (fun out token=>operationOn setup token out.1 out.2) out).2.arena := by
    induction tokens generalizing out with
    | nil=>exact RawExtends.refl _
    | cons token tokens ih=>exact (operationOn_grows setup token out.1 out.2).trans (ih _)
  exact loop tokens.reverse (input,runtime)

theorem wordGenerated_wordMemo (setup : RawSetup) (tokens : List Token) (input : RawSeries) (runtime : RawRuntime) :
    (wordGenerated setup tokens input runtime).2.wordMemo=runtime.wordMemo := by
  have loop (tokens : List Token) (out : RawSeries × RawRuntime) :
      (tokens.foldl (fun out token=>operationOn setup token out.1 out.2) out).2.wordMemo=out.2.wordMemo := by
    induction tokens generalizing out with
    | nil=>rfl
    | cons token tokens ih=>rw [List.foldl_cons,ih,operationOn_wordMemo]
  exact loop tokens.reverse (input,runtime)

theorem wordFold_native (K : ℕ) (setup : RawSetup) (base : RawRuntime) (tokens : List Token)
    (out : RawSeries × RawRuntime) (values : List AngularField)
    (baseClosed : RawMoyalClosed base.arena) (baseSetup : SetupHandles base setup)
    (growth : RawExtends base.arena out.2.arena) (native : SetupNative K setup out.2)
    (valid : SeriesHandles out.2.arena out.1) (same : SeriesAgrees (readAngularSeries K out.2.arena out.1) values) :
    let result:=tokens.foldl (fun out token=>operationOn setup token out.1 out.2) out
    let target:=tokens.foldl (fun out token=>operationValue setup.depth
      (fun a=>readAngularSeries K base.arena (setup.jclocks a)) (readAngularSeries K base.arena setup.ellclock) token out) values
    SetupNative K setup result.2 ∧ SeriesHandles result.2.arena result.1 ∧
      SeriesAgrees (readAngularSeries K result.2.arena result.1) target := by
  induction tokens generalizing out values with
  | nil=>exact ⟨native,valid,same⟩
  | cons token tokens ih=>
    have step:=operationOn_native K setup token out.1 out.2 native valid
    have clocks : (fun a=>readAngularSeries K out.2.arena (setup.jclocks a))=
        (fun a=>readAngularSeries K base.arena (setup.jclocks a)) := by
      funext a
      exact readAngularSeries_prefix K growth baseClosed _ (baseSetup.jclocks a)
    have target : SeriesAgrees (readAngularSeries K (operationOn setup token out.1 out.2).2.arena
        (operationOn setup token out.1 out.2).1)
        (operationValue setup.depth (fun a=>readAngularSeries K base.arena (setup.jclocks a))
          (readAngularSeries K base.arena setup.ellclock) token values) := by
      have read:=step.2.2
      rw [clocks,readAngularSeries_prefix K growth baseClosed setup.ellclock baseSetup.ellclock] at read
      exact read.trans (operationValue_congr _ _ _ _ _ _ same)
    exact ih (operationOn setup token out.1 out.2) _ (growth.trans (operationOn_grows setup token out.1 out.2)) step.1 step.2.1 target

theorem wordGenerated_native (K : ℕ) (setup : RawSetup) (tokens : List Token) (input : RawSeries) (runtime : RawRuntime)
    (native : SetupNative K setup runtime) (valid : SeriesHandles runtime.arena input) :
    SetupNative K setup (wordGenerated setup tokens input runtime).2 ∧
      SeriesHandles (wordGenerated setup tokens input runtime).2.arena (wordGenerated setup tokens input runtime).1 ∧
        SeriesAgrees (readAngularSeries K (wordGenerated setup tokens input runtime).2.arena (wordGenerated setup tokens input runtime).1)
          (wordValues setup.depth (fun a=>readAngularSeries K runtime.arena (setup.jclocks a))
            (readAngularSeries K runtime.arena setup.ellclock) tokens (readAngularSeries K runtime.arena input)) :=
  wordFold_native K setup runtime tokens.reverse (input,runtime) (readAngularSeries K runtime.arena input)
    native.cached.handles.closed native.handles (RawExtends.refl _) native valid (SeriesAgrees.refl _)

def WordCacheNative (K : ℕ) (setup : RawSetup) (runtime : RawRuntime) : Prop :=
  ∀ entry,entry∈runtime.wordMemo → ∃ input : RawSeries,
    seriesKey input=entry.1.2 ∧ SeriesHandles runtime.arena input ∧
      SeriesAgrees (readAngularSeries K runtime.arena entry.2)
        (wordValues setup.depth (fun a=>readAngularSeries K runtime.arena (setup.jclocks a))
          (readAngularSeries K runtime.arena setup.ellclock) entry.1.1 (readAngularSeries K runtime.arena input))

theorem wordValues_prefix (K : ℕ) {old next : RawArena} (extension : RawExtends old next)
    (closed : RawMoyalClosed old) (setup : RawSetup) (tokens : List Token) (input : RawSeries)
    (clocks : ∀ a,SeriesHandles old (setup.jclocks a)) (ell : SeriesHandles old setup.ellclock) (valid : SeriesHandles old input) :
    wordValues setup.depth (fun a=>readAngularSeries K next (setup.jclocks a)) (readAngularSeries K next setup.ellclock) tokens
      (readAngularSeries K next input)=
    wordValues setup.depth (fun a=>readAngularSeries K old (setup.jclocks a)) (readAngularSeries K old setup.ellclock) tokens
      (readAngularSeries K old input) := by
  have same : (fun a=>readAngularSeries K next (setup.jclocks a))=(fun a=>readAngularSeries K old (setup.jclocks a)) := by
    funext a
    exact readAngularSeries_prefix K extension closed _ (clocks a)
  rw [same,readAngularSeries_prefix K extension closed setup.ellclock ell,readAngularSeries_prefix K extension closed input valid]

theorem WordCacheNative.extend {K : ℕ} {setup : RawSetup} {old next : RawRuntime}
    (native : WordCacheNative K setup old) (cached : CachedNative K old) (setupValid : SetupHandles old setup)
    (growth : RawExtends old.arena next.arena) (same : next.wordMemo=old.wordMemo) : WordCacheNative K setup next := by
  intro entry member
  obtain ⟨input,key,valid,value⟩:=native entry (same ▸ member)
  refine ⟨input,key,series_extend growth valid,?_⟩
  rw [readAngularSeries_prefix K growth cached.handles.closed entry.2 (cached.handles.word entry (same ▸ member)),
    wordValues_prefix K growth cached.handles.closed setup entry.1.1 input setupValid.jclocks setupValid.ellclock valid]
  exact value

theorem originalWord_native_cache (K : ℕ) (setup : RawSetup) (tokens : List Token) (input : RawSeries) (runtime : RawRuntime)
    (native : SetupNative K setup runtime) (words : WordCacheNative K setup runtime) (valid : SeriesHandles runtime.arena input) :
    SetupNative K setup (originalWord setup tokens input runtime).2 ∧
      WordCacheNative K setup (originalWord setup tokens input runtime).2 ∧
        SeriesAgrees (readAngularSeries K (originalWord setup tokens input runtime).2.arena (originalWord setup tokens input runtime).1)
          (wordValues setup.depth (fun a=>readAngularSeries K runtime.arena (setup.jclocks a))
            (readAngularSeries K runtime.arena setup.ellclock) tokens (readAngularSeries K runtime.arena input)) := by
  rw [originalWord_execution]
  split
  · rename_i output found
    refine ⟨native,words,?_⟩
    obtain ⟨entry,member,key,equals⟩:=memoLookup_source _ _ output found
    obtain ⟨original,originalKey,originalValid,value⟩:=words entry member
    dsimp only
    rw [←equals,←readAngularSeries_key K runtime.arena original input (originalKey.trans (congrArg Prod.snd key)),
      ←show entry.1.1=tokens from congrArg Prod.fst key]
    exact value
  · rename_i miss
    let result:=wordGenerated setup tokens input runtime
    have paid:=wordGenerated_native K setup tokens input runtime native valid
    have growth:=wordGenerated_grows setup tokens input runtime
    have old:=words.extend native.cached native.handles growth (wordGenerated_wordMemo setup tokens input runtime)
    refine ⟨⟨paid.1.cached.cacheWord _ _ paid.2.1,⟨paid.1.handles.jclocks,paid.1.handles.ellclock⟩,paid.1.jordan,paid.1.resolvent⟩,?_,paid.2.2⟩
    intro entry member
    rcases List.mem_cons.mp member with equal|earlier
    · subst entry
      refine ⟨input,rfl,series_extend growth valid,?_⟩
      change SeriesAgrees (readAngularSeries K result.2.arena result.1)
        (wordValues setup.depth (fun a=>readAngularSeries K result.2.arena (setup.jclocks a))
          (readAngularSeries K result.2.arena setup.ellclock) tokens (readAngularSeries K result.2.arena input))
      rw [wordValues_prefix K growth native.cached.handles.closed setup tokens input native.handles.jclocks native.handles.ellclock valid]
      exact paid.2.2
    · exact old entry earlier

structure FullSetupNative (K : ℕ) (setup : RawSetup) (runtime : RawRuntime) : Prop where
  operations : SetupNative K setup runtime
  words : WordCacheNative K setup runtime

theorem FullSetupNative.withArena {K : ℕ} {setup : RawSetup} {runtime : RawRuntime}
    (native : FullSetupNative K setup runtime) (next : RawArena) (extension : RawExtends runtime.arena next)
    (closed : RawMoyalClosed next) : FullSetupNative K setup {runtime with arena:=next} :=
  ⟨⟨native.operations.cached.withArena next extension closed,native.operations.handles.extend extension,
    native.operations.jordan.extend native.operations.cached native.operations.handles extension rfl,
    native.operations.resolvent.extend native.operations.cached native.operations.handles extension rfl⟩,
    native.words.extend native.operations.cached native.operations.handles extension rfl⟩

theorem runtimeSetup_full_native (K depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (cached : CachedNative K runtime) (clockValid : ClockHandles runtime.arena clocks) :
    FullSetupNative K (runtimeSetup depth clocks runtime).1 (runtimeSetup depth clocks runtime).2 := by
  have setup:=runtimeSetup_cached depth clocks runtime cached clockValid
  refine ⟨⟨setup.1,setup.2,reset_jordan_native K depth clocks runtime,reset_resolvent_native K depth clocks runtime⟩,?_⟩
  intro entry member
  exact False.elim (List.not_mem_nil member)

def sourceInput (setup : RawSetup) (slot : Option (Fin 13)) : RuntimeAction RawSeries := fun runtime=>
  match slot with
  | none=>runtimeTrace setup.depth runtime
  | some j=>runtimeSource setup.depth j runtime

theorem sourceInput_grows (setup : RawSetup) (slot : Option (Fin 13)) (runtime : RawRuntime) :
    RawExtends runtime.arena (sourceInput setup slot runtime).2.arena := by
  cases slot with
  | none=>exact originalTrace_grows setup.depth runtime.arena
  | some j=>exact originalSource_grows setup.depth j runtime.arena

theorem sourceInput_full_native (K : ℕ) (setup : RawSetup) (slot : Option (Fin 13)) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) :
    FullSetupNative K setup (sourceInput setup slot runtime).2 ∧
      SeriesHandles (sourceInput setup slot runtime).2.arena (sourceInput setup slot runtime).1 := by
  cases slot with
  | none=>
    have paid:=runtimeTrace_cached setup.depth runtime native.operations.cached
    exact ⟨native.withArena _ (originalTrace_grows _ _) paid.1.handles.closed,paid.2⟩
  | some j=>
    have paid:=runtimeSource_cached setup.depth j runtime native.operations.cached
    exact ⟨native.withArena _ (originalSource_grows _ _ _) paid.1.handles.closed,paid.2⟩

theorem originalWord_full_native (K : ℕ) (setup : RawSetup) (tokens : List Token) (input : RawSeries) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (valid : SeriesHandles runtime.arena input) :
    FullSetupNative K setup (originalWord setup tokens input runtime).2 ∧
      SeriesHandles (originalWord setup tokens input runtime).2.arena (originalWord setup tokens input runtime).1 ∧
        SeriesAgrees (readAngularSeries K (originalWord setup tokens input runtime).2.arena (originalWord setup tokens input runtime).1)
          (wordValues setup.depth (fun a=>readAngularSeries K runtime.arena (setup.jclocks a))
            (readAngularSeries K runtime.arena setup.ellclock) tokens (readAngularSeries K runtime.arena input)) := by
  have value:=originalWord_native_cache K setup tokens input runtime native.operations native.words valid
  exact ⟨⟨value.1,value.2.1⟩,(originalWord_cached K setup tokens input runtime native.operations.cached native.operations.handles valid).2,value.2.2⟩

abbrev SourceWordRequest := Option (Fin 13) × List Token

def sourceWord (setup : RawSetup) (request : SourceWordRequest) : RuntimeAction RawSeries := fun runtime=>
  let input:=sourceInput setup request.1 runtime
  originalWord setup request.2 input.1 input.2

def sourceWordValue (K : ℕ) (setup : RawSetup) (request : SourceWordRequest) (runtime : RawRuntime) : List AngularField :=
  let input:=sourceInput setup request.1 runtime
  wordValues setup.depth (fun a=>readAngularSeries K input.2.arena (setup.jclocks a))
    (readAngularSeries K input.2.arena setup.ellclock) request.2 (readAngularSeries K input.2.arena input.1)

theorem sourceWord_native (K : ℕ) (setup : RawSetup) (request : SourceWordRequest) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) :
    FullSetupNative K setup (sourceWord setup request runtime).2 ∧
      SeriesHandles (sourceWord setup request runtime).2.arena (sourceWord setup request runtime).1 ∧
        SeriesAgrees (readAngularSeries K (sourceWord setup request runtime).2.arena (sourceWord setup request runtime).1)
          (sourceWordValue K setup request runtime) := by
  have input:=sourceInput_full_native K setup request.1 runtime native
  exact originalWord_full_native K setup request.2 _ _ input.1 input.2

def sourceWordRequests (setup : RawSetup) (requests : List SourceWordRequest) : RuntimeAction (List RawSeries) :=
  runtimeSequence (requests.map (sourceWord setup))

theorem sourceWordRequests_native (K : ℕ) (setup : RawSetup) (requests : List SourceWordRequest) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) :
    FullSetupNative K setup (sourceWordRequests setup requests runtime).2 := by
  induction requests generalizing runtime with
  | nil=>exact native
  | cons request requests ih=>
    exact ih (sourceWord setup request runtime).2 (sourceWord_native K setup request runtime native).1

def actualSourceWordRun (order depth : ℕ) (requests : List SourceWordRequest) : RawRuntime :=
  (sourceWordRequests (actualSetup order depth).1 requests (actualSetup order depth).2).2

theorem actual_source_word_cache (order depth : ℕ) (requests : List SourceWordRequest) :
    FullSetupNative (order+1) (actualSetup order depth).1 (actualSourceWordRun order depth requests) :=
  sourceWordRequests_native (order+1) _ requests _
    (runtimeSetup_full_native (order+1) depth (originalEngine order).clocks (originalEngine order).runtime
      (originalEngine_cached (order+1) order) (originalEngine_handles order).clocks)

theorem actual_source_word_native (order depth : ℕ) (requests : List SourceWordRequest) (query : SourceWordRequest) :
    let setup:=(actualSetup order depth).1
    let runtime:=actualSourceWordRun order depth requests
    FullSetupNative (order+1) setup (sourceWord setup query runtime).2 ∧
      SeriesHandles (sourceWord setup query runtime).2.arena (sourceWord setup query runtime).1 ∧
        SeriesAgrees (readAngularSeries (order+1) (sourceWord setup query runtime).2.arena (sourceWord setup query runtime).1)
          (sourceWordValue (order+1) setup query runtime) :=
  sourceWord_native (order+1) _ query _ (actual_source_word_cache order depth requests)

theorem SeriesAgrees.coefficient_germ {left right : List AngularField} (same : SeriesAgrees left right)
    (n : ℕ) (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) :
    (left.getD n 0) u=ᶠ[𝓝 x](right.getD n 0) u := by
  filter_upwards [poleDomain_open.mem_nhds hx] with y hy
  exact same.getD n u hy

theorem actual_source_word_all_jets (order depth : ℕ) (requests : List SourceWordRequest) (query : SourceWordRequest)
    (n m : ℕ) (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) (directions : Fin m → Phase) :
    let setup:=(actualSetup order depth).1
    let runtime:=actualSourceWordRun order depth requests
    let result:=sourceWord setup query runtime
    iteratedFDeriv ℝ m ((readAngularSeries (order+1) result.2.arena result.1).getD n 0 u) x directions=
      iteratedFDeriv ℝ m ((sourceWordValue (order+1) setup query runtime).getD n 0 u) x directions := by
  have same:=(actual_source_word_native order depth requests query).2.2.coefficient_germ n u x hx
  exact congrArg (fun D=>D directions) (same.iteratedFDeriv ℝ m).eq_of_nhds

theorem runtimeSequence_full_native {α : Type} (K : ℕ) (setup : RawSetup) (actions : List (RuntimeAction α))
    (runtime : RawRuntime) (native : FullSetupNative K setup runtime)
    (step : ∀ action,action∈actions → ∀ current,FullSetupNative K setup current → FullSetupNative K setup (action current).2) :
    FullSetupNative K setup (runtimeSequence actions runtime).2 := by
  induction actions generalizing runtime with
  | nil=>exact native
  | cons action actions ih=>
    exact ih (action runtime).2 (step action (by simp) runtime native) (fun a h=>step a (List.mem_cons_of_mem _ h))

theorem runAdd_full_native (K : ℕ) (setup : RawSetup) (ids : List ℕ) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) : FullSetupNative K setup (runArena (rawAdd ids) runtime).2 :=
  native.withArena _ (rawAdd_extends _ _) (rawAdd_closed _ _ native.operations.cached.handles.closed)

theorem runScale_full_native (K : ℕ) (setup : RawSetup) (c : PreparationVacuumDAGCoefficient.NormalizedCoefficient) (id : ℕ)
    (runtime : RawRuntime) (native : FullSetupNative K setup runtime) : FullSetupNative K setup (runArena (rawScale c id) runtime).2 :=
  native.withArena _ (rawScale_extends _ _ _) (rawScale_closed _ _ _ native.operations.cached.handles.closed)

theorem runAngularAdd_full_native (K : ℕ) (setup : RawSetup) (rows : List RawAngular) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) : FullSetupNative K setup (runAngular (angularAdd rows) runtime).2 :=
  native.withArena _ (angularAdd_grows _ _) (runAngularAdd_cached rows runtime native.operations.cached).1.handles.closed

theorem runAngularScale_full_native (K : ℕ) (setup : RawSetup) (c : PreparationVacuumDAGCoefficient.NormalizedCoefficient)
    (rows : RawAngular) (runtime : RawRuntime) (native : FullSetupNative K setup runtime) :
    FullSetupNative K setup (runAngular (angularScale c rows) runtime).2 :=
  native.withArena _ (angularScale_grows _ _ _) (runAngularScale_cached c rows runtime native.operations.cached).1.handles.closed

theorem runAverage_full_native (K : ℕ) (setup : RawSetup) (rows : RawAngular) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) : FullSetupNative K setup (runArena (angularAverage rows) runtime).2 :=
  native.withArena _ (angularAverage_grows _ _) (runAverage_cached rows runtime native.operations.cached).1.handles.closed

theorem originalJS_full_native (K : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) (valid : SeriesHandles runtime.arena input) :
    FullSetupNative K setup (originalJS setup axis input runtime).2 :=
  ⟨originalJS_setup_native K setup axis input runtime native.operations valid,
    native.words.extend native.operations.cached native.operations.handles (originalJS_grows setup axis input runtime)
      (operationOn_wordMemo setup (.jordan axis) input runtime)⟩

theorem originalApplyT_full_native (K : ℕ) (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4))
    (runtime : RawRuntime) (native : FullSetupNative K setup runtime) (inputValid : SeriesHandles runtime.arena input) :
    FullSetupNative K setup (originalApplyT setup a b input equation runtime).2 := by
  let step:=fun (out : RawSeries × RawRuntime) (term : RawTemporalTerm)=>
    let operated:=originalWord setup term.tokens input out.2
    (List.range (setup.depth+1)).foldl (fun (acc : RawSeries × RawRuntime) k=>
      let scaled:=runAngular (angularScale (PreparationVacuumDAGCoefficient.polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent)) acc.2
      let added:=runAngular (angularAdd [acc.1.getD k [],scaled.1]) scaled.2
      (acc.1.set k added.1,added.2)) (out.1,operated.2)
  have result:=fold_invariant (rawTemporalTable a b equation) step
    (fun out=>RawExtends runtime.arena out.2.arena ∧ FullSetupNative K setup out.2) (by
      intro out paid term member
      let operated:=originalWord setup term.tokens input out.2
      have ho:=originalWord_full_native K setup term.tokens input out.2 paid.2 (series_extend paid.1 inputValid)
      have grow:=originalWord_grows setup term.tokens input out.2
      refine fold_invariant (List.range (setup.depth+1)) _
        (fun acc=>RawExtends runtime.arena acc.2.arena ∧ FullSetupNative K setup acc.2) ?_
        (out.1,operated.2) ⟨paid.1.trans grow,ho.1⟩
      intro acc current k member
      let scaled:=runAngular (angularScale (PreparationVacuumDAGCoefficient.polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent)) acc.2
      let added:=runAngular (angularAdd [acc.1.getD k [],scaled.1]) scaled.2
      have hs:=runAngularScale_full_native K setup (PreparationVacuumDAGCoefficient.polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent) acc.2 current.2
      have ha:=runAngularAdd_full_native K setup [acc.1.getD k [],scaled.1] scaled.2 hs
      exact ⟨current.1.trans ((angularScale_grows _ _ _).trans (angularAdd_grows _ _)),ha⟩)
    (List.replicate (setup.depth+1) [],runtime) ⟨RawExtends.refl _,native⟩
  apply runtimeSequence_full_native K setup _ _ result.2
  intro action member current paid
  obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
  exact runAverage_full_native K setup row current paid

theorem originalAffine_full_native (K : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) : FullSetupNative K setup (originalAffine setup equation runtime).2 := by
  cases equation with
  | none=>
    let actions:=(List.finRange 4).map (fun a=>fun current=>
      let source:=runtimeSource setup.depth (Fin.castAdd 9 a) current
      originalJS setup a source.1 source.2)
    have affine:=runtimeSequence_full_native K setup actions runtime native (by
      intro action member current paid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      have source:=sourceInput_full_native K setup (some (Fin.castAdd 9 a)) current paid
      exact originalJS_full_native K setup a _ _ source.1 source.2)
    apply runtimeSequence_full_native K setup _ _ affine
    intro action member current paid
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    exact runAdd_full_native K setup _ current paid
  | some a=>
    have source:=sourceInput_full_native K setup (some (Fin.castAdd 9 a)) runtime native
    apply runtimeSequence_full_native K setup _ _ source.1
    intro action member current paid
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact runScale_full_native K setup _ _ current paid

theorem sourceTemporal_full_native (K : ℕ) (setup : RawSetup) (slot : Fin 13) (a b : Fin 4) (equation : Option (Fin 4))
    (runtime : RawRuntime) (native : FullSetupNative K setup runtime) :
    let source:=runtimeSource setup.depth slot runtime
    FullSetupNative K setup (originalApplyT setup a b source.1 equation source.2).2 := by
  have source:=sourceInput_full_native K setup (some slot) runtime native
  exact originalApplyT_full_native K setup a b _ equation _ source.1 source.2

theorem originalForceOrEnergy_full_native (K : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime)
    (native : FullSetupNative K setup runtime) : FullSetupNative K setup (originalForceOrEnergy setup equation runtime).2 := by
  let affine:=originalAffine setup equation runtime
  let trace:=runtimeTrace setup.depth affine.2
  let first:=originalApplyT setup 0 0 trace.1 equation trace.2
  have ha:=originalAffine_full_native K setup equation runtime native
  have ht:=sourceInput_full_native K setup none affine.2 ha
  have hf:=originalApplyT_full_native K setup 0 0 trace.1 equation trace.2 ht.1 ht.2
  let diagonalActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨4+i.val,by omega⟩ current
    originalApplyT setup (Fin.succ i) (Fin.succ i) source.1 equation source.2)
  let diagonal:=runtimeSequence diagonalActions first.2
  have hd:=runtimeSequence_full_native K setup diagonalActions first.2 hf (by
    intro action member current paid
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_full_native K setup ⟨4+i.val,by omega⟩ (Fin.succ i) (Fin.succ i) equation current paid)
  let crossIndices : List (Fin 4 × Fin 4 × Fin 13):=[(1,2,7),(1,3,8),(2,3,9)]
  let crossActions : List (RuntimeAction (List ℕ)) := crossIndices.map (fun entry=>fun current=>
    let source:=runtimeSource setup.depth entry.2.2 current
    originalApplyT setup entry.1 entry.2.1 source.1 equation source.2)
  let cross:=runtimeSequence crossActions diagonal.2
  have hc:=runtimeSequence_full_native K setup crossActions diagonal.2 hd (by
    intro action member current paid
    obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_full_native K setup entry.2.2 entry.1 entry.2.1 equation current paid)
  let timeActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨10+i.val,by omega⟩ current
    originalApplyT setup 0 (Fin.succ i) source.1 equation source.2)
  let time:=runtimeSequence timeActions cross.2
  have ht:=runtimeSequence_full_native K setup timeActions cross.2 hc (by
    intro action member current paid
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_full_native K setup ⟨10+i.val,by omega⟩ 0 (Fin.succ i) equation current paid)
  apply runtimeSequence_full_native K setup _ time.2 ht
  intro action member current paid
  obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
  apply runAdd_full_native K setup
  apply runtimeSequence_full_native K setup _ current paid
  intro action member state statePaid
  obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
  exact runScale_full_native K setup _ _ state statePaid

theorem originalChecks_full_native (K : ℕ) (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ)
    (runtime : RawRuntime) (native : FullSetupNative K setup runtime) :
    FullSetupNative K setup (originalChecks setup order residualIds clockIds runtime).2.2 := by
  apply fold_invariant (List.finRange 4) _ (fun out : List ℕ × List Bool × RawRuntime=>FullSetupNative K setup out.2.2) ?_
    ([],[],runtime) native
  intro out paid a member
  let result:=originalForceOrEnergy setup (some a) out.2.2
  let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
    (rawScale (jacobianCoefficient a b) (clockIds.getD b.val 0)))) result.2
  have hf:=originalForceOrEnergy_full_native K setup (some a) out.2.2 paid
  have hs : FullSetupNative K setup scaled.2 := runtimeSequence_full_native K setup _ result.2 hf (by
    intro action member current native
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
    exact runScale_full_native K setup _ _ current native)
  exact runAdd_full_native K setup ((residualIds.getD a.val 0)::scaled.1) scaled.2 hs

def engineNextSetup (k : ℕ) (engine : RawEngineState) : RawSetup :=
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let residuals:=runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))) before.2
  let installed:=originalInstall k (residuals.1.map (fun row=>row.getD (k+1) 0)) engine.clocks residuals.2
  (runtimeSetup (k+1) installed.1 installed.2.2.2).1

theorem originalEngineNext_full_native (K k : ℕ) (engine : RawEngineState)
    (cached : CachedNative K engine.runtime) (clocks : ClockHandles engine.runtime.arena engine.clocks) :
    FullSetupNative K (engineNextSetup k engine) (originalEngineNext k engine).runtime := by
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))
  let residuals:=runtimeSequence actions before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  let checked:=originalChecks after.1 (k+1) residualIds installed.2.1 after.2
  have hb:=runtimeSetup_cached (k+1) engine.clocks engine.runtime cached clocks
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  have hr:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    before.2 before.2 actions (RawExtends.refl _) hb.1 grows (by
      intro action member current extension currentValid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalForceOrEnergy_cached K before.1 (some a) current currentValid (hb.2.extend extension))
  have clockGrow : RawExtends engine.runtime.arena residuals.2.arena :=
    (runtimeSetup_grows _ _ _).trans (runtimeSequence_grows actions grows before.2)
  have hi:=originalInstall_cached K k residualIds engine.clocks residuals.2 hr.1 (clocks_extend clockGrow clocks)
  have ha:=runtimeSetup_full_native K (k+1) installed.1 installed.2.2.2 hi.1 hi.2.1
  have hc:=originalChecks_full_native K after.1 (k+1) residualIds installed.2.1 after.2 ha
  exact originalForceOrEnergy_full_native K after.1 none checked.2.2 hc

theorem originalEngine_full_native (K k : ℕ) :
    FullSetupNative K (engineNextSetup k (originalEngine k)) (originalEngine (k+1)).runtime :=
  originalEngineNext_full_native K k (originalEngine k) (originalEngine_cached K k) (originalEngine_handles k).clocks

theorem actual_engine_source_word_native (k : ℕ) (query : SourceWordRequest) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    FullSetupNative (k+1) setup (sourceWord setup query runtime).2 ∧
      SeriesHandles (sourceWord setup query runtime).2.arena (sourceWord setup query runtime).1 ∧
        SeriesAgrees (readAngularSeries (k+1) (sourceWord setup query runtime).2.arena (sourceWord setup query runtime).1)
          (sourceWordValue (k+1) setup query runtime) :=
  sourceWord_native (k+1) _ query _ (originalEngine_full_native (k+1) k)

theorem actual_engine_source_word_all_jets (k : ℕ) (query : SourceWordRequest)
    (n m : ℕ) (u : AngularExponent) (x : Phase) (hx : x∈poleDomain) (directions : Fin m → Phase) :
    let setup:=engineNextSetup k (originalEngine k)
    let runtime:=(originalEngine (k+1)).runtime
    let result:=sourceWord setup query runtime
    iteratedFDeriv ℝ m ((readAngularSeries (k+1) result.2.arena result.1).getD n 0 u) x directions=
      iteratedFDeriv ℝ m ((sourceWordValue (k+1) setup query runtime).getD n 0 u) x directions := by
  have same:=(actual_engine_source_word_native k query).2.2.coefficient_germ n u x hx
  exact congrArg (fun D=>D directions) (same.iteratedFDeriv ℝ m).eq_of_nhds

end LowEnergy.PreparationVacuumSetupValues

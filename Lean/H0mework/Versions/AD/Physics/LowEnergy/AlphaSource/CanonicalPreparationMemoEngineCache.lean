import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationMemoNative

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

theorem runAdd_cached {K : ℕ} (ids : List ℕ) (runtime : RawRuntime) (valid : CachedNative K runtime) :
    CachedNative K (runArena (rawAdd ids) runtime).2 ∧ Handle (runArena (rawAdd ids) runtime).2.arena (runArena (rawAdd ids) runtime).1 :=
  runArena_cached _ (rawAdd_extends ids) (rawAdd_closed ids) (fun _ _=>rawPoly_bound _ _) runtime valid

theorem runScale_cached {K : ℕ} (c : NormalizedCoefficient) (id : ℕ) (runtime : RawRuntime) (valid : CachedNative K runtime) :
    CachedNative K (runArena (rawScale c id) runtime).2 ∧ Handle (runArena (rawScale c id) runtime).2.arena (runArena (rawScale c id) runtime).1 :=
  runArena_cached _ (rawScale_extends c id) (rawScale_closed c id) (fun _ _=>rawPoly_bound _ _) runtime valid

theorem runScalar_cached {K : ℕ} (c : NormalizedCoefficient) (runtime : RawRuntime) (valid : CachedNative K runtime) :
    CachedNative K (runArena (rawScalar c) runtime).2 ∧ Handle (runArena (rawScalar c) runtime).2.arena (runArena (rawScalar c) runtime).1 :=
  runArena_cached _ (rawScalar_extends c) (rawScalar_closed c) (fun _ _=>rawPoly_bound _ _) runtime valid

theorem runAtom_cached {K : ℕ} (kind : RawKind) (central : Bool) (runtime : RawRuntime) (valid : CachedNative K runtime)
    (dependencies : ∀ id,id∈kind.dependencies → Handle runtime.arena id) :
    CachedNative K (runArena (rawAtom kind central) runtime).2 ∧
      Handle (runArena (rawAtom kind central) runtime).2.arena (runArena (rawAtom kind central) runtime).1 :=
  ⟨valid.withArena _ (rawAtom_extends _ _ _) (rawAtom_closed _ _ _ valid.handles.closed dependencies),rawPoly_bound _ _⟩

theorem runAngularAdd_cached {K : ℕ} (inputs : List RawAngular) (runtime : RawRuntime) (valid : CachedNative K runtime) :
    CachedNative K (runAngular (angularAdd inputs) runtime).2 ∧
      AngularHandles (runAngular (angularAdd inputs) runtime).2.arena (runAngular (angularAdd inputs) runtime).1 :=
  ⟨valid.withArena _ (angularAdd_grows _ _) (angularAdd_closed_handles _ _ valid.handles.closed).1,
    (angularAdd_closed_handles _ _ valid.handles.closed).2⟩

theorem runAngularScale_cached {K : ℕ} (c : NormalizedCoefficient) (input : RawAngular) (runtime : RawRuntime)
    (valid : CachedNative K runtime) : CachedNative K (runAngular (angularScale c input) runtime).2 ∧
      AngularHandles (runAngular (angularScale c input) runtime).2.arena (runAngular (angularScale c input) runtime).1 :=
  ⟨valid.withArena _ (angularScale_grows _ _ _) (angularScale_closed_handles _ _ _ valid.handles.closed).1,
    (angularScale_closed_handles _ _ _ valid.handles.closed).2⟩

theorem runAverage_cached {K : ℕ} (input : RawAngular) (runtime : RawRuntime) (valid : CachedNative K runtime) :
    CachedNative K (runArena (angularAverage input) runtime).2 ∧
      Handle (runArena (angularAverage input) runtime).2.arena (runArena (angularAverage input) runtime).1 :=
  ⟨valid.withArena _ (angularAverage_grows _ _) (angularAverage_closed_handles _ _ valid.handles.closed).1,
    (angularAverage_closed_handles _ _ valid.handles.closed).2⟩

theorem runtimeSource_cached {K : ℕ} (depth : ℕ) (slot : Fin 13) (runtime : RawRuntime) (valid : CachedNative K runtime) :
    CachedNative K (runtimeSource depth slot runtime).2 ∧
      SeriesHandles (runtimeSource depth slot runtime).2.arena (runtimeSource depth slot runtime).1 :=
  ⟨valid.withArena _ (originalSource_grows _ _ _)
    (originalSource_closed_handles _ _ _ valid.handles.initialized valid.handles.closed).1,
    (originalSource_closed_handles _ _ _ valid.handles.initialized valid.handles.closed).2⟩

theorem runtimeTrace_cached {K : ℕ} (depth : ℕ) (runtime : RawRuntime) (valid : CachedNative K runtime) :
    CachedNative K (runtimeTrace depth runtime).2 ∧
      SeriesHandles (runtimeTrace depth runtime).2.arena (runtimeTrace depth runtime).1 :=
  ⟨valid.withArena _ (originalTrace_grows _ _)
    (originalTrace_closed_handles _ _ valid.handles.initialized valid.handles.closed).1,
    (originalTrace_closed_handles _ _ valid.handles.initialized valid.handles.closed).2⟩

theorem runtimeSetup_cached {K : ℕ} (depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime) (valid : CachedNative K runtime)
    (clockValid : ClockHandles runtime.arena clocks) :
    CachedNative K (runtimeSetup depth clocks runtime).2 ∧
      SetupHandles (runtimeSetup depth clocks runtime).2 (runtimeSetup depth clocks runtime).1 := by
  have generated:=runtimeSetup_handles depth clocks runtime valid.handles clockValid
  have arena:=valid.withArena (originalSetup depth clocks runtime.arena).2 (originalSetup_grows _ _ _)
    (originalSetup_closed_handles _ _ _ valid.handles.initialized valid.handles.closed clockValid).1
  exact ⟨⟨generated.1,arena.moyal⟩,generated.2⟩

theorem runtimeSequence_cached {α : Type} (K : ℕ) (P : RawArena → α → Prop)
    (monotone : ∀ {old next},RawExtends old next → ∀ value,P old value → P next value)
    (base current : RawRuntime) (actions : List (RuntimeAction α))
    (extension : RawExtends base.arena current.arena) (valid : CachedNative K current)
    (grows : ∀ action,action∈actions → RuntimeGrows action)
    (step : ∀ action,action∈actions → ∀ state,RawExtends base.arena state.arena → CachedNative K state →
      CachedNative K (action state).2 ∧ P (action state).2.arena (action state).1) :
    CachedNative K (runtimeSequence actions current).2 ∧
      ∀ value,value∈(runtimeSequence actions current).1 → P (runtimeSequence actions current).2.arena value := by
  induction actions generalizing current with
  | nil=>exact ⟨valid,fun value member=>False.elim (List.not_mem_nil member)⟩
  | cons action actions ih=>
    have one:=step action (by simp) current extension valid
    have next:=ih (action current).2 (extension.trans (grows action (by simp) current)) one.1
      (fun a h=>grows a (List.mem_cons_of_mem _ h)) (fun a h=>step a (List.mem_cons_of_mem _ h))
    refine ⟨next.1,?_⟩
    intro value member
    rcases List.mem_cons.mp member with equal|old
    · subst value
      exact monotone (runtimeSequence_grows actions (fun a h=>grows a (List.mem_cons_of_mem _ h)) (action current).2) _ one.2
    · exact next.2 value old

theorem runtimeWeighted_cached (K r : ℕ) (left right : RawAngular) (runtime : RawRuntime)
    (valid : CachedNative K runtime) (leftValid : AngularHandles runtime.arena left)
    (rightValid : AngularHandles runtime.arena right) :
    CachedNative K (runtimeWeighted r left right runtime).2 ∧
      AngularHandles (runtimeWeighted r left right runtime).2.arena (runtimeWeighted r left right runtime).1 := by
  let pairs:=left.flatMap (fun a=>right.map (fun b=>(a,b)))
  let step:=fun (out : RawAngular × RawRuntime) (pair : (RawAngle × ℕ) × (RawAngle × ℕ))=>
    let key:=pair.1.1+pair.2.1
    let product:=memoJordan r pair.1.2 pair.2.2 out.2
    let added:=runArena (rawAdd [angularLookup key out.1,product.1]) product.2
    (angularInsert key added.1 out.1,added.2)
  have result:=fold_invariant pairs step
    (fun out=>RawExtends runtime.arena out.2.arena ∧ CachedNative K out.2 ∧ AngularHandles out.2.arena out.1) (by
      intro out paid pair member
      obtain ⟨a,ha,hr⟩:=List.mem_flatMap.mp member
      obtain ⟨b,hb,same⟩:=List.mem_map.mp hr
      subst pair
      let product:=memoJordan r a.2 b.2 out.2
      let added:=runArena (rawAdd [angularLookup (a.1+b.1) out.1,product.1]) product.2
      have hp:=memoJordan_native K r a.2 b.2 out.2 paid.2.1
        (handle_extend paid.1 (leftValid a ha)) (handle_extend paid.1 (rightValid b hb))
      have hs:=runAdd_cached [angularLookup (a.1+b.1) out.1,product.1] product.2 hp.1
      have grow : RawExtends out.2.arena added.2.arena :=
        (memoJordan_grows r a.2 b.2 out.2).trans (rawAdd_extends _ _)
      exact ⟨paid.1.trans grow,hs.1,angularInsert_handles (angular_extend grow paid.2.2) _ _ hs.2⟩)
    ([],runtime) ⟨RawExtends.refl _,valid,fun row member=>False.elim (List.not_mem_nil member)⟩
  exact ⟨result.2.1,angularNonzero_handles result.2.2⟩

theorem CachedNative.cacheJ {K : ℕ} {runtime : RawRuntime} (valid : CachedNative K runtime)
    (key : Fin 4 × SeriesKey) (value : RawSeries) (bound : SeriesHandles runtime.arena value) :
    CachedNative K {runtime with jMemo:=(key,value)::runtime.jMemo} :=
  ⟨valid.handles.cacheJ key value bound,valid.moyal⟩

theorem CachedNative.cacheR {K : ℕ} {runtime : RawRuntime} (valid : CachedNative K runtime)
    (key : SeriesKey) (value : RawSeries) (bound : SeriesHandles runtime.arena value) :
    CachedNative K {runtime with rMemo:=(key,value)::runtime.rMemo} :=
  ⟨valid.handles.cacheR key value bound,valid.moyal⟩

theorem CachedNative.cacheWord {K : ℕ} {runtime : RawRuntime} (valid : CachedNative K runtime)
    (key : List PreparationVacuumEngineSource.Token × SeriesKey) (value : RawSeries)
    (bound : SeriesHandles runtime.arena value) :
    CachedNative K {runtime with wordMemo:=(key,value)::runtime.wordMemo} :=
  ⟨valid.handles.cacheWord key value bound,valid.moyal⟩


theorem originalJS_cached (K : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries)
    (runtime : RawRuntime) (valid : CachedNative K runtime) (setupValid : SetupHandles runtime setup)
    (inputValid : SeriesHandles runtime.arena input) :
    CachedNative K (originalJS setup axis input runtime).2 ∧
      SeriesHandles (originalJS setup axis input runtime).2.arena (originalJS setup axis input runtime).1 := by
  classical
  dsimp only [originalJS]
  split
  · rename_i output found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ output found
    exact ⟨valid,equal ▸ valid.handles.jordan entry member⟩
  · have result:=runtimeSequence_cached K AngularHandles (fun h _ hv=>angular_extend h hv)
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
        apply runAngularAdd_cached
        apply (runtimeSequence_cached K AngularHandles (fun h _ hv=>angular_extend h hv)
          runtime current _ extension currentValid ?_ ?_).1
        · intro action member state
          obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
          obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
          exact runtimeWeighted_grows _ _ _ state
        · intro action member state extension2 paid
          obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
          obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
          exact runtimeWeighted_cached K _ _ _ state paid
            (series_getD (series_extend extension2 (setupValid.jclocks axis)) i)
            (series_getD (series_extend extension2 inputValid) j))
    exact ⟨result.1.cacheJ _ _ result.2,result.2⟩


theorem originalResolvent_cached (K : ℕ) (setup : RawSetup) (input : RawSeries)
    (runtime : RawRuntime) (valid : CachedNative K runtime) (setupValid : SetupHandles runtime setup) :
    CachedNative K (originalResolvent setup input runtime).2 ∧
      SeriesHandles (originalResolvent setup input runtime).2.arena (originalResolvent setup input runtime).1 := by
  dsimp only [originalResolvent]
  split
  · rename_i output found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ output found
    exact ⟨valid,equal ▸ valid.handles.resolvent entry member⟩
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
      (fun out=>RawExtends runtime.arena out.2.arena ∧ CachedNative K out.2 ∧ SeriesHandles out.2.arena out.1) (by
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
        have hg:=runtimeSequence_cached K AngularHandles (fun h _ hv=>angular_extend h hv)
          out.2 out.2 lower (RawExtends.refl _) paid.2.1 grows (by
            intro action member current extension currentValid
            obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
            obtain ⟨j,_,hj⟩:=List.mem_filterMap.mp hi
            split_ifs at hj
            cases hj
            exact runtimeWeighted_cached K _ _ _ current currentValid
              (series_getD (series_extend (paid.1.trans extension) setupValid.ellclock) i)
              (series_getD (series_extend extension paid.2.2) j))
        let summed:=runAngular (angularAdd generated.1) generated.2
        let negated:=runAngular (angularScale (polynomialCoefficient (-1)) summed.1) summed.2
        let residual:=runAngular (angularAdd [input.getD k [],negated.1]) negated.2
        let answer:=runAngular (angularScale (inversePoleCoefficient 0) residual.1) residual.2
        have hs:=runAngularAdd_cached generated.1 generated.2 hg.1
        have hn:=runAngularScale_cached (polynomialCoefficient (-1)) summed.1 summed.2 hs.1
        have hr:=runAngularAdd_cached [input.getD k [],negated.1] negated.2 hn.1
        have ha:=runAngularScale_cached (inversePoleCoefficient 0) residual.1 residual.2 hr.1
        have grow : RawExtends out.2.arena answer.2.arena :=
          ((((runtimeSequence_grows lower grows out.2).trans (angularAdd_grows _ _)).trans
            (angularScale_grows _ _ _)).trans (angularAdd_grows _ _)).trans (angularScale_grows _ _ _)
        exact ⟨paid.1.trans grow,ha.1,series_append_handles (series_extend grow paid.2.2) ha.2⟩)
      ([],runtime) ⟨RawExtends.refl _,valid,fun row member=>False.elim (List.not_mem_nil member)⟩
    exact ⟨result.2.1.cacheR _ _ result.2.2,result.2.2⟩


theorem originalWord_cached (K : ℕ) (setup : RawSetup) (tokens : List PreparationVacuumEngineSource.Token) (input : RawSeries)
    (runtime : RawRuntime) (valid : CachedNative K runtime) (setupValid : SetupHandles runtime setup)
    (inputValid : SeriesHandles runtime.arena input) :
    CachedNative K (originalWord setup tokens input runtime).2 ∧
      SeriesHandles (originalWord setup tokens input runtime).2.arena (originalWord setup tokens input runtime).1 := by
  classical
  dsimp only [originalWord]
  split
  · rename_i output found
    obtain ⟨entry,member,equal⟩:=memoLookup_member _ _ output found
    exact ⟨valid,equal ▸ valid.handles.word entry member⟩
  · let step:=fun (out : RawSeries × RawRuntime) (token : PreparationVacuumEngineSource.Token)=>
      match token with
      | .inverse=>originalResolvent setup out.1 out.2
      | .jordan a=>originalJS setup a out.1 out.2
    have result:=fold_invariant tokens.reverse step
      (fun out=>RawExtends runtime.arena out.2.arena ∧ CachedNative K out.2 ∧ SeriesHandles out.2.arena out.1) (by
        intro out paid token member
        cases token with
        | inverse=>exact ⟨paid.1.trans (originalResolvent_grows _ _ _),
            originalResolvent_cached K _ _ out.2 paid.2.1 (setupValid.extend paid.1)⟩
        | jordan a=>exact ⟨paid.1.trans (originalJS_grows _ _ _ _),
            originalJS_cached K _ _ _ out.2 paid.2.1 (setupValid.extend paid.1) paid.2.2⟩)
      (input,runtime) ⟨RawExtends.refl _,valid,inputValid⟩
    exact ⟨result.2.1.cacheWord _ _ result.2.2,result.2.2⟩



theorem originalApplyT_cached (K : ℕ) (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4))
    (runtime : RawRuntime) (valid : CachedNative K runtime) (setupValid : SetupHandles runtime setup)
    (inputValid : SeriesHandles runtime.arena input) :
    CachedNative K (originalApplyT setup a b input equation runtime).2 ∧
      ∀ id,id∈(originalApplyT setup a b input equation runtime).1 → Handle (originalApplyT setup a b input equation runtime).2.arena id := by
  let step:=fun (out : RawSeries × RawRuntime) (term : RawTemporalTerm)=>
    let operated:=originalWord setup term.tokens input out.2
    (List.range (setup.depth+1)).foldl (fun (acc : RawSeries × RawRuntime) k=>
      let scaled:=runAngular (angularScale (polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent)) acc.2
      let added:=runAngular (angularAdd [acc.1.getD k [],scaled.1]) scaled.2
      (acc.1.set k added.1,added.2)) (out.1,operated.2)
  have result:=fold_invariant (rawTemporalTable a b equation) step
    (fun out=>RawExtends runtime.arena out.2.arena ∧ CachedNative K out.2 ∧ SeriesHandles out.2.arena out.1) (by
      intro out paid term member
      let operated:=originalWord setup term.tokens input out.2
      have ho:=originalWord_cached K setup term.tokens input out.2 paid.2.1 (setupValid.extend paid.1)
        (series_extend paid.1 inputValid)
      have grow:=originalWord_grows setup term.tokens input out.2
      refine fold_invariant (List.range (setup.depth+1)) _
        (fun acc=>RawExtends runtime.arena acc.2.arena ∧ CachedNative K acc.2 ∧ SeriesHandles acc.2.arena acc.1) ?_
        (out.1,operated.2) ⟨paid.1.trans grow,ho.1,series_extend grow paid.2.2⟩
      intro acc current k member
      let scaled:=runAngular (angularScale (polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent)) acc.2
      let added:=runAngular (angularAdd [acc.1.getD k [],scaled.1]) scaled.2
      have hs:=runAngularScale_cached (polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent) acc.2 current.2.1
      have ha:=runAngularAdd_cached [acc.1.getD k [],scaled.1] scaled.2 hs.1
      have extension : RawExtends acc.2.arena added.2.arena := (angularScale_grows _ _ _).trans (angularAdd_grows _ _)
      exact ⟨current.1.trans extension,ha.1,series_set_handles (series_extend extension current.2.2) k added.1 ha.2⟩)
    (List.replicate (setup.depth+1) [],runtime) ⟨RawExtends.refl _,valid,by
      intro row member
      have same:row=[] := (List.mem_replicate.mp member).2
      subst row
      intro entry member;exact False.elim (List.not_mem_nil member)⟩
  apply runtimeSequence_cached K Handle (fun h _ hv=>handle_extend h hv) _ _ _ (RawExtends.refl _) result.2.1
  · intro action member current
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact angularAverage_grows _ _
  · intro action member current extension currentValid
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact runAverage_cached row current currentValid


theorem originalAffine_cached (K : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime)
    (valid : CachedNative K runtime) (setupValid : SetupHandles runtime setup) :
    CachedNative K (originalAffine setup equation runtime).2 ∧
      ∀ id,id∈(originalAffine setup equation runtime).1 → Handle (originalAffine setup equation runtime).2.arena id := by
  cases equation with
  | none=>
    let actions:=(List.finRange 4).map (fun a=>fun current=>
      let source:=runtimeSource setup.depth (Fin.castAdd 9 a) current
      originalJS setup a source.1 source.2)
    have affine:=runtimeSequence_cached K SeriesHandles (fun h _ hv=>series_extend h hv)
      runtime runtime actions (RawExtends.refl _) valid (by
        intro action member current
        obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
        exact (runtimeSource_grows _ _ current).trans
          (originalJS_grows setup a _ (runtimeSource setup.depth (Fin.castAdd 9 a) current).2)) (by
        intro action member current extension currentValid
        obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
        let source:=runtimeSource setup.depth (Fin.castAdd 9 a) current
        have hs:=runtimeSource_cached setup.depth (Fin.castAdd 9 a) current currentValid
        exact originalJS_cached K setup a source.1 source.2 hs.1
          (setupValid.extend (extension.trans (runtimeSource_grows _ _ current))) hs.2)
    apply runtimeSequence_cached K Handle (fun h _ hv=>handle_extend h hv) _ _ _ (RawExtends.refl _) affine.1
    · intro action member current
      obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
      exact rawAdd_extends _ _
    · intro action member current extension currentValid
      obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
      exact runAdd_cached _ current currentValid
  | some a=>
    have hs:=runtimeSource_cached setup.depth (Fin.castAdd 9 a) runtime valid
    apply runtimeSequence_cached K Handle (fun h _ hv=>handle_extend h hv) _ _ _ (RawExtends.refl _) hs.1
    · intro action member current
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact rawScale_extends _ _ _
    · intro action member current extension currentValid
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact runScale_cached _ _ current currentValid




theorem sourceTemporal_cached (K : ℕ) (setup : RawSetup) (slot : Fin 13) (a b : Fin 4) (equation : Option (Fin 4))
    (runtime : RawRuntime) (valid : CachedNative K runtime) (setupValid : SetupHandles runtime setup) :
    let source:=runtimeSource setup.depth slot runtime
    CachedNative K (originalApplyT setup a b source.1 equation source.2).2 ∧
      ListHandles (originalApplyT setup a b source.1 equation source.2).2.arena
        (originalApplyT setup a b source.1 equation source.2).1 := by
  let source:=runtimeSource setup.depth slot runtime
  have hs:=runtimeSource_cached setup.depth slot runtime valid
  exact originalApplyT_cached K setup a b source.1 equation source.2 hs.1
    (setupValid.extend (runtimeSource_grows setup.depth slot runtime)) hs.2


theorem originalForceOrEnergy_cached (K : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) (runtime : RawRuntime)
    (valid : CachedNative K runtime) (setupValid : SetupHandles runtime setup) :
    CachedNative K (originalForceOrEnergy setup equation runtime).2 ∧
      ListHandles (originalForceOrEnergy setup equation runtime).2.arena (originalForceOrEnergy setup equation runtime).1 := by
  let affine:=originalAffine setup equation runtime
  let trace:=runtimeTrace setup.depth affine.2
  let first:=originalApplyT setup 0 0 trace.1 equation trace.2
  have ha:=originalAffine_cached K setup equation runtime valid setupValid
  have ht:=runtimeTrace_cached setup.depth affine.2 ha.1
  have traceGrow : RawExtends runtime.arena trace.2.arena :=
    (originalAffine_grows setup equation runtime).trans (runtimeTrace_grows setup.depth affine.2)
  have hf:=originalApplyT_cached K setup 0 0 trace.1 equation trace.2 ht.1 (setupValid.extend traceGrow) ht.2
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
  have hd:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    runtime first.2 diagonalActions firstGrow hf.1 diagonalGrows (by
      intro action member current extension paid
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
      exact sourceTemporal_cached K setup ⟨4+i.val,by omega⟩ (Fin.succ i) (Fin.succ i) equation current paid
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
  have hc:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    runtime diagonal.2 crossActions diagonalGrow hd.1 crossGrows (by
      intro action member current extension paid
      obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
      exact sourceTemporal_cached K setup entry.2.2 entry.1 entry.2.1 equation current paid (setupValid.extend extension))
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
  have htime:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    runtime cross.2 timeActions crossGrow hc.1 timeGrows (by
      intro action member current extension paid
      obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
      exact sourceTemporal_cached K setup ⟨10+i.val,by omega⟩ 0 (Fin.succ i) equation current paid
        (setupValid.extend extension))
  apply runtimeSequence_cached K Handle (fun h _ hv=>handle_extend h hv) time.2 time.2 _ (RawExtends.refl _) htime.1
  · intro action member current
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    apply RawExtends.trans (runtimeSequence_grows _ ?_ current)
    · exact rawAdd_extends _ _
    · intro action member current
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact rawScale_extends _ _ _
  · intro action member current extension paid
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    apply runAdd_cached
    apply (runtimeSequence_cached K Handle (fun h _ hv=>handle_extend h hv) current current _ (RawExtends.refl _) paid ?_ ?_).1
    · intro action member state
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact rawScale_extends _ _ _
    · intro action member state grows valid
      obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
      exact runScale_cached _ _ state valid


theorem originalInstall_cached (K : ℕ) (k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (valid : CachedNative K runtime) (clocksValid : ClockHandles runtime.arena clocks) :
    let installed:=originalInstall k residualIds clocks runtime
    CachedNative K installed.2.2.2 ∧ ClockHandles installed.2.2.2.arena installed.1 ∧
      ListHandles installed.2.2.2.arena installed.2.1 ∧ ListHandles installed.2.2.2.arena installed.2.2.1 := by
  have result:=fold_invariant (List.finRange 4)
    (fun (out : RawClocks × List ℕ × List ℕ × RawRuntime) a=>
      let atom:=runArena (rawAtom (.clock k a) false) out.2.2.2
      let clocks:=clockInsert out.1 (k+1) a atom.1
      let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
        (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))) atom.2
      let definition:=runArena (rawAdd scaled.1) scaled.2
      (clocks,out.2.1++[atom.1],out.2.2.1++[definition.1],definition.2))
    (fun out=>CachedNative K out.2.2.2 ∧ ClockHandles out.2.2.2.arena out.1 ∧
      ListHandles out.2.2.2.arena out.2.1 ∧ ListHandles out.2.2.2.arena out.2.2.1) (by
      intro out paid a member
      let atom:=runArena (rawAtom (.clock k a) false) out.2.2.2
      let actions:=(List.finRange 4).map (fun b=>runArena
        (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))
      let scaled:=runtimeSequence actions atom.2
      let definition:=runArena (rawAdd scaled.1) scaled.2
      have hatom:=runAtom_cached (.clock k a) false out.2.2.2 paid.1 (by intro id member;cases member)
      have grows : ∀ action,action∈actions → RuntimeGrows action := by
        intro action member current
        obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
        exact rawScale_extends _ _ _
      have hscaled:=runtimeSequence_cached K Handle (fun h _ hv=>handle_extend h hv)
        atom.2 atom.2 actions (RawExtends.refl _) hatom.1 grows (by
          intro action member current extension currentValid
          obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
          exact runScale_cached _ _ current currentValid)
      have hdef:=runAdd_cached scaled.1 scaled.2 hscaled.1
      have tailGrow : RawExtends atom.2.arena definition.2.arena :=
        (runtimeSequence_grows actions grows atom.2).trans (rawAdd_extends _ _)
      have allGrow : RawExtends out.2.2.2.arena definition.2.arena := (rawAtom_extends _ _ _).trans tailGrow
      exact ⟨hdef.1,
        clockInsert_handles (clocks_extend allGrow paid.2.1) (k+1) a atom.1 (handle_extend tailGrow hatom.2),
        list_append_handle (list_extend allGrow paid.2.2.1) atom.1 (handle_extend tailGrow hatom.2),
        list_append_handle (list_extend allGrow paid.2.2.2) definition.1 hdef.2⟩)
    (clocks,[],[],runtime) ⟨valid,clocksValid,fun id member=>False.elim (List.not_mem_nil member),
      fun id member=>False.elim (List.not_mem_nil member)⟩
  exact result


theorem originalChecks_cached (K : ℕ) (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ)
    (runtime : RawRuntime) (valid : CachedNative K runtime) (setupValid : SetupHandles runtime setup) :
    CachedNative K (originalChecks setup order residualIds clockIds runtime).2.2 ∧
      ListHandles (originalChecks setup order residualIds clockIds runtime).2.2.arena
        (originalChecks setup order residualIds clockIds runtime).1 := by
  have result:=fold_invariant (List.finRange 4)
    (fun (out : List ℕ × List Bool × RawRuntime) a=>
      let result:=originalForceOrEnergy setup (some a) out.2.2
      let new:=result.1.getD order 0
      let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
        (rawScale (jacobianCoefficient a b) (clockIds.getD b.val 0)))) result.2
      let expected:=runArena (rawAdd ((residualIds.getD a.val 0)::scaled.1)) scaled.2
      (out.1++[new],out.2.1++[decide (new=expected.1)],expected.2))
    (fun out=>RawExtends runtime.arena out.2.2.arena ∧ CachedNative K out.2.2 ∧ ListHandles out.2.2.arena out.1) (by
      intro out paid a member
      let result:=originalForceOrEnergy setup (some a) out.2.2
      let actions:=(List.finRange 4).map (fun b=>runArena (rawScale (jacobianCoefficient a b) (clockIds.getD b.val 0)))
      let scaled:=runtimeSequence actions result.2
      let expected:=runArena (rawAdd ((residualIds.getD a.val 0)::scaled.1)) scaled.2
      have hf:=originalForceOrEnergy_cached K setup (some a) out.2.2 paid.2.1 (setupValid.extend paid.1)
      have grows : ∀ action,action∈actions → RuntimeGrows action := by
        intro action member current
        obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
        exact rawScale_extends _ _ _
      have hs:=runtimeSequence_cached K Handle (fun h _ hv=>handle_extend h hv)
        result.2 result.2 actions (RawExtends.refl _) hf.1 grows (by
          intro action member current extension currentValid
          obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
          exact runScale_cached _ _ current currentValid)
      have he:=runAdd_cached ((residualIds.getD a.val 0)::scaled.1) scaled.2 hs.1
      have tailGrow : RawExtends result.2.arena expected.2.arena :=
        (runtimeSequence_grows actions grows result.2).trans (rawAdd_extends _ _)
      have allGrow : RawExtends out.2.2.arena expected.2.arena := (originalForceOrEnergy_grows _ _ _).trans tailGrow
      exact ⟨paid.1.trans allGrow,he.1,list_append_handle (list_extend allGrow paid.2.2) (result.1.getD order 0)
        (handle_extend tailGrow (list_getD_handle hf.1.handles hf.2 order))⟩)
    ([],[],runtime) ⟨RawExtends.refl _,valid,fun id member=>False.elim (List.not_mem_nil member)⟩
  exact ⟨result.2.1,result.2.2⟩



theorem originalEngineNext_cached (K k : ℕ) (engine : RawEngineState)
    (valid : CachedNative K engine.runtime) (clockValid : ClockHandles engine.runtime.arena engine.clocks) :
    CachedNative K (originalEngineNext k engine).runtime := by
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))
  let residuals:=runtimeSequence actions before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  let checked:=originalChecks after.1 (k+1) residualIds installed.2.1 after.2
  have hb:=runtimeSetup_cached (k+1) engine.clocks engine.runtime valid clockValid
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  have hr:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    before.2 before.2 actions (RawExtends.refl _) hb.1 grows (by
      intro action member current extension currentValid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalForceOrEnergy_cached K before.1 (some a) current currentValid (hb.2.extend extension))
  have residualGrow : RawExtends engine.runtime.arena residuals.2.arena :=
    (runtimeSetup_grows _ _ _).trans (runtimeSequence_grows actions grows before.2)
  have hi:=originalInstall_cached K k residualIds engine.clocks residuals.2 hr.1 (clocks_extend residualGrow clockValid)
  have ha:=runtimeSetup_cached (k+1) installed.1 installed.2.2.2 hi.1 hi.2.1
  have hc:=originalChecks_cached K after.1 (k+1) residualIds installed.2.1 after.2 ha.1 ha.2
  exact (originalForceOrEnergy_cached K after.1 none checked.2.2 hc.1
    (ha.2.extend (originalChecks_grows _ _ _ _ _))).1

attribute [local irreducible] originalForceOrEnergy runtimeSequence runtimeSetup
set_option backward.isDefEq.respectTransparency true

theorem originalBoot_cached (K : ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (valid : CachedNative K runtime) (clockValid : ClockHandles runtime.arena clocks) :
    CachedNative K (originalBoot clocks runtime).runtime := by
  let setup:=runtimeSetup 0 clocks runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy setup.1 (some a))
  let forces:=runtimeSequence actions setup.2
  have hs:=runtimeSetup_cached 0 clocks runtime valid clockValid
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  have hf:=runtimeSequence_cached K ListHandles (fun h _ hv=>list_extend h hv)
    setup.2 setup.2 actions (RawExtends.refl _) hs.1 grows (by
      intro action member current extension currentValid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalForceOrEnergy_cached K setup.1 (some a) current currentValid (hs.2.extend extension))
  change CachedNative K (originalForceOrEnergy setup.1 none forces.2).2
  exact (originalForceOrEnergy_cached K setup.1 none forces.2 hf.1
    (hs.2.extend (runtimeSequence_grows actions grows setup.2))).1

theorem originalEngineInitial_cached (K : ℕ) : CachedNative K originalEngineInitial.runtime := by
  let seeded:=runArena (rawScalar (polynomialCoefficient (MvPolynomial.X 0))) ⟨rawInitial,[],[],[],[]⟩
  have source:=runScalar_cached (polynomialCoefficient (MvPolynomial.X 0)) _ (initial_cachedNative K)
  apply originalBoot_cached K _ seeded.2 source.1
  intro entry member
  have equal:=List.mem_singleton.mp member
  subst entry
  exact source.2

theorem originalEngine_cached (K order : ℕ) : CachedNative K (originalEngine order).runtime := by
  induction order with
  | zero=>exact originalEngineInitial_cached K
  | succ k ih=>exact originalEngineNext_cached K k (originalEngine k) ih (originalEngine_handles k).clocks

theorem actual_memo_entry_native (order : ℕ) (entry : (ℕ × ℕ × ℕ) × ℕ)
    (member : entry∈(originalEngine order).runtime.moyalMemo) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial order (originalEngine order).runtime.arena entry.2 x=
      complexMoyal entry.1.1 (nativePolynomial order (originalEngine order).runtime.arena entry.1.2.1)
        (nativePolynomial order (originalEngine order).runtime.arena entry.1.2.2) x :=
  ((originalEngine_cached order order).moyal entry member).2.2 x hx

theorem actual_memoMoyal_generated (order r : ℕ)
    (left right : Fin (originalEngine order).runtime.arena.polynomials.length) :
    CachedNative order (memoMoyal r left.val right.val (originalEngine order).runtime).2 ∧
      Handle (memoMoyal r left.val right.val (originalEngine order).runtime).2.arena
        (memoMoyal r left.val right.val (originalEngine order).runtime).1 ∧
      ∀ x,x∈poleDomain → nativePolynomial order
        (memoMoyal r left.val right.val (originalEngine order).runtime).2.arena
        (memoMoyal r left.val right.val (originalEngine order).runtime).1 x=
        complexMoyal r (nativePolynomial order (originalEngine order).runtime.arena left.val)
          (nativePolynomial order (originalEngine order).runtime.arena right.val) x :=
  memoMoyal_native order r left.val right.val (originalEngine order).runtime
    (originalEngine_cached order order) left.isLt right.isLt

theorem actual_memoMoyal_all_jets (order r : ℕ)
    (left right : Fin (originalEngine order).runtime.arena.polynomials.length)
    (x : Phase) (hx : x∈poleDomain) (directions : List Phase) :
    complexListJet directions
      (nativePolynomial order (memoMoyal r left.val right.val (originalEngine order).runtime).2.arena
        (memoMoyal r left.val right.val (originalEngine order).runtime).1) x=
      complexListJet directions (complexMoyal r
        (nativePolynomial order (originalEngine order).runtime.arena left.val)
        (nativePolynomial order (originalEngine order).runtime.arena right.val)) x := by
  have germ : nativePolynomial order (memoMoyal r left.val right.val (originalEngine order).runtime).2.arena
      (memoMoyal r left.val right.val (originalEngine order).runtime).1=ᶠ[𝓝 x]
      complexMoyal r (nativePolynomial order (originalEngine order).runtime.arena left.val)
        (nativePolynomial order (originalEngine order).runtime.arena right.val) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with y hy
    exact (actual_memoMoyal_generated order r left right).2.2 y hy
  exact (complexListJet_germ germ directions).eq_of_nhds

theorem actual_memoJordan_generated (order r : ℕ)
    (left right : Fin (originalEngine order).runtime.arena.polynomials.length) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial order (memoJordan r left.val right.val (originalEngine order).runtime).2.arena
      (memoJordan r left.val right.val (originalEngine order).runtime).1 x=
      (1/2 : ℂ)*(complexMoyal r (nativePolynomial order (originalEngine order).runtime.arena left.val)
        (nativePolynomial order (originalEngine order).runtime.arena right.val) x+
        complexMoyal r (nativePolynomial order (originalEngine order).runtime.arena right.val)
          (nativePolynomial order (originalEngine order).runtime.arena left.val) x) :=
  (memoJordan_native order r left.val right.val (originalEngine order).runtime
    (originalEngine_cached order order) left.isLt right.isLt).2.2 x hx

end LowEnergy.PreparationVacuumNativeMemo

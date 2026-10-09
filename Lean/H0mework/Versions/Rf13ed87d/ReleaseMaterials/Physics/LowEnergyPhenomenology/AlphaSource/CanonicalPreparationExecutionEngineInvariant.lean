import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationExecutionRuntimeInvariant

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumExecutionGraph
open PreparationVacuumSharedPool PreparationVacuumDAGCoefficient

def ClockHandles (state : RawArena) (clocks : RawClocks) : Prop :=
  ∀ entry,entry∈clocks → Handle state entry.2

def StageHandles (state : RawArena) (stage : RawStageRecord) : Prop :=
  ListHandles state stage.residuals ∧ ListHandles state stage.correctedForces ∧
  ListHandles state stage.clockAtoms ∧ ListHandles state stage.clockDefinitions ∧ Handle state stage.energy

structure EngineHandles (engine : RawEngineState) : Prop where
  runtime : RuntimeHandles engine.runtime
  clocks : ClockHandles engine.runtime.arena engine.clocks
  definitions : ClockHandles engine.runtime.arena engine.definitions
  leading : Handle engine.runtime.arena engine.leadingEnergy
  stages : ∀ stage,stage∈engine.stages → StageHandles engine.runtime.arena stage

theorem clocks_extend {old next : RawArena} (extension : RawExtends old next) {clocks : RawClocks}
    (valid : ClockHandles old clocks) : ClockHandles next clocks :=
  fun entry member=>handle_extend extension (valid entry member)

theorem stages_extend {old next : RawArena} (extension : RawExtends old next) {stage : RawStageRecord}
    (valid : StageHandles old stage) : StageHandles next stage :=
  ⟨list_extend extension valid.1,list_extend extension valid.2.1,list_extend extension valid.2.2.1,
    list_extend extension valid.2.2.2.1,handle_extend extension valid.2.2.2.2⟩

theorem clockInsert_handles {state : RawArena} {clocks : RawClocks} (valid : ClockHandles state clocks)
    (level : ℕ) (axis : Fin 4) (id : ℕ) (bound : Handle state id) : ClockHandles state (clockInsert clocks level axis id) := by
  intro entry member
  rcases List.mem_cons.mp member with same|old
  · subst entry;exact bound
  · exact valid entry (List.mem_filter.mp old).1

theorem list_getD_handle {runtime : RawRuntime} (valid : RuntimeHandles runtime) {ids : List ℕ}
    (handles : ListHandles runtime.arena ids) (index : ℕ) : Handle runtime.arena (ids.getD index 0) := by
  by_cases inside : index < ids.length
  · rw [List.getD_eq_getElem _ _ inside]
    exact handles _ (List.getElem_mem _)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact zero_handle valid

theorem list_append_handle {state : RawArena} {ids : List ℕ} (valid : ListHandles state ids)
    (id : ℕ) (bound : Handle state id) : ListHandles state (ids++[id]) := by
  intro value member
  rcases List.mem_append.mp member with old|fresh
  · exact valid value old
  · have equal:=List.mem_singleton.mp fresh
    subst value;exact bound

theorem originalInstall_handles (k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (valid : RuntimeHandles runtime) (clocksValid : ClockHandles runtime.arena clocks) :
    let installed:=originalInstall k residualIds clocks runtime
    RuntimeHandles installed.2.2.2 ∧ ClockHandles installed.2.2.2.arena installed.1 ∧
      ListHandles installed.2.2.2.arena installed.2.1 ∧ ListHandles installed.2.2.2.arena installed.2.2.1 := by
  have result:=fold_invariant (List.finRange 4)
    (fun (out : RawClocks × List ℕ × List ℕ × RawRuntime) a=>
      let atom:=runArena (rawAtom (.clock k a) false) out.2.2.2
      let clocks:=clockInsert out.1 (k+1) a atom.1
      let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
        (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))) atom.2
      let definition:=runArena (rawAdd scaled.1) scaled.2
      (clocks,out.2.1++[atom.1],out.2.2.1++[definition.1],definition.2))
    (fun out=>RuntimeHandles out.2.2.2 ∧ ClockHandles out.2.2.2.arena out.1 ∧
      ListHandles out.2.2.2.arena out.2.1 ∧ ListHandles out.2.2.2.arena out.2.2.1) (by
      intro out paid a member
      let atom:=runArena (rawAtom (.clock k a) false) out.2.2.2
      let actions:=(List.finRange 4).map (fun b=>runArena
        (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))
      let scaled:=runtimeSequence actions atom.2
      let definition:=runArena (rawAdd scaled.1) scaled.2
      have hatom:=runAtom_handles (.clock k a) false out.2.2.2 paid.1 (by intro id member;cases member)
      have grows : ∀ action,action∈actions → RuntimeGrows action := by
        intro action member current
        obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
        exact rawScale_extends _ _ _
      have hscaled:=runtimeSequence_handles Handle (fun h _ hv=>handle_extend h hv)
        atom.2 atom.2 actions (RawExtends.refl _) hatom.1 grows (by
          intro action member current extension currentValid
          obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
          exact runScale_handles _ _ current currentValid)
      have hdef:=runAdd_handles scaled.1 scaled.2 hscaled.1
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

theorem originalChecks_handles (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ)
    (runtime : RawRuntime) (valid : RuntimeHandles runtime) (setupValid : SetupHandles runtime setup) :
    RuntimeHandles (originalChecks setup order residualIds clockIds runtime).2.2 ∧
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
    (fun out=>RawExtends runtime.arena out.2.2.arena ∧ RuntimeHandles out.2.2 ∧ ListHandles out.2.2.arena out.1) (by
      intro out paid a member
      let result:=originalForceOrEnergy setup (some a) out.2.2
      let actions:=(List.finRange 4).map (fun b=>runArena (rawScale (jacobianCoefficient a b) (clockIds.getD b.val 0)))
      let scaled:=runtimeSequence actions result.2
      let expected:=runArena (rawAdd ((residualIds.getD a.val 0)::scaled.1)) scaled.2
      have hf:=originalForceOrEnergy_handles setup (some a) out.2.2 paid.2.1 (setupValid.extend paid.1)
      have grows : ∀ action,action∈actions → RuntimeGrows action := by
        intro action member current
        obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
        exact rawScale_extends _ _ _
      have hs:=runtimeSequence_handles Handle (fun h _ hv=>handle_extend h hv)
        result.2 result.2 actions (RawExtends.refl _) hf.1 grows (by
          intro action member current extension currentValid
          obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
          exact runScale_handles _ _ current currentValid)
      have he:=runAdd_handles ((residualIds.getD a.val 0)::scaled.1) scaled.2 hs.1
      have tailGrow : RawExtends result.2.arena expected.2.arena :=
        (runtimeSequence_grows actions grows result.2).trans (rawAdd_extends _ _)
      have allGrow : RawExtends out.2.2.arena expected.2.arena := (originalForceOrEnergy_grows _ _ _).trans tailGrow
      exact ⟨paid.1.trans allGrow,he.1,list_append_handle (list_extend allGrow paid.2.2) (result.1.getD order 0)
        (handle_extend tailGrow (list_getD_handle hf.1 hf.2 order))⟩)
    ([],[],runtime) ⟨RawExtends.refl _,valid,fun id member=>False.elim (List.not_mem_nil member)⟩
  exact ⟨result.2.1,result.2.2⟩


theorem originalEngineNext_handles (k : ℕ) (engine : RawEngineState) (valid : EngineHandles engine) :
    EngineHandles (originalEngineNext k engine) := by
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))
  let residuals:=runtimeSequence actions before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  let checked:=originalChecks after.1 (k+1) residualIds installed.2.1 after.2
  let energy:=originalForceOrEnergy after.1 none checked.2.2
  have hb:=runtimeSetup_handles (k+1) engine.clocks engine.runtime valid.runtime valid.clocks
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  have hr:=runtimeSequence_handles ListHandles (fun h _ hv=>list_extend h hv)
    before.2 before.2 actions (RawExtends.refl _) hb.1 grows (by
      intro action member current extension currentValid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalForceOrEnergy_handles before.1 (some a) current currentValid (hb.2.extend extension))
  have residualGrow : RawExtends engine.runtime.arena residuals.2.arena :=
    (runtimeSetup_grows _ _ _).trans (runtimeSequence_grows actions grows before.2)
  have residualValid : ListHandles residuals.2.arena residualIds := by
    intro id member
    obtain ⟨row,rowMember,rfl⟩:=List.mem_map.mp member
    exact list_getD_handle hr.1 (hr.2 row rowMember) (k+1)
  have hi:=originalInstall_handles k residualIds engine.clocks residuals.2 hr.1 (clocks_extend residualGrow valid.clocks)
  have ha:=runtimeSetup_handles (k+1) installed.1 installed.2.2.2 hi.1 hi.2.1
  have hc:=originalChecks_handles after.1 (k+1) residualIds installed.2.1 after.2 ha.1 ha.2
  have he:=originalForceOrEnergy_handles after.1 none checked.2.2 hc.1
    (ha.2.extend (originalChecks_grows _ _ _ _ _))
  have energyGrow : RawExtends checked.2.2.arena energy.2.arena := originalForceOrEnergy_grows _ _ _
  have afterGrow : RawExtends after.2.arena energy.2.arena := (originalChecks_grows _ _ _ _ _).trans energyGrow
  have installGrow : RawExtends installed.2.2.2.arena energy.2.arena := (runtimeSetup_grows _ _ _).trans afterGrow
  have residualTail : RawExtends residuals.2.arena energy.2.arena := (originalInstall_grows _ _ _ _).trans installGrow
  have allGrow : RawExtends engine.runtime.arena energy.2.arena := residualGrow.trans residualTail
  have definitionHandles : ListHandles energy.2.arena installed.2.2.1 := list_extend installGrow hi.2.2.2
  have definitions:=fold_invariant (List.finRange 4)
    (fun defs a=>clockInsert defs (k+1) a (installed.2.2.1.getD a.val 0))
    (ClockHandles energy.2.arena) (by
      intro defs paid a member
      exact clockInsert_handles paid (k+1) a _ (list_getD_handle he.1 definitionHandles a.val))
    engine.definitions (clocks_extend allGrow valid.definitions)
  refine ⟨he.1,clocks_extend installGrow hi.2.1,definitions,handle_extend allGrow valid.leading,?_⟩
  intro stage member
  rcases List.mem_append.mp member with old|new
  · exact stages_extend allGrow (valid.stages stage old)
  · have equal:=List.mem_singleton.mp new
    subst stage
    exact ⟨list_extend residualTail residualValid,list_extend energyGrow hc.2,list_extend installGrow hi.2.2.1,
      definitionHandles,list_getD_handle he.1 he.2 (k+1)⟩

attribute [local irreducible] originalForceOrEnergy runtimeSequence runtimeSetup
set_option backward.isDefEq.respectTransparency true

theorem originalBoot_handles (clocks : RawClocks) (runtime : RawRuntime) (valid : RuntimeHandles runtime)
    (clockValid : ClockHandles runtime.arena clocks) : EngineHandles (originalBoot clocks runtime) := by
  let setup:=runtimeSetup 0 clocks runtime
  let actions:=(List.finRange 4).map (fun a=>originalForceOrEnergy setup.1 (some a))
  let forces:=runtimeSequence actions setup.2
  let leading:=originalForceOrEnergy setup.1 none forces.2
  have hs:=runtimeSetup_handles 0 clocks runtime valid clockValid
  have grows : ∀ action,action∈actions → RuntimeGrows action := by
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  have hf:=runtimeSequence_handles ListHandles (fun h _ hv=>list_extend h hv)
    setup.2 setup.2 actions (RawExtends.refl _) hs.1 grows (by
      intro action member current extension currentValid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalForceOrEnergy_handles setup.1 (some a) current currentValid (hs.2.extend extension))
  have hleading:=originalForceOrEnergy_handles setup.1 none forces.2 hf.1
    (hs.2.extend (runtimeSequence_grows actions grows setup.2))
  have grow : RawExtends runtime.arena leading.2.arena :=
    ((runtimeSetup_grows 0 clocks runtime).trans (runtimeSequence_grows actions grows setup.2)).trans
      (originalForceOrEnergy_grows setup.1 none forces.2)
  refine ⟨hleading.1,clocks_extend grow clockValid,?_,list_getD_handle hleading.1 hleading.2 0,?_⟩
  all_goals intro value member;exact False.elim (List.not_mem_nil member)

theorem originalEngineInitial_handles : EngineHandles originalEngineInitial := by
  let seeded:=runArena (rawScalar (polynomialCoefficient (MvPolynomial.X 0))) ⟨rawInitial,[],[],[],[]⟩
  have hs:=runScalar_handles (polynomialCoefficient (MvPolynomial.X 0)) _ initial_handles
  apply originalBoot_handles _ seeded.2 hs.1
  intro entry member
  have equal:=List.mem_singleton.mp member
  subst entry
  exact hs.2

theorem originalEngine_handles (order : ℕ) : EngineHandles (originalEngine order) := by
  induction order with
  | zero=>exact originalEngineInitial_handles
  | succ k ih=>exact originalEngineNext_handles k (originalEngine k) ih

theorem originalEngine_graph_closed (order : ℕ) : RawMoyalClosed (originalEngine order).runtime.arena :=
  (originalEngine_handles order).runtime.closed

theorem originalStageRecord_handles (k : ℕ) : StageHandles (originalEngine (k+1)).runtime.arena (originalStageRecord k) :=
  (originalEngine_handles (k+1)).stages _ (List.getElem_mem _)

theorem originalFive_handle (k : ℕ) (i : Fin 5) : Handle (originalEngine (k+1)).runtime.arena (originalFiveId k i) := by
  refine Fin.lastCases ?_ (fun a=>?_) i
  · rw [originalFive_energy]
    exact (originalStageRecord_handles k).2.2.2.2
  · rw [originalFive_clock_definition]
    exact list_getD_handle (originalEngine_handles (k+1)).runtime (originalStageRecord_handles k).2.2.2.1 a.val

theorem originalFiveRows_preserved (k later : ℕ) (h : k+1 ≤ later) (i : Fin 5) :
    rawRows (originalEngine later).runtime.arena (originalFiveId k i)=originalFiveRows k i :=
  originalFiveRows_at_later k later h i (originalFive_handle k i)

-- This is a generated finite table readback, with no input graph certificate.
def originalFiveExpression (k : ℕ) (i : Fin 5) : PreparationVacuumDAGSemantic.ArenaExpression (k+1) :=
  rawExpand (k+1) (originalEngine (k+1)).runtime.arena.polynomials.length
    (originalEngine (k+1)).runtime.arena (originalFiveId k i)

theorem originalFiveExpression_equation (k : ℕ) (i : Fin 5) :
    originalFiveExpression k i=rawExpandStep (k+1) (originalEngine (k+1)).runtime.arena
      (rawExpand (k+1) (originalEngine (k+1)).runtime.arena.polynomials.length (originalEngine (k+1)).runtime.arena)
      (originalFiveId k i) :=
  rawExpand_equation (k+1) _ (originalEngine_graph_closed (k+1)) _ (originalFive_handle k i)


set_option backward.isDefEq.respectTransparency false
attribute [local semireducible] runtimeSequence runtimeSetup originalForceOrEnergy

def KindClockBelow (limit : ℕ) : RawKind → Prop
  | .clock level _=>level < limit
  | _=>True

def ClockRange (limit : ℕ) (state : RawArena) : Prop :=
  ∀ node,node∈state.nodes → KindClockBelow limit node.kind

theorem clockRange_mono {small large : ℕ} (h : small ≤ large) {state : RawArena}
    (valid : ClockRange small state) : ClockRange large state := by
  intro node member
  have hn:=valid node member
  cases equation : node.kind <;> simp only [equation,KindClockBelow] at hn ⊢
  exact lt_of_lt_of_le hn h

theorem rawPoly_clockRange (limit : ℕ) (rows : List RawRow) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (rawPoly rows state).2 := valid

theorem rawScalar_clockRange (limit : ℕ) (c : NormalizedCoefficient) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (rawScalar c state).2 := valid

theorem rawAdd_clockRange (limit : ℕ) (ids : List ℕ) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (rawAdd ids state).2 := valid

theorem rawScale_clockRange (limit : ℕ) (c : NormalizedCoefficient) (id : ℕ) (state : RawArena)
    (valid : ClockRange limit state) : ClockRange limit (rawScale c id state).2 := valid

theorem rawMultiply_clockRange (limit : ℕ) (left right : ℕ) (state : RawArena)
    (valid : ClockRange limit state) : ClockRange limit (rawMultiply left right state).2 := valid

theorem rawStrip_clockRange (limit : ℕ) (id : ℕ) (row : RawRow) (state : RawArena)
    (valid : ClockRange limit state) : ClockRange limit (rawStrip id row state).2 := by
  intro node member
  rw [rawStrip_nodes] at member
  exact valid node member

theorem rawAtom_clockRange (limit : ℕ) (kind : RawKind) (central : Bool) (state : RawArena)
    (valid : ClockRange limit state) (allowed : KindClockBelow limit kind) : ClockRange limit (rawAtom kind central state).2 := by
  classical
  intro node member
  change node∈PreparationVacuumSourceSerialization.intern ⟨kind,central⟩ state.nodes at member
  unfold PreparationVacuumSourceSerialization.intern at member
  split_ifs at member
  · exact valid node member
  · rcases List.mem_append.mp member with old|fresh
    · exact valid node old
    · have same:=List.mem_singleton.mp fresh
      subst node;exact allowed

theorem rawPair_clockRange (limit r left right : ℕ) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (rawPair r left right state).2 := by
  have stripped:=rawStrip_clockRange limit right ((rawRows state right).getD 0 ⟨polynomialCoefficient 0,[]⟩)
    _ (rawStrip_clockRange limit left ((rawRows state left).getD 0 ⟨polynomialCoefficient 0,[]⟩) state valid)
  dsimp only [rawPair]
  split_ifs
  all_goals first
    | exact stripped
    | exact rawScale_clockRange _ _ _ _ (rawAtom_clockRange _ _ _ _ stripped trivial)

abbrev RuntimeClockRange (limit : ℕ) (runtime : RawRuntime) : Prop := ClockRange limit runtime.arena

def RangeAction {α : Type} (limit : ℕ) (action : RuntimeAction α) : Prop :=
  ∀ runtime,RuntimeClockRange limit runtime → RuntimeClockRange limit (action runtime).2

theorem runtimeSequence_clockRange {α : Type} (limit : ℕ) (actions : List (RuntimeAction α))
    (preserves : ∀ action,action∈actions → RangeAction limit action) : RangeAction limit (runtimeSequence actions) := by
  intro runtime valid
  induction actions generalizing runtime with
  | nil=>exact valid
  | cons action actions ih=>
    exact ih (fun a h=>preserves a (List.mem_cons_of_mem _ h)) (action runtime).2
      (preserves action (by simp) runtime valid)

theorem memoPair_clockRange (limit r left right : ℕ) : RangeAction limit (memoPair r left right) := by
  intro runtime valid
  dsimp only [memoPair]
  split
  · exact valid
  · dsimp only [cacheMoyalResult]
    split_ifs
    · exact valid
    · exact rawPair_clockRange _ _ _ _ _ valid

theorem memoMoyal_clockRange (limit r left right : ℕ) : RangeAction limit (memoMoyal r left right) := by
  intro runtime valid
  dsimp only [memoMoyal]
  split
  · exact valid
  · dsimp only [cacheMoyalResult]
    split_ifs
    · exact valid
    · exact valid
    · apply runtimeSequence_clockRange limit _ ?_ runtime valid
      intro action member current paid
      obtain ⟨a,_,ha⟩:=List.mem_flatMap.mp member
      obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
      exact memoPair_clockRange limit r _ _ _ paid
    · exact rawPair_clockRange _ _ _ _ _ valid

theorem memoJordan_clockRange (limit r left right : ℕ) : RangeAction limit (memoJordan r left right) := by
  intro runtime valid
  exact memoMoyal_clockRange limit r right left _ (memoMoyal_clockRange limit r left right runtime valid)

theorem angularAdd_clockRange (limit : ℕ) (inputs : List RawAngular) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (angularAdd inputs state).2 := by
  refine fold_invariant inputs.flatten _ (fun out : RawAngular × RawArena=>ClockRange limit out.2)
    ?_ ([],state) valid
  intro out paid row member
  exact paid

theorem angularScale_clockRange (limit : ℕ) (c : NormalizedCoefficient) (input : RawAngular)
    (state : RawArena) (valid : ClockRange limit state) : ClockRange limit (angularScale c input state).2 := by
  apply fold_invariant input _ (fun out : RawAngular × RawArena=>ClockRange limit out.2) ?_ ([],state) valid
  intro out paid row member
  dsimp only
  split_ifs <;> exact paid

theorem angularSequence_clockRange (limit : ℕ) (actions : List AngularAction)
    (preserves : ∀ action,action∈actions → ∀ state,ClockRange limit state → ClockRange limit (action state).2)
    (state : RawArena) (valid : ClockRange limit state) : ClockRange limit (angularSequence actions state).2 := by
  induction actions generalizing state with
  | nil=>exact valid
  | cons action actions ih=>exact ih (fun a h=>preserves a (List.mem_cons_of_mem _ h)) _ (preserves action (by simp) state valid)

theorem rawSequence_clockRange (limit : ℕ) (actions : List RawAction)
    (preserves : ∀ action,action∈actions → ∀ state,ClockRange limit state → ClockRange limit (action state).2)
    (state : RawArena) (valid : ClockRange limit state) : ClockRange limit (rawSequence actions state).2 := by
  induction actions generalizing state with
  | nil=>exact valid
  | cons action actions ih=>exact ih (fun a h=>preserves a (List.mem_cons_of_mem _ h)) _ (preserves action (by simp) state valid)

theorem angularAverage_clockRange (limit : ℕ) (input : RawAngular) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (angularAverage input state).2 := by
  apply rawSequence_clockRange limit _ ?_ state valid
  intro action member current paid
  obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
  exact paid

theorem runtimeWeighted_clockRange (limit r : ℕ) (left right : RawAngular) : RangeAction limit (runtimeWeighted r left right) := by
  intro runtime valid
  refine fold_invariant _ _ (fun out : RawAngular × RawRuntime=>RuntimeClockRange limit out.2)
    ?_ ([],runtime) valid
  intro out paid pair member
  exact memoJordan_clockRange limit r pair.1.2 pair.2.2 out.2 paid

theorem originalSource_clockRange (limit depth : ℕ) (slot : Fin 13) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (originalSource depth slot state).2 := by
  let principal:=if slot.val=0 ∨ (4 ≤ slot.val ∧ slot.val ≤ 9) then rawScalar (principalCoefficient slot) state else (0,state)
  have hp : ClockRange limit principal.2 := by dsimp only [principal];split_ifs <;> exact valid
  let first:=rawAtom (.source 1 slot.castSucc) false principal.2
  let lower:=rawAtom (.source 0 slot.castSucc) false first.2
  have hl : ClockRange limit lower.2 :=
    rawAtom_clockRange limit (.source 0 slot.castSucc) false first.2
      (rawAtom_clockRange limit (.source 1 slot.castSucc) false principal.2 hp trivial) trivial
  change ClockRange limit (if slot=0 then
    let extra:=rawAtom (.source 0 (Fin.last 13)) false lower.2
    rawAdd [lower.1,extra.1] extra.2 else lower).2
  split_ifs
  · exact rawAtom_clockRange limit (.source 0 (Fin.last 13)) false lower.2 hl trivial
  · exact hl

theorem originalTrace_clockRange (limit depth : ℕ) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (originalTrace depth state).2 := by
  apply angularSequence_clockRange limit _ ?_ _
    (originalSource_clockRange _ _ _ _ (originalSource_clockRange _ _ _ _ (originalSource_clockRange _ _ _ _ valid)))
  intro action member current paid
  obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
  exact angularAdd_clockRange _ _ _ paid

theorem originalSetup_clockRange (limit depth : ℕ) (clocks : RawClocks) (state : RawArena) (valid : ClockRange limit state) :
    ClockRange limit (originalSetup depth clocks state).2 := by
  apply angularSequence_clockRange limit _ ?_ state valid
  intro action member current paid
  obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
  exact angularAdd_clockRange _ _ _ paid

theorem runtimeSetup_clockRange (limit depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (valid : RuntimeClockRange limit runtime) : RuntimeClockRange limit (runtimeSetup depth clocks runtime).2 := by
  unfold runtimeSetup
  exact originalSetup_clockRange limit depth clocks runtime.arena valid


theorem originalJS_clockRange (limit : ℕ) (setup : RawSetup) (axis : Fin 4) (input : RawSeries) :
    RangeAction limit (originalJS setup axis input) := by
  intro runtime valid
  dsimp only [originalJS]
  split
  · exact valid
  · apply runtimeSequence_clockRange limit _ ?_ runtime valid
    intro action member current paid
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    apply angularAdd_clockRange
    apply runtimeSequence_clockRange limit _ ?_ current paid
    intro action member current paid
    obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
    obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
    exact runtimeWeighted_clockRange _ _ _ _ current paid

theorem originalResolvent_clockRange (limit : ℕ) (setup : RawSetup) (input : RawSeries) :
    RangeAction limit (originalResolvent setup input) := by
  intro runtime valid
  dsimp only [originalResolvent]
  split
  · exact valid
  · refine fold_invariant _ _ (fun out : RawSeries × RawRuntime=>RuntimeClockRange limit out.2) ?_ ([],runtime) valid
    intro out paid k member
    apply angularScale_clockRange
    apply angularAdd_clockRange
    apply angularScale_clockRange
    apply angularAdd_clockRange
    apply runtimeSequence_clockRange limit _ ?_ out.2 paid
    intro action member current paid
    obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
    obtain ⟨j,_,hj⟩:=List.mem_filterMap.mp hi
    split_ifs at hj
    cases hj
    exact runtimeWeighted_clockRange _ _ _ _ current paid

theorem originalWord_clockRange (limit : ℕ) (setup : RawSetup)
    (tokens : List PreparationVacuumEngineSource.Token) (input : RawSeries) : RangeAction limit (originalWord setup tokens input) := by
  intro runtime valid
  dsimp only [originalWord]
  split
  · exact valid
  · refine fold_invariant _ _ (fun out : RawSeries × RawRuntime=>RuntimeClockRange limit out.2) ?_ (input,runtime) valid
    intro out paid token member
    cases token with
    | inverse=>exact originalResolvent_clockRange _ _ _ _ paid
    | jordan a=>exact originalJS_clockRange _ _ _ _ _ paid

theorem originalApplyT_clockRange (limit : ℕ) (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4)) :
    RangeAction limit (originalApplyT setup a b input equation) := by
  intro runtime valid
  unfold originalApplyT
  refine runtimeSequence_clockRange limit _ ?_ _ ?_
  · intro action member current paid
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact angularAverage_clockRange _ _ _ paid
  · refine fold_invariant _ _ (fun out : RawSeries × RawRuntime=>RuntimeClockRange limit out.2) ?_
      (List.replicate (setup.depth+1) [],runtime) valid
    intro out paid term member
    refine fold_invariant _ _ (fun acc : RawSeries × RawRuntime=>RuntimeClockRange limit acc.2) ?_
      (out.1,(originalWord setup term.tokens input out.2).2) (originalWord_clockRange _ _ _ _ _ paid)
    intro acc current k member
    exact angularAdd_clockRange _ _ _ (angularScale_clockRange _ _ _ _ current)

theorem originalAffine_clockRange (limit : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) :
    RangeAction limit (originalAffine setup equation) := by
  intro runtime valid
  cases equation with
  | none=>
    refine runtimeSequence_clockRange limit _ ?_ _ ?_
    · intro action member current paid
      obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
      exact paid
    · apply runtimeSequence_clockRange limit _ ?_ runtime valid
      intro action member current paid
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact originalJS_clockRange limit setup a (runtimeSource setup.depth (Fin.castAdd 9 a) current).1
        (runtimeSource setup.depth (Fin.castAdd 9 a) current).2
        (originalSource_clockRange limit setup.depth (Fin.castAdd 9 a) current.arena paid)
  | some a=>
    apply runtimeSequence_clockRange limit _ ?_ (runtimeSource setup.depth (Fin.castAdd 9 a) runtime).2
      (originalSource_clockRange limit setup.depth (Fin.castAdd 9 a) runtime.arena valid)
    intro action member current paid
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact paid

theorem sourceTemporal_clockRange (limit : ℕ) (setup : RawSetup) (slot : Fin 13) (a b : Fin 4)
    (equation : Option (Fin 4)) : RangeAction limit (fun runtime=>
      let source:=runtimeSource setup.depth slot runtime
      originalApplyT setup a b source.1 equation source.2) := by
  intro runtime valid
  exact originalApplyT_clockRange limit setup a b (runtimeSource setup.depth slot runtime).1 equation
    (runtimeSource setup.depth slot runtime).2 (originalSource_clockRange limit setup.depth slot runtime.arena valid)

theorem numericSeriesSum_clockRange (limit depth : ℕ) (head : List ℕ) (terms : List (ℚ × List ℕ)) :
    RangeAction limit (runtimeSequence ((List.range (depth+1)).map (fun k=>fun current=>
      let scaled:=runtimeSequence (terms.map (fun row=>runArena
        (rawScale (polynomialCoefficient (MvPolynomial.C row.1)) (row.2.getD k 0)))) current
      runArena (rawAdd ((head.getD k 0)::scaled.1)) scaled.2))) := by
  intro runtime valid
  apply runtimeSequence_clockRange limit _ ?_ runtime valid
  intro action member current paid
  obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
  apply runtimeSequence_clockRange limit _ ?_ current paid
  intro action member current paid
  obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
  exact paid

theorem originalForceOrEnergy_clockRange (limit : ℕ) (setup : RawSetup) (equation : Option (Fin 4)) :
    RangeAction limit (originalForceOrEnergy setup equation) := by
  intro runtime valid
  let affine:=originalAffine setup equation runtime
  let trace:=runtimeTrace setup.depth affine.2
  let first:=originalApplyT setup 0 0 trace.1 equation trace.2
  have hf : RuntimeClockRange limit first.2 := originalApplyT_clockRange limit setup 0 0 trace.1 equation trace.2
    (originalTrace_clockRange limit setup.depth affine.2.arena (originalAffine_clockRange limit setup equation runtime valid))
  let diagonalActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨4+i.val,by omega⟩ current
    originalApplyT setup (Fin.succ i) (Fin.succ i) source.1 equation source.2)
  let diagonal:=runtimeSequence diagonalActions first.2
  have hd : RuntimeClockRange limit diagonal.2 := by
    apply runtimeSequence_clockRange limit _ ?_ first.2 hf
    intro action member current paid
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_clockRange limit setup ⟨4+i.val,by omega⟩ i.succ i.succ equation current paid
  let crossIndices : List (Fin 4 × Fin 4 × Fin 13):=[(1,2,7),(1,3,8),(2,3,9)]
  let crossActions : List (RuntimeAction (List ℕ)) := crossIndices.map (fun entry=>fun current=>
    let source:=runtimeSource setup.depth entry.2.2 current
    originalApplyT setup entry.1 entry.2.1 source.1 equation source.2)
  let cross:=runtimeSequence crossActions diagonal.2
  have hc : RuntimeClockRange limit cross.2 := by
    apply runtimeSequence_clockRange limit _ ?_ diagonal.2 hd
    intro action member current paid
    obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_clockRange limit setup entry.2.2 entry.1 entry.2.1 equation current paid
  let timeActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨10+i.val,by omega⟩ current
    originalApplyT setup 0 (Fin.succ i) source.1 equation source.2)
  let time:=runtimeSequence timeActions cross.2
  have ht : RuntimeClockRange limit time.2 := by
    apply runtimeSequence_clockRange limit _ ?_ cross.2 hc
    intro action member current paid
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact sourceTemporal_clockRange limit setup ⟨10+i.val,by omega⟩ 0 i.succ equation current paid
  exact numericSeriesSum_clockRange limit setup.depth affine.1
    ([(1/2,first.1)]++diagonal.1.map (fun row=>(-1/2,row))++
      cross.1.map (fun row=>(-1,row))++time.1.map (fun row=>(-1,row))) time.2 ht

attribute [local irreducible] originalForceOrEnergy runtimeSequence runtimeSetup
set_option backward.isDefEq.respectTransparency true

def installStep (k : ℕ) (residualIds : List ℕ)
    (out : RawClocks × List ℕ × List ℕ × RawRuntime) (a : Fin 4) :
    RawClocks × List ℕ × List ℕ × RawRuntime :=
  let atom:=runArena (rawAtom (.clock k a) false) out.2.2.2
  let nextClocks:=clockInsert out.1 (k+1) a atom.1
  let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
    (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))) atom.2
  let definition:=runArena (rawAdd scaled.1) scaled.2
  (nextClocks,out.2.1++[atom.1],out.2.2.1++[definition.1],definition.2)

theorem originalInstall_as_fold (k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime) :
    originalInstall k residualIds clocks runtime=(List.finRange 4).foldl (installStep k residualIds) (clocks,[],[],runtime) := rfl

theorem installStep_nodes (k : ℕ) (residualIds : List ℕ)
    (out : RawClocks × List ℕ × List ℕ × RawRuntime) (a : Fin 4) :
    (installStep k residualIds out a).2.2.2.arena.nodes=(rawAtom (.clock k a) false out.2.2.2.arena).2.nodes := by
  unfold installStep runtimeSequence
  rfl

theorem installStep_clockRange (limit k : ℕ) (residualIds : List ℕ)
    (out : RawClocks × List ℕ × List ℕ × RawRuntime) (a : Fin 4)
    (paid : RuntimeClockRange limit out.2.2.2) (orderBound : k < limit) :
    RuntimeClockRange limit (installStep k residualIds out a).2.2.2 := by
  intro node member
  rw [installStep_nodes] at member
  exact rawAtom_clockRange limit (.clock k a) false out.2.2.2.arena paid orderBound node member

set_option maxHeartbeats 200000 in
theorem originalInstall_clockRange (limit k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (valid : RuntimeClockRange limit runtime) (orderBound : k < limit) :
    RuntimeClockRange limit (originalInstall k residualIds clocks runtime).2.2.2 := by
  rw [originalInstall_as_fold]
  exact fold_invariant (List.finRange 4) (installStep k residualIds)
    (fun out=>RuntimeClockRange limit out.2.2.2)
    (fun out paid a _=>installStep_clockRange limit k residualIds out a paid orderBound)
    (clocks,[],[],runtime) valid

def checksStep (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ)
    (out : List ℕ × List Bool × RawRuntime) (a : Fin 4) : List ℕ × List Bool × RawRuntime :=
  let result:=originalForceOrEnergy setup (some a) out.2.2
  let new:=result.1.getD order 0
  let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
    (rawScale (jacobianCoefficient a b) (clockIds.getD b.val 0)))) result.2
  let expected:=runArena (rawAdd ((residualIds.getD a.val 0)::scaled.1)) scaled.2
  (out.1++[new],out.2.1++[decide (new=expected.1)],expected.2)

theorem originalChecks_as_fold (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ) (runtime : RawRuntime) :
    originalChecks setup order residualIds clockIds runtime=
      (List.finRange 4).foldl (checksStep setup order residualIds clockIds) ([],[],runtime) := rfl

theorem checksStep_nodes (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ)
    (out : List ℕ × List Bool × RawRuntime) (a : Fin 4) :
    (checksStep setup order residualIds clockIds out a).2.2.arena.nodes=
      (originalForceOrEnergy setup (some a) out.2.2).2.arena.nodes := by
  unfold checksStep runtimeSequence
  rfl

theorem checksStep_clockRange (limit : ℕ) (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ)
    (out : List ℕ × List Bool × RawRuntime) (a : Fin 4) (paid : RuntimeClockRange limit out.2.2) :
    RuntimeClockRange limit (checksStep setup order residualIds clockIds out a).2.2 := by
  intro node member
  rw [checksStep_nodes] at member
  exact originalForceOrEnergy_clockRange limit setup (some a) out.2.2 paid node member

set_option maxHeartbeats 200000 in
theorem originalChecks_clockRange (limit : ℕ) (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ)
    (runtime : RawRuntime) (valid : RuntimeClockRange limit runtime) :
    RuntimeClockRange limit (originalChecks setup order residualIds clockIds runtime).2.2 := by
  rw [originalChecks_as_fold]
  exact fold_invariant (List.finRange 4) (checksStep setup order residualIds clockIds)
    (fun out=>RuntimeClockRange limit out.2.2)
    (fun out paid a _=>checksStep_clockRange limit setup order residualIds clockIds out a paid)
    ([],[],runtime) valid

theorem originalEngineNext_clockRange (limit k : ℕ) (engine : RawEngineState)
    (valid : RuntimeClockRange limit engine.runtime) (orderBound : k < limit) :
    RuntimeClockRange limit (originalEngineNext k engine).runtime := by
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let residuals:=runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))) before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  let checked:=originalChecks after.1 (k+1) residualIds installed.2.1 after.2
  have hr : RuntimeClockRange limit residuals.2 := by
    apply runtimeSequence_clockRange limit _ ?_ before.2 (runtimeSetup_clockRange _ _ _ _ valid)
    intro action member current paid
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_clockRange _ _ _ _ paid
  have hi:=originalInstall_clockRange limit k residualIds engine.clocks residuals.2 hr orderBound
  have ha:=runtimeSetup_clockRange limit (k+1) installed.1 installed.2.2.2 hi
  have hc:=originalChecks_clockRange limit after.1 (k+1) residualIds installed.2.1 after.2 ha
  exact originalForceOrEnergy_clockRange limit after.1 none checked.2.2 hc



theorem originalBoot_clockRange (limit : ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (valid : RuntimeClockRange limit runtime) : RuntimeClockRange limit (originalBoot clocks runtime).runtime := by
  let setup:=runtimeSetup 0 clocks runtime
  let forces:=runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy setup.1 (some a))) setup.2
  have hf : RuntimeClockRange limit forces.2 := by
    apply runtimeSequence_clockRange limit _ ?_ setup.2 (runtimeSetup_clockRange _ _ _ _ valid)
    intro action member current paid
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_clockRange _ _ _ _ paid
  change RuntimeClockRange limit (originalForceOrEnergy setup.1 none forces.2).2
  exact originalForceOrEnergy_clockRange limit setup.1 none forces.2 hf

theorem originalEngine_clockRange (order : ℕ) : RuntimeClockRange order (originalEngine order).runtime := by
  induction order with
  | zero=>
    apply originalBoot_clockRange
    intro node member
    change node∈rawInitial.nodes at member
    rw [rawInitial_nodes] at member
    exact False.elim (List.not_mem_nil member)
  | succ k ih=>exact originalEngineNext_clockRange (k+1) k (originalEngine k) (clockRange_mono (by omega) ih) (by omega)


def originalResidualRun (k : ℕ) : List (List ℕ) × RawRuntime :=
  let engine:=originalEngine k
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))) before.2

theorem originalResidualRun_handles (k : ℕ) :
    RuntimeHandles (originalResidualRun k).2 ∧
      ∀ row,row∈(originalResidualRun k).1 → ListHandles (originalResidualRun k).2.arena row := by
  let engine:=originalEngine k
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  have source:=originalEngine_handles k
  have setup:=runtimeSetup_handles (k+1) engine.clocks engine.runtime source.runtime source.clocks
  apply runtimeSequence_handles ListHandles (fun h _ hv=>list_extend h hv)
    before.2 before.2 _ (RawExtends.refl _) setup.1
  · intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  · intro action member current extension paid
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_handles before.1 (some a) current paid (setup.2.extend extension)

theorem originalResidualRun_earlier_clocks (k : ℕ) : RuntimeClockRange k (originalResidualRun k).2 := by
  let engine:=originalEngine k
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  apply runtimeSequence_clockRange k _ ?_ before.2
    (runtimeSetup_clockRange k (k+1) engine.clocks engine.runtime (originalEngine_clockRange k))
  intro action member current paid
  obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
  exact originalForceOrEnergy_clockRange k before.1 (some a) current paid

theorem originalFive_clock_reference (k : ℕ) (node : RawNode)
    (member : node∈(originalEngine (k+1)).runtime.arena.nodes) (level : ℕ) (axis : Fin 4)
    (kind : node.kind=RawKind.clock level axis) : level < k+1 := by
  have bound:=originalEngine_clockRange (k+1) node member
  simpa only [kind,KindClockBelow] using bound

def originalAssertions (order : ℕ) : Bool :=
  let engine:=originalEngine order
  engine.leadingChecks.all id && engine.stages.all (fun stage=>stage.correctionChecks.all id && stage.newestExcluded)

-- The source's assert branch is exposed as computed execution data, not supplied
-- as a Boolean witness to the graph or native-value producer.
def originalAcceptedRun (order : ℕ) : Option RawEngineState :=
  if originalAssertions order then some (originalEngine order) else none

theorem originalAcceptedRun_branch (order : ℕ) :
    originalAcceptedRun order=some (originalEngine order) ↔ originalAssertions order=true := by
  unfold originalAcceptedRun
  split_ifs with condition <;> simp_all

theorem originalAcceptedRun_reject (order : ℕ) :
    originalAcceptedRun order=none ↔ originalAssertions order=false := by
  unfold originalAcceptedRun
  split_ifs with condition <;> simp_all


-- Root words of a clock definition refer only to nodes present before installing
-- the new clocks; the old table's Moyal closure then controls every child edge.
def Supported (base current : RawArena) (id : ℕ) : Prop :=
  Handle current id ∧ RawWords (fun node=>node < base.nodes.length) (rawRows current id)

theorem supported_extend {base old next : RawArena} (extension : RawExtends old next) {id : ℕ}
    (valid : Supported base old id) : Supported base next id := by
  refine ⟨handle_extend extension valid.1,?_⟩
  rw [rawRows_preserved extension id valid.1]
  exact valid.2

theorem rawScale_supported (P : ℕ → Prop) (c : NormalizedCoefficient) (id : ℕ) (state : RawArena)
    (valid : RawWords P (rawRows state id)) : RawWords P (rawRows (rawScale c id state).2 (rawScale c id state).1) := by
  rw [show rawRows (rawScale c id state).2 (rawScale c id state).1=
    rawNormalize ((rawRows state id).map (fun row=>⟨multiplyCoefficient c row.coefficient,row.word⟩)) from rawPoly_reference _ _]
  apply rawNormalize_words
  intro row member node hn
  obtain ⟨prior,hp,rfl⟩:=List.mem_map.mp member
  exact valid prior hp node hn

theorem rawAdd_supported (P : ℕ → Prop) (ids : List ℕ) (state : RawArena)
    (valid : ∀ id,id∈ids → RawWords P (rawRows state id)) :
    RawWords P (rawRows (rawAdd ids state).2 (rawAdd ids state).1) := by
  rw [show rawRows (rawAdd ids state).2 (rawAdd ids state).1=rawNormalize (ids.flatMap (rawRows state)) from rawPoly_reference _ _]
  apply rawNormalize_words
  intro row member node hn
  obtain ⟨id,hi,hr⟩:=List.mem_flatMap.mp member
  exact valid id hi row hr node hn

theorem originalInstall_definition_support (k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime)
    (valid : RuntimeHandles runtime) (residualValid : ListHandles runtime.arena residualIds) :
    ∀ id,id∈(originalInstall k residualIds clocks runtime).2.2.1 →
      Supported runtime.arena (originalInstall k residualIds clocks runtime).2.2.2.arena id := by
  have result:=fold_invariant (List.finRange 4) (installStep k residualIds)
    (fun out=>RawExtends runtime.arena out.2.2.2.arena ∧ RuntimeHandles out.2.2.2 ∧
      ∀ id,id∈out.2.2.1 → Supported runtime.arena out.2.2.2.arena id) (by
      intro out paid a member
      let atom:=runArena (rawAtom (.clock k a) false) out.2.2.2
      let actions:=(List.finRange 4).map (fun b=>runArena
        (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))
      let scaled:=runtimeSequence actions atom.2
      let definition:=runArena (rawAdd scaled.1) scaled.2
      have hatom:=runAtom_handles (.clock k a) false out.2.2.2 paid.2.1 (by intro id member;cases member)
      have atomGrow : RawExtends runtime.arena atom.2.arena := paid.1.trans (rawAtom_extends _ _ _)
      have grows : ∀ action,action∈actions → RuntimeGrows action := by
        intro action member current
        obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
        exact rawScale_extends _ _ _
      have hs:=runtimeSequence_handles (Supported runtime.arena) (fun h _ hv=>supported_extend h hv)
        runtime atom.2 actions atomGrow hatom.1 grows (by
          intro action member current extension currentValid
          obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
          have bounded:=list_getD_handle valid residualValid b.val
          have words : RawWords (fun node=>node < runtime.arena.nodes.length)
              (rawRows current.arena (residualIds.getD b.val 0)) := by
            rw [rawRows_preserved extension _ bounded]
            exact rawRows_words _ valid.closed _
          exact ⟨(runScale_handles _ _ current currentValid).1,
            rawPoly_bound _ _,rawScale_supported _ _ _ _ words⟩)
      have hd:=runAdd_handles scaled.1 scaled.2 hs.1
      have definitionSupport : Supported runtime.arena definition.2.arena definition.1 :=
        ⟨hd.2,rawAdd_supported _ _ _ (fun id member=>(hs.2 id member).2)⟩
      have tailGrow : RawExtends atom.2.arena definition.2.arena :=
        (runtimeSequence_grows actions grows atom.2).trans (rawAdd_extends _ _)
      have allGrow : RawExtends out.2.2.2.arena definition.2.arena := (rawAtom_extends _ _ _).trans tailGrow
      refine ⟨paid.1.trans allGrow,hd.1,?_⟩
      intro id member
      rcases List.mem_append.mp member with old|fresh
      · exact supported_extend allGrow (paid.2.2 id old)
      · have equal:=List.mem_singleton.mp fresh
        subst id;exact definitionSupport)
    (clocks,[],[],runtime) ⟨RawExtends.refl _,valid,fun id member=>False.elim (List.not_mem_nil member)⟩
  rw [originalInstall_as_fold]
  exact result.2.2

def originalInstalledRun (k : ℕ) : RawClocks × List ℕ × List ℕ × RawRuntime :=
  originalInstall k ((originalResidualRun k).1.map (fun row=>row.getD (k+1) 0))
    (originalEngine k).clocks (originalResidualRun k).2

theorem originalInstalled_definition_support (k : ℕ) :
    ∀ id,id∈(originalInstalledRun k).2.2.1 →
      Supported (originalResidualRun k).2.arena (originalInstalledRun k).2.2.2.arena id := by
  have residual:=originalResidualRun_handles k
  apply originalInstall_definition_support _ _ _ _ residual.1
  intro id member
  obtain ⟨row,rowMember,rfl⟩:=List.mem_map.mp member
  exact list_getD_handle residual.1 (residual.2 row rowMember) (k+1)

theorem originalInstalled_clock_earlier (k id node level : ℕ) (axis : Fin 4)
    (definition : id∈(originalInstalledRun k).2.2.1)
    (row : RawRow) (member : row∈rawRows (originalInstalledRun k).2.2.2.arena id)
    (inWord : node∈row.word)
    (clock : (rawNode (originalInstalledRun k).2.2.2.arena node).kind=.clock level axis) : level < k := by
  have support:=originalInstalled_definition_support k id definition
  have bound:=support.2 row member node inWord
  have extension:=originalInstall_grows k ((originalResidualRun k).1.map (fun row=>row.getD (k+1) 0))
    (originalEngine k).clocks (originalResidualRun k).2
  have oldNode : rawNode (originalInstalledRun k).2.2.2.arena node=rawNode (originalResidualRun k).2.arena node :=
    rawNode_preserved extension node bound
  rw [oldNode] at clock
  have range:=originalResidualRun_earlier_clocks k _ (rawNode_member _ node bound)
  simpa only [clock,KindClockBelow] using range

end LowEnergy.PreparationVacuumExecutionGraph

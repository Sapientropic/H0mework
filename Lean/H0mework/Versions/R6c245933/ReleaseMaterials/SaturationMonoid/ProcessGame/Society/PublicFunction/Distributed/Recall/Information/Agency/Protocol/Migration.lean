import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Alignment
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.CrossMigration

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Migration

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

private def moveGrant {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) : Mandate.Grant base scope second secondWord := by
  cases sameCurrent; cases sameWord; exact grant

private def rawGrantImage (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
    (base : RawLaw Party Good Port Technology Instrument) (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port))
    (currentAt : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (wordAt : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
    (birth last : Nat) (grant : Mandate.Grant base scope (currentAt birth) (wordAt birth)) :
    Authority.Trace.GrantImage Party Good Port Technology Instrument :=
  let history := Mandate.Lifecycle.Observed.through (base := base) (scope := scope)
    (currentAt := currentAt) (wordAt := wordAt) (birth := birth) (grant := grant) last
  ⟨birth,Authority.Trace.itemImage code grant.proposal.item.val,
    Authority.Trace.itemImage code grant.acceptance.item.val,
    Authority.Trace.grantObligationImage (Mandate.Lifecycle.original base scope currentAt wordAt birth grant),
    Authority.Trace.grantObligationImage history.obligation,Authority.Trace.grantHistoryImage code history⟩

structure GrantTrajectory (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
    (base : RawLaw Party Good Port Technology Instrument) (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)) where
  beforeCurrent : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument
  beforeWord : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  afterCurrent : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument
  afterWord : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  arrival : Nat
  last : Nat
  prefixCurrent : ∀ birth ≤ arrival, afterCurrent birth = beforeCurrent birth
  prefixWord : ∀ birth ≤ arrival, afterWord birth = beforeWord birth

def GrantTrajectory.images {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
    (trace : GrantTrajectory code base scope) :
    List (Authority.Trace.GrantImage Party Good Port Technology Instrument ×
      Authority.Trace.GrantImage Party Good Port Technology Instrument) :=
  (List.finRange (trace.arrival+1)).flatMap fun birth =>
    (Mandate.grantsAt base scope (trace.beforeCurrent birth.val) (trace.beforeWord birth.val)).map fun grant =>
      (rawGrantImage code base scope trace.beforeCurrent trace.beforeWord birth.val trace.arrival grant,
        rawGrantImage code base scope trace.afterCurrent trace.afterWord birth.val trace.last
          (moveGrant (trace.prefixCurrent birth.val (Nat.le_of_lt_succ birth.isLt))
            (trace.prefixWord birth.val (Nat.le_of_lt_succ birth.isLt)) grant))

def grantTrajectory (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
    (input : Input bound.source.code) (cut : Nat) (rival : Opponent bound.source.code)
    (term : Cut.Term bound.source input cut) (active : bound.source.feedback? = some input) :
    GrantTrajectory bound.source.code bound.base bound.scope where
  beforeCurrent := Native.Authority.currentAt bound
  beforeWord := Native.Authority.wordAt bound
  afterCurrent := Native.Authority.currentAt (Authority.candidate bound input cut rival term)
  afterWord := Native.Authority.wordAt (Authority.candidate bound input cut rival term)
  arrival := Authority.arrivalDepth bound cut
  last := Authority.terminalDepth bound input cut
  prefixCurrent := Authority.prefix_grant_current bound input cut rival term active
  prefixWord := Authority.prefix_grant_word bound input cut rival term active

theorem grant_trajectory_is_the_complete_original_migration
    (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (input : Input bound.source.code) (cut : Nat) (rival : Opponent bound.source.code)
    (term : Cut.Term bound.source input cut) (active : bound.source.feedback? = some input) :
    (Authority.Trace.generate bound input cut rival term active).originalGrants =
      (grantTrajectory bound input cut rival term active).images := by
  simp only [Authority.Trace.generate,Authority.grantContinuations,List.map_map]
  change (Native.Authority.recordsAt bound (Authority.arrivalDepth bound cut)).attach.map
    (fun record => (Authority.Trace.grantImage bound record.val.1.val _ record.val.2,
      Authority.Trace.continuedGrantImage bound input cut rival term active record)) = _
  calc
    _ = (Native.Authority.recordsAt bound (Authority.arrivalDepth bound cut)).attach.map
        (fun record => (rawGrantImage bound.source.code bound.base bound.scope
          (Native.Authority.currentAt bound) (Native.Authority.wordAt bound)
          record.val.1.val (Authority.arrivalDepth bound cut) record.val.2.admission.grant,
          rawGrantImage bound.source.code bound.base bound.scope
            (Native.Authority.currentAt (Authority.candidate bound input cut rival term))
            (Native.Authority.wordAt (Authority.candidate bound input cut rival term))
            record.val.1.val (Authority.terminalDepth bound input cut)
            (Authority.migratedGrant bound input cut rival term active record))) := by
      apply List.map_congr_left
      intro record _
      simp only [Authority.Trace.grantImage,Authority.Trace.continuedGrantImage,
        Native.Authority.traceGrant,Mandate.admitGrant,rawGrantImage,record.val.2.exact]
      rfl
    _ = _ := by
      let row := fun record : Authority.OriginalGrant bound cut =>
        (rawGrantImage bound.source.code bound.base bound.scope
          (Native.Authority.currentAt bound) (Native.Authority.wordAt bound)
          record.1.val (Authority.arrivalDepth bound cut) record.2.admission.grant,
          rawGrantImage bound.source.code bound.base bound.scope
            (Native.Authority.currentAt (Authority.candidate bound input cut rival term))
            (Native.Authority.wordAt (Authority.candidate bound input cut rival term))
            record.1.val (Authority.terminalDepth bound input cut)
            (moveGrant (Authority.prefix_grant_current bound input cut rival term active _ (Nat.le_of_lt_succ record.1.isLt))
              (Authority.prefix_grant_word bound input cut rival term active _ (Nat.le_of_lt_succ record.1.isLt)) record.2.admission.grant))
      change (Native.Authority.recordsAt bound (Authority.arrivalDepth bound cut)).attach.map
        (fun record => row record.val) = _
      rw [List.attach_map_val]
      simp only [Native.Authority.recordsAt,List.map_flatMap,List.map_map,Function.comp_def,
        row,Native.Authority.traceGrant,Mandate.admitGrant,GrantTrajectory.images,grantTrajectory]


omit [DecidableEq Port] [DecidableEq Technology] in
theorem GrantTrajectory.ext {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    {base : RawLaw Party Good Port Technology Instrument}
    {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
    (first second : GrantTrajectory code base scope)
    (beforeCurrent : first.beforeCurrent = second.beforeCurrent)
    (beforeWord : first.beforeWord = second.beforeWord)
    (afterCurrent : first.afterCurrent = second.afterCurrent)
    (afterWord : first.afterWord = second.afterWord)
    (arrival : first.arrival = second.arrival) (last : first.last = second.last) : first = second := by
  cases first
  cases second
  cases beforeCurrent
  cases beforeWord
  cases afterCurrent
  cases afterWord
  cases arrival
  cases last
  rfl

private theorem currentAt_of_input
    (first second : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (same : first.source.input = second.source.input) :
    Native.Authority.currentAt first = Native.Authority.currentAt second := by
  funext ordinal
  exact congrArg (fun input : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument =>
    ((ProgrammeLiving.projectionLaw input).project .execution
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (ordinal+1)).current) ()).before) same

private theorem wordAt_of_input
    (first second : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument))
    (same : first.source.input = second.source.input) :
    Native.Authority.wordAt first = Native.Authority.wordAt second := by
  funext ordinal
  exact congrArg (fun input : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument =>
    ((ProgrammeLiving.projectionLaw input).project .execution
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (ordinal+1)).current) ()).submitted) same

namespace Generated

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (first second : Cursor model.source.code) (matched : Aligned first second)
  (firstDriver secondDriver : Opponent model.source.code)
  (firstTerm : Cut.Term first.source first.entry first.cut)
  (secondTerm : Cut.Term second.source second.entry second.cut)
  (emitted : (Future.target first.source first.entry first.cut firstDriver firstTerm.val).input =
    (Future.target second.source second.entry second.cut secondDriver secondTerm.val).input)

abbrev evaluation (point : Cursor model.source.code) (driver : Opponent model.source.code)
    (programme : Cut.Term point.source point.entry point.cut) :=
  evaluate (Replanning.native model point) point.entry point.cut rfl driver programme

include matched firstDriver secondDriver firstTerm secondTerm emitted

theorem aligned_original_grant_migration :
    (evaluation model first firstDriver firstTerm).native.originalGrants =
      (evaluation model second secondDriver secondTerm).native.originalGrants := by
  change (Authority.Trace.generate (Replanning.native model first) _ _ _ _ rfl).originalGrants =
    (Authority.Trace.generate (Replanning.native model second) _ _ _ _ rfl).originalGrants
  rw [grant_trajectory_is_the_complete_original_migration,grant_trajectory_is_the_complete_original_migration]
  apply congrArg GrantTrajectory.images
  apply GrantTrajectory.ext
  · exact currentAt_of_input _ _
      (matched.input)
  · exact wordAt_of_input _ _
      (matched.input)
  · exact currentAt_of_input _ _
      emitted
  · exact wordAt_of_input _ _
      emitted
  · exact congrArg₂ (fun history cut => history.length+cut) matched.history matched.cut
  · exact congrArg (·-2) matched.finish


open Mandate.Challenge

private abbrev finiteCandidate := Authority.candidate (Replanning.native model first) first.entry first.cut
  firstDriver firstTerm
private abbrev actualCandidate := Authority.candidate (Replanning.native model second) second.entry second.cut
  secondDriver secondTerm

private theorem original_challenge_lifecycle
    (firstData : Authority.OriginalChallenge (Replanning.native model second))
    (firstInside : firstData ∈ Native.Authority.challengesAt (Replanning.native model second) (Cut.start second.source second.cut))
    (secondData : Authority.OriginalChallenge (Replanning.native model first))
    (secondInside : secondData ∈ Native.Authority.challengesAt (Replanning.native model first) (Cut.start first.source first.cut))
    (same : Authority.Trace.challengeImage model.source.code (Native.Authority.programme model)
        (Native.Authority.sourceIndex (Replanning.native model first)) secondData.1 =
      Authority.Trace.challengeImage model.source.code (Native.Authority.programme model)
        (Native.Authority.sourceIndex (Replanning.native model second)) firstData.1) :
    Authority.Trace.CrossMigration.Match model.source.code (Native.Authority.programme model)
      (Authority.Trace.continuedChallenge (Replanning.native model second)
        second.entry second.cut
        secondDriver secondTerm rfl ⟨firstData,firstInside⟩)
      (Authority.Trace.continuedChallenge (Replanning.native model first)
        first.entry first.cut
        firstDriver firstTerm rfl ⟨secondData,secondInside⟩) := by
  let family := Native.Authority.programme model
  have firstPrefix := Cross.Programme.record_is_its_actual_prefix family
    (Cut.start second.source second.cut) firstData firstInside
  have secondPrefix := Cross.Programme.record_is_its_actual_prefix family
    (Cut.start first.source first.cut) secondData secondInside
  have inputs : I family (Native.Authority.sourceIndex (Replanning.native model first)) =
      I family (Native.Authority.sourceIndex (Replanning.native model second)) :=
    matched.input
  have initialMatch : Authority.Trace.LocalLifecycle.Match model.source.code family firstData.2 secondData.2 := by
    rw [firstPrefix.2,secondPrefix.2]
    simp only [matched.start]
    exact Authority.Trace.LocalLifecycle.through_match model.source.code family
      (Cut.start second.source second.cut)
      (congrArg ProgrammeSource.Input.initial inputs) (fun ordinal _ => by rw [inputs]) _ (Nat.le_refl _) same
  have firstWithin : Cross.Programme.Within family
      (Cut.start second.source second.cut) (Cross.History.inherit family firstData.2) := by
    apply Cross.Programme.inherit_within
    rw [firstPrefix.2]
    exact Cross.Programme.local_through_within _ _ _ _ firstPrefix.1 (Nat.le_refl _)
  have secondWithin : Cross.Programme.Within family
      (Cut.start first.source first.cut) (Cross.History.inherit family secondData.2) := by
    apply Cross.Programme.inherit_within
    rw [secondPrefix.2]
    exact Cross.Programme.local_through_within _ _ _ _ secondPrefix.1 (Nat.le_refl _)
  have transported : Authority.Trace.CrossMigration.Match model.source.code family
      (Authority.inheritedChallenge (Replanning.native model second) second.entry second.cut
        secondDriver secondTerm rfl ⟨firstData,firstInside⟩)
      (Authority.inheritedChallenge (Replanning.native model first) first.entry first.cut
        firstDriver firstTerm rfl ⟨secondData,secondInside⟩) := by
    unfold Authority.inheritedChallenge
    exact Authority.Trace.CrossMigration.transport_independent_prefixes model.source.code family
      (inputs := Native.Authority.sourceIndex (actualCandidate model second secondDriver secondTerm))
      (nextInputs := Native.Authority.sourceIndex (finiteCandidate model first firstDriver firstTerm)) _ _
      (Authority.Trace.CrossMigration.inherit_match model.source.code family _ _ initialMatch)
      _ _ firstWithin secondWithin rfl rfl
      (Future.prior_raw_event second.source second.entry second.cut
        secondDriver secondTerm.val rfl)
      (Future.prior_raw_event first.source first.entry first.cut
        firstDriver firstTerm.val rfl)

  change Authority.Trace.CrossMigration.Match model.source.code family
    (Cross.Programme.continueFrom family
      (Authority.inheritedChallenge (Replanning.native model second) second.entry second.cut
        secondDriver secondTerm rfl ⟨firstData,firstInside⟩)
      (Cut.start second.source second.cut)
      (Cut.horizon second.source second.entry second.cut))
    (Cross.Programme.continueFrom family
      (Authority.inheritedChallenge (Replanning.native model first) first.entry first.cut
        firstDriver firstTerm rfl ⟨secondData,secondInside⟩)
      (Cut.start first.source first.cut)
      (Cut.horizon first.source first.entry first.cut))
  simp only [matched.horizon,matched.start]
  have targets : I family (Native.Authority.sourceIndex (finiteCandidate model first firstDriver firstTerm)) =
      I family (Native.Authority.sourceIndex (actualCandidate model second secondDriver secondTerm)) :=
    emitted
  apply Authority.Trace.CrossMigration.continue_match model.source.code family
    (Cut.finish second.source second.entry second.cut)
    (congrArg ProgrammeSource.Input.initial targets) (fun ordinal _ => by rw [targets]) _ _ (Nat.le_refl _) _ _ transported
  apply Authority.Trace.ChallengeLifecycle.within_mono family
    (Cut.start second.source second.cut) _ (by simp only [Cut.finish];omega)
  unfold Authority.inheritedChallenge
  exact Authority.Trace.ChallengeLifecycle.transport_within family _ _ _ _

omit matched firstDriver secondDriver firstTerm secondTerm emitted [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument] in
private theorem mapped_images_determine_generated_rows {A B C D : Type}
    (first : List A) (second : List B) (f : A → C) (g : B → C) (row : A → D) (nextRow : B → D)
    (same : second.map g = first.map f)
    (generated : ∀ a ∈ first, ∀ b ∈ second, g b = f a → nextRow b = row a) :
    second.map nextRow = first.map row := by
  induction first generalizing second with
  | nil => cases second <;> simp_all
  | cons a rest ih =>
    cases second with
    | nil => cases same
    | cons b later =>
      have parts := List.cons.inj same
      exact congrArg₂ List.cons (generated a List.mem_cons_self b List.mem_cons_self parts.1)
        (ih later parts.2 (fun x hx y hy => generated x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)))

theorem aligned_original_challenge_migration :
    (evaluation model first firstDriver firstTerm).native.originalChallenges =
      (evaluation model second secondDriver secondTerm).native.originalChallenges := by
  let family := Native.Authority.programme model
  have inputs : I family (Native.Authority.sourceIndex (Replanning.native model first)) =
      I family (Native.Authority.sourceIndex (Replanning.native model second)) :=
    matched.input
  have census := Authority.Trace.ChallengeTransport.census_images model.source.code family
    (Cut.start second.source second.cut)
    (congrArg ProgrammeSource.Input.initial inputs) (fun ordinal _ => by rw [inputs]) _ (Nat.le_refl _)
  simp only [evaluate,Authority.Trace.generate,Authority.challengeContinuations,List.map_map]
  change (Native.Authority.challengesAt (Replanning.native model first) _).attach.map
      (fun record => (Authority.Trace.challengeImage model.source.code family _ record.val.1,
        Authority.Trace.challengeStateImage model.source.code family _ record.val.2.state.current,
        Authority.Trace.challengeStateImage model.source.code family _
          (Authority.Trace.continuedChallenge (Replanning.native model first) first.entry first.cut
            firstDriver firstTerm rfl record).state.current)) =
    (Native.Authority.challengesAt (Replanning.native model second) _).attach.map
      (fun record => (Authority.Trace.challengeImage model.source.code family _ record.val.1,
        Authority.Trace.challengeStateImage model.source.code family _ record.val.2.state.current,
        Authority.Trace.challengeStateImage model.source.code family _
          (Authority.Trace.continuedChallenge (Replanning.native model second) second.entry second.cut
            secondDriver secondTerm rfl record).state.current))
  apply mapped_images_determine_generated_rows _ _
    (fun record => Authority.Trace.challengeImage model.source.code family _ record.val.1)
    (fun record => Authority.Trace.challengeImage model.source.code family _ record.val.1)
  · rw [List.attach_map_val (f := fun record : Authority.OriginalChallenge (Replanning.native model first) =>
        Authority.Trace.challengeImage model.source.code family _ record.1),
      List.attach_map_val (f := fun record : Authority.OriginalChallenge (Replanning.native model second) =>
        Authority.Trace.challengeImage model.source.code family _ record.1)]
    simpa only [family,Authority.OriginalChallenge,Native.Authority.Challenge,Native.Authority.ChallengeHistory,Native.Authority.challengesAt,Native.Authority.programme,Replanning.native,matched.start] using census
  · intro first _ second _ same
    have lifecycle := original_challenge_lifecycle model _ _ matched firstDriver secondDriver firstTerm secondTerm emitted first.val first.property second.val second.property same
    have firstPrefix := Cross.Programme.record_is_its_actual_prefix family _ first.val first.property
    have secondPrefix := Cross.Programme.record_is_its_actual_prefix family _ second.val second.property
    have before : Authority.Trace.challengeStateImage model.source.code family _ second.val.2.state.current =
        Authority.Trace.challengeStateImage model.source.code family _ first.val.2.state.current := by
      rw [firstPrefix.2,secondPrefix.2]
      simpa only [family,Authority.OriginalChallenge,Native.Authority.Challenge,Native.Authority.ChallengeHistory,Native.Authority.challengesAt,Native.Authority.programme,Replanning.native,matched.start] using (Authority.Trace.LocalLifecycle.through_match model.source.code family _
        (congrArg ProgrammeSource.Input.initial inputs) (fun ordinal _ => by rw [inputs]) _ (Nat.le_refl _) same).state
    exact Prod.ext same (Prod.ext before lifecycle.state)

theorem aligned_candidate_grants :
    (evaluation model first firstDriver firstTerm).native.candidateGrants =
      (evaluation model second secondDriver secondTerm).native.candidateGrants := by
  have currents := currentAt_of_input (finiteCandidate model first firstDriver firstTerm)
    (actualCandidate model second secondDriver secondTerm) emitted
  have words := wordAt_of_input (finiteCandidate model first firstDriver firstTerm)
    (actualCandidate model second secondDriver secondTerm) emitted
  change (Native.Authority.recordsAt (finiteCandidate model first firstDriver firstTerm)
      (Cut.finish first.source first.entry first.cut-2)).map
      (fun record => Authority.Trace.grantImage (finiteCandidate model first firstDriver firstTerm) record.1.val _ record.2) =
    (Native.Authority.recordsAt (actualCandidate model second secondDriver secondTerm)
      (Cut.finish second.source second.entry second.cut-2)).map
      (fun record => Authority.Trace.grantImage (actualCandidate model second secondDriver secondTerm) record.1.val _ record.2)
  rw [matched.finish]
  simp only [Native.Authority.recordsAt,List.map_flatMap,List.map_map,Function.comp_def,
    Authority.Trace.grantImage,Native.Authority.traceGrant,Mandate.admitGrant]
  change (List.finRange (Cut.finish second.source second.entry second.cut-2+1)).flatMap
    (fun birth => (Mandate.grantsAt model.base model.scope
      (Native.Authority.currentAt (finiteCandidate model first firstDriver firstTerm) birth.val)
      (Native.Authority.wordAt (finiteCandidate model first firstDriver firstTerm) birth.val)).map
      (fun grant => rawGrantImage model.source.code model.base model.scope
        (Native.Authority.currentAt (finiteCandidate model first firstDriver firstTerm))
        (Native.Authority.wordAt (finiteCandidate model first firstDriver firstTerm)) birth.val
        (Cut.finish second.source second.entry second.cut-2) grant)) = _
  rw [currents,words]
  rfl

theorem aligned_candidate_challenges :
    (evaluation model first firstDriver firstTerm).native.candidateChallenges =
      (evaluation model second secondDriver secondTerm).native.candidateChallenges := by
  let family := Native.Authority.programme model
  have inputs : I family (Native.Authority.sourceIndex (finiteCandidate model first firstDriver firstTerm)) =
      I family (Native.Authority.sourceIndex (actualCandidate model second secondDriver secondTerm)) :=
    emitted
  have generated := Authority.Trace.LocalLifecycle.census_images model.source.code family
    (inputs := Native.Authority.sourceIndex (actualCandidate model second secondDriver secondTerm))
    (nextInputs := Native.Authority.sourceIndex (finiteCandidate model first firstDriver firstTerm))
    (Cut.finish second.source second.entry second.cut) (congrArg ProgrammeSource.Input.initial inputs)
    (fun ordinal _ => by rw [inputs]) _ (Nat.le_refl _)
  change (Native.Authority.challengesAt (finiteCandidate model first firstDriver firstTerm)
    (Cut.finish first.source first.entry first.cut)).map
      (fun record => (Authority.Trace.challengeImage model.source.code family _ record.1,
        Authority.Trace.challengeStateImage model.source.code family _ record.2.state.current)) = _
  rw [matched.finish]
  exact generated

theorem aligned_native_manifest :
    (evaluation model first firstDriver firstTerm).native =
      (evaluation model second secondDriver secondTerm).native := by
  apply (Authority.Trace.Manifest.mk.injEq ..).mpr
  refine ⟨?_,aligned_original_grant_migration model first second matched firstDriver secondDriver firstTerm secondTerm emitted,
    aligned_original_challenge_migration model first second matched firstDriver secondDriver firstTerm secondTerm emitted,
    aligned_candidate_grants model first second matched firstDriver secondDriver firstTerm secondTerm emitted,
    aligned_candidate_challenges model first second matched firstDriver secondDriver firstTerm secondTerm emitted⟩
  change (List.range (Cut.finish first.source first.entry first.cut)).map
    (fun ordinal => Identity.occurrenceImage model.source.code (finiteCandidate model first firstDriver firstTerm).source.input
      (ProgrammeHistory.visitAt (finiteCandidate model first firstDriver firstTerm).source.input ordinal).current) = _
  rw [matched.finish]
  exact congrArg (fun input => (List.range (Cut.finish second.source
    second.entry second.cut)).map fun ordinal =>
      Identity.occurrenceImage model.source.code input (ProgrammeHistory.visitAt input ordinal).current)
    emitted


end Generated

section
variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (first second : Cursor model.source.code) (matched : Aligned first second)
  (new : Rule model.source.code) (futureRival : Opponent model.source.code)

include matched

theorem aligned_original_grant_migration :
    (Replanning.actualEvaluation model first new futureRival).native.originalGrants =
      (Replanning.actualEvaluation model second new futureRival).native.originalGrants :=
  Generated.aligned_original_grant_migration model first second matched
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input

theorem aligned_original_challenge_migration :
    (Replanning.actualEvaluation model first new futureRival).native.originalChallenges =
      (Replanning.actualEvaluation model second new futureRival).native.originalChallenges :=
  Generated.aligned_original_challenge_migration model first second matched
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input

theorem aligned_candidate_grants :
    (Replanning.actualEvaluation model first new futureRival).native.candidateGrants =
      (Replanning.actualEvaluation model second new futureRival).native.candidateGrants :=
  Generated.aligned_candidate_grants model first second matched
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input

theorem aligned_candidate_challenges :
    (Replanning.actualEvaluation model first new futureRival).native.candidateChallenges =
      (Replanning.actualEvaluation model second new futureRival).native.candidateChallenges :=
  Generated.aligned_candidate_challenges model first second matched
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input

theorem aligned_native_manifest :
    (Replanning.actualEvaluation model first new futureRival).native =
      (Replanning.actualEvaluation model second new futureRival).native :=
  Generated.aligned_native_manifest model first second matched
    (Cursor.controller first new futureRival) (Cursor.controller second new futureRival)
    (term first.source first.entry first.cut new) (term second.source second.entry second.cut new)
    (matched.after new futureRival).input

end


variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (old new : Rule model.source.code)
  (pastRival futureRival : Opponent model.source.code)

private abbrev finitePoint := Transport.representative point old pastRival
private abbrev actualPoint := Transport.actual point old pastRival
private abbrev finiteBound := Replanning.native model (finitePoint model point old pastRival)
private abbrev actualBound := Replanning.native model (actualPoint model point old pastRival)

theorem the_new_rule_preserves_the_full_original_grant_migration :
    (Replanning.actualEvaluation model (finitePoint model point old pastRival) new futureRival).native.originalGrants =
      (Replanning.actualEvaluation model (actualPoint model point old pastRival) new futureRival).native.originalGrants :=
  aligned_original_grant_migration model _ _ (Aligned.representative point old pastRival) new futureRival

theorem the_new_rule_preserves_the_full_original_challenge_migration :
    (Replanning.actualEvaluation model (finitePoint model point old pastRival) new futureRival).native.originalChallenges =
      (Replanning.actualEvaluation model (actualPoint model point old pastRival) new futureRival).native.originalChallenges :=
  aligned_original_challenge_migration model _ _ (Aligned.representative point old pastRival) new futureRival

theorem the_new_rule_preserves_the_complete_native_manifest :
    (Replanning.actualEvaluation model (finitePoint model point old pastRival) new futureRival).native =
      (Replanning.actualEvaluation model (actualPoint model point old pastRival) new futureRival).native :=
  aligned_native_manifest model _ _ (Aligned.representative point old pastRival) new futureRival

structure SourceMatch (installed : Rule model.source.code) (environment : Opponent model.source.code)
    (next : Cursor model.source.code) : Prop extends Transport.SourceMatch model point installed environment next where
  renewed_native : ∀ (rule : Rule model.source.code) (rival : Opponent model.source.code),
    (Replanning.actualEvaluation model next rule rival).native =
      (Replanning.actualEvaluation model (Transport.actual point installed environment) rule rival).native

theorem the_public_representative_preserves_every_original_and_new_native_responsibility :
    SourceMatch model point old pastRival (Transport.representative point old pastRival) := by
  exact {
    toSourceMatch := Transport.the_public_representative_preserves_all_future_protocol_sources model point old pastRival
    renewed_native := fun rule rival => the_new_rule_preserves_the_complete_native_manifest model point old rule pastRival rival }

theorem one_public_successor_preserves_every_original_and_new_native_responsibility
    (domain : List (Cursor model.source.code)) (inside : point ∈ domain) :
    ∃ next ∈ advance model.source.code domain old, SourceMatch model point old pastRival next := by
  refine ⟨Transport.representative point old pastRival,
    every_generated_table_produces_its_own_successor model.source.code domain old point inside
      (externalTable point pastRival) (Residual.restriction_is_generated _ _ _ pastRival),?_⟩
  exact the_public_representative_preserves_every_original_and_new_native_responsibility model point old pastRival

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Migration

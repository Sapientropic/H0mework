import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalLifecycle
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.ChallengeLifecycle

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Transport

open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Normalization Normalization.RawProfile Authority.Trace Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (input : Input model.source.code) (cut : Nat)
  (raw nextRaw : List (Option model.source.code.Policy))
  (rival nextRival : Opponent model.source.code)

abbrev original := RawAuthority.candidate model input cut rival raw
abbrev normalized := RawAuthority.candidate model input cut nextRival nextRaw
abbrev finish := Cut.finish model.source input cut
abbrev last := Cut.finish model.source input cut-2

variable (observed : ∀ ordinal < Cut.finish model.source input cut,
  ProgrammeSource.rawEvent (normalized model input cut nextRaw nextRival).source.input
    (ProgrammeHistory.visitAt (original model input cut raw rival).source.input ordinal).current =
  ProgrammeSource.rawEvent (original model input cut raw rival).source.input
    (ProgrammeHistory.visitAt (original model input cut raw rival).source.input ordinal).current)
  (active : model.source.feedback? = some input)

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}

private def transportCandidateGrant
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) : Mandate.Grant base scope second secondWord := by
  cases sameCurrent; cases sameWord; exact grant

private theorem transport_candidate_event
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (transportCandidateGrant sameCurrent sameWord grant).electionEvent = grant.electionEvent := by
  cases sameCurrent; cases sameWord; rfl

private theorem transport_candidate_items
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Mandate.Grant base scope first firstWord) :
    (transportCandidateGrant sameCurrent sameWord grant).proposal.item.val = grant.proposal.item.val ∧
      (transportCandidateGrant sameCurrent sameWord grant).acceptance.item.val = grant.acceptance.item.val := by
  cases sameCurrent; cases sameWord; exact ⟨rfl, rfl⟩

private theorem transport_candidate_initial
    {oldCurrent newCurrent : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {oldWord newWord : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (birth : Nat) (sameCurrent : newCurrent birth = oldCurrent birth) (sameWord : newWord birth = oldWord birth)
    (grant : Mandate.Grant base scope (oldCurrent birth) (oldWord birth)) :
    Mandate.Lifecycle.Observed.initialState base scope newCurrent newWord birth
        (transportCandidateGrant sameCurrent sameWord grant) =
      Mandate.Lifecycle.Observed.initialState base scope oldCurrent oldWord birth grant := by
  change (Election.mandateAdmissionEdge Mandate.Grant.lineageCompiler
    (transportCandidateGrant sameCurrent sameWord grant).electionEvent).target = _
  rw [transport_candidate_event]
  rfl

include observed in
theorem current (visit : Nat) (inside : visit ≤ last model input cut) :
    Native.Authority.currentAt (normalized model input cut nextRaw nextRival) visit =
      Native.Authority.currentAt (original model input cut raw rival) visit :=
  Native.Coupling.History.raw_current (original model input cut raw rival).source.input
    (normalized model input cut nextRaw nextRival).source.input rfl rfl (finish model input cut)
    (observed) (visit+1)
    (by dsimp only [last,finish,Cut.finish,Cut.start] at *;omega)

include observed in
theorem word (visit : Nat) (inside : visit ≤ last model input cut) :
    Native.Authority.wordAt (normalized model input cut nextRaw nextRival) visit =
      Native.Authority.wordAt (original model input cut raw rival) visit :=
  (Native.Coupling.History.occurrences (original model input cut raw rival).source.input
    (normalized model input cut nextRaw nextRival).source.input rfl rfl (finish model input cut)
    (observed) (visit+1)
    (by dsimp only [last,finish,Cut.finish,Cut.start] at *;omega)).2

include observed in
theorem grant_image (birth : Nat) (inside : birth ≤ last model input cut)
    (grant : Mandate.Grant model.base model.scope
      (Native.Authority.currentAt (original model input cut raw rival) birth)
      (Native.Authority.wordAt (original model input cut raw rival) birth)) :
    grantImage (normalized model input cut nextRaw nextRival) birth
        (last model input cut) (Native.Authority.traceGrant _ _ _
          (transportCandidateGrant (current model input cut raw nextRaw rival nextRival observed birth inside)
            (word model input cut raw nextRaw rival nextRival observed birth inside) grant)) =
      grantImage (original model input cut raw rival) birth (last model input cut)
        (Native.Authority.traceGrant _ _ _ grant) := by
  have items := transport_candidate_items
    (current model input cut raw nextRaw rival nextRival observed birth inside)
    (word model input cut raw nextRaw rival nextRival observed birth inside) grant
  have initial := transport_candidate_initial birth
    (current model input cut raw nextRaw rival nextRival observed birth inside)
    (word model input cut raw nextRaw rival nextRival observed birth inside) grant
  have index := congrArg ExecutionItem.index items.2
  have state := Mandate.Lifecycle.Observed.through_state_congr (last model input cut) index initial
    (current model input cut raw nextRaw rival nextRival observed) (word model input cut raw nextRaw rival nextRival observed)
  have final := Mandate.Lifecycle.Observed.History.obligation_eq_of_state_eq _ _ state
  have history := grant_through_images_congr model.source.code (last model input cut) index initial
    (current model input cut raw nextRaw rival nextRival observed) (word model input cut raw nextRaw rival nextRival observed)
  have election := transport_candidate_event
    (current model input cut raw nextRaw rival nextRival observed birth inside)
    (word model input cut raw nextRaw rival nextRival observed birth inside) grant
  have original := congrArg (Election.mandateObligation (Mandate.Grant.lineageCompiler (Party := Party) (Port := Port))) election
  apply (GrantImage.mk.injEq ..).mpr
  exact ⟨rfl, congrArg (itemImage model.source.code) items.1, congrArg (itemImage model.source.code) items.2,
    congrArg grantObligationImage original, congrArg grantObligationImage final, history⟩

private theorem grantsAt_transport
    {first second : RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord) :
    Mandate.grantsAt base scope second secondWord =
      (Mandate.grantsAt base scope first firstWord).map (transportCandidateGrant sameCurrent sameWord) := by
  cases sameCurrent; cases sameWord
  exact (List.map_id _).symm

include observed in
theorem complete_grant_census :
    (Native.Authority.recordsAt (normalized model input cut nextRaw nextRival) (last model input cut)).map
      (fun record => grantImage (normalized model input cut nextRaw nextRival) record.1.val _ record.2) =
    (Native.Authority.recordsAt (original model input cut raw rival) (last model input cut)).map
      (fun record => grantImage (original model input cut raw rival) record.1.val _ record.2) := by
  simp only [Native.Authority.recordsAt,List.map_flatMap,List.map_map,Function.comp_def]
  apply congrArg (List.flatMap · (List.finRange (last model input cut+1)))
  funext birth
  have inside : birth.val ≤ last model input cut := Nat.le_of_lt_succ birth.isLt
  rw [grantsAt_transport (current model input cut raw nextRaw rival nextRival observed birth.val inside)
    (word model input cut raw nextRaw rival nextRival observed birth.val inside)]
  simp only [List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro grant _
  exact grant_image model input cut raw nextRaw rival nextRival observed birth.val inside grant


include active in
private theorem inherited_within (record : RawAuthority.ChallengeAtArrival model cut) :
    Cross.Programme.Within (Native.Authority.programme model) (Cut.start model.source cut)
      (RawAuthority.inheritedChallenge model input cut rival raw active record) := by
  unfold RawAuthority.inheritedChallenge
  exact ChallengeLifecycle.transport_within (Native.Authority.programme model) _ _ _ _

include active in
private theorem inherited_match (record : RawAuthority.ChallengeAtArrival model cut) :
    ChallengeLifecycle.Match model.source.code (Native.Authority.programme model)
      (RawAuthority.inheritedChallenge model input cut rival raw active record)
      (RawAuthority.inheritedChallenge model input cut nextRival nextRaw active record) := by
  have original := Cross.Programme.record_is_its_actual_prefix (Native.Authority.programme model)
    (Cut.start model.source cut) record.val record.property
  have within : Cross.Programme.Within (Native.Authority.programme model) (Cut.start model.source cut)
      (Cross.History.inherit (Native.Authority.programme model) record.val.2) := by
    apply Cross.Programme.inherit_within
    rw [original.2]
    exact Cross.Programme.local_through_within _ _ _ _ original.1 (Nat.le_refl _)
  unfold RawAuthority.inheritedChallenge
  exact ChallengeLifecycle.transport_seeds_match model.source.code (Native.Authority.programme model)
    (inputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival raw))
    (nextInputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut nextRival nextRaw))
    (Cross.History.inherit (Native.Authority.programme model) record.val.2) (Cut.start model.source cut) within rfl rfl
    (Future.prior_raw_event model.source input cut rival raw active)
    (Future.prior_raw_event model.source input cut nextRival nextRaw active)

include observed active in
theorem original_challenge_lifecycle (record : RawAuthority.ChallengeAtArrival model cut) :
    ChallengeLifecycle.Match model.source.code (Native.Authority.programme model)
      (Cross.Programme.continueFrom (Native.Authority.programme model)
        (RawAuthority.inheritedChallenge model input cut rival raw active record)
        (Cut.start model.source cut) (Cut.horizon model.source input cut))
      (Cross.Programme.continueFrom (Native.Authority.programme model)
        (RawAuthority.inheritedChallenge model input cut nextRival nextRaw active record)
        (Cut.start model.source cut) (Cut.horizon model.source input cut)) := by
  apply ChallengeLifecycle.continue_match model.source.code (Native.Authority.programme model)
    (inputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival raw))
    (nextInputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut nextRival nextRaw))
    (Cut.finish model.source input cut) rfl
    (observed)
    (Cut.start model.source cut) (Cut.horizon model.source input cut) (Nat.le_refl _)
    _ _ (inherited_match model input cut raw nextRaw rival nextRival active record)
  exact ChallengeLifecycle.within_mono (Native.Authority.programme model) (Cut.start model.source cut) (Cut.finish model.source input cut)
    (by simp only [Cut.finish];omega) _ (inherited_within model input cut raw rival active record)

include observed active in
theorem original_challenge_manifest :
    (RawAuthority.manifest model input cut nextRival nextRaw active).originalChallenges =
      (RawAuthority.manifest model input cut rival raw active).originalChallenges := by
  simp only [RawAuthority.manifest,RawAuthority.challengeContinuations,List.map_map]
  change (Native.Authority.challengesAt model (Cut.start model.source cut)).attach.map
      (fun record => (challengeImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.val.1,
        challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.val.2.state.current,
        challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model)
          (Cross.Programme.continueFrom (Native.Authority.programme model)
            (RawAuthority.inheritedChallenge model input cut nextRival nextRaw active record)
            (Cut.start model.source cut) (Cut.horizon model.source input cut)).state.current)) = _
  apply List.map_congr_left
  intro record _
  exact congrArg (fun image => (challengeImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.val.1,
    challengeStateImage model.source.code (Native.Authority.programme model) (Native.Authority.sourceIndex model) record.val.2.state.current,image))
    (original_challenge_lifecycle model input cut raw nextRaw rival nextRival observed active record).state

include observed active in
theorem complete_candidate_challenge_manifest :
    (RawAuthority.manifest model input cut nextRival nextRaw active).candidateChallenges =
      (RawAuthority.manifest model input cut rival raw active).candidateChallenges :=
  LocalLifecycle.census_images model.source.code (Native.Authority.programme model)
    (inputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut rival raw))
    (nextInputs := Native.Authority.sourceIndex (RawAuthority.candidate model input cut nextRival nextRaw))
    (Cut.finish model.source input cut) rfl
    (observed)
    (Cut.finish model.source input cut) (Nat.le_refl _)


include observed active in
theorem original_grant_lifecycle (record : RawAuthority.GrantAtArrival model cut) :
    grantImage (RawAuthority.candidate model input cut nextRival nextRaw)
      record.val.1.val (RawAuthority.terminalDepth model input cut)
      (Native.Authority.traceGrant _ _ _ (RawAuthority.migratedGrant model input cut nextRival nextRaw active record)) =
    grantImage (RawAuthority.candidate model input cut rival raw) record.val.1.val (RawAuthority.terminalDepth model input cut)
      (Native.Authority.traceGrant _ _ _ (RawAuthority.migratedGrant model input cut rival raw active record)) := by
  have newItems := RawAuthority.migrated_grant_keeps_both_original_signature_items model input cut nextRival nextRaw active record
  have oldItems := RawAuthority.migrated_grant_keeps_both_original_signature_items model input cut rival raw active record
  have items := And.intro (newItems.1.trans oldItems.1.symm) (newItems.2.trans oldItems.2.symm)
  have election := (RawAuthority.migrated_grant_keeps_the_original_election model input cut nextRival nextRaw active record).trans
      (RawAuthority.migrated_grant_keeps_the_original_election model input cut rival raw active record).symm
  have initial : Mandate.Lifecycle.Observed.initialState model.base model.scope
      (Native.Authority.currentAt (RawAuthority.candidate model input cut nextRival nextRaw))
      (Native.Authority.wordAt (RawAuthority.candidate model input cut nextRival nextRaw))
      record.val.1.val (RawAuthority.migratedGrant model input cut nextRival nextRaw active record) =
    Mandate.Lifecycle.Observed.initialState model.base model.scope
      (Native.Authority.currentAt (RawAuthority.candidate model input cut rival raw))
      (Native.Authority.wordAt (RawAuthority.candidate model input cut rival raw)) record.val.1.val
      (RawAuthority.migratedGrant model input cut rival raw active record) := by
    change (Election.mandateAdmissionEdge Mandate.Grant.lineageCompiler _).target = _
    rw [election]
    rfl
  have index := congrArg ExecutionItem.index items.2
  have state := Mandate.Lifecycle.Observed.through_state_congr (RawAuthority.terminalDepth model input cut) index initial
    (current model input cut raw nextRaw rival nextRival observed)
    (word model input cut raw nextRaw rival nextRival observed)
  have final := Mandate.Lifecycle.Observed.History.obligation_eq_of_state_eq _ _ state
  have history := grant_through_images_congr model.source.code (RawAuthority.terminalDepth model input cut) index initial
    (current model input cut raw nextRaw rival nextRival observed)
    (word model input cut raw nextRaw rival nextRival observed)
  have original := congrArg (Election.mandateObligation (Mandate.Grant.lineageCompiler (Party := Party) (Port := Port))) election
  apply (GrantImage.mk.injEq ..).mpr
  exact ⟨rfl,congrArg (itemImage model.source.code) items.1,congrArg (itemImage model.source.code) items.2,
    congrArg grantObligationImage original,congrArg grantObligationImage final,history⟩

include observed active in
theorem original_grant_manifest :
    (RawAuthority.manifest model input cut nextRival nextRaw active).originalGrants =
      (RawAuthority.manifest model input cut rival raw active).originalGrants := by
  simp only [RawAuthority.manifest,RawAuthority.grantContinuations,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro record _
  exact congrArg (fun image => (grantImage model record.val.1.val _ record.val.2,image))
    (original_grant_lifecycle model input cut raw nextRaw rival nextRival observed active record)

include observed active in
theorem every_world_and_actual_instruction_is_preserved :
    (RawAuthority.manifest model input cut nextRival nextRaw active).worlds =
      (RawAuthority.manifest model input cut rival raw active).worlds := by
  apply List.map_congr_left
  intro ordinal member
  exact Native.Coupling.History.occurrence_image model.source.code
    (RawAuthority.candidate model input cut rival raw).source.input
    (RawAuthority.candidate model input cut nextRival nextRaw).source.input
    rfl rfl (Cut.finish model.source input cut)
    (observed)
    ordinal (List.mem_range.mp member)

include observed active in
/-- Every original and newborn responsibility is read from its own actual native history. -/
theorem the_complete_raw_native_manifest_is_preserved :
    RawAuthority.manifest model input cut nextRival nextRaw active =
      RawAuthority.manifest model input cut rival raw active := by
  apply (Manifest.mk.injEq ..).mpr
  exact ⟨every_world_and_actual_instruction_is_preserved model input cut raw nextRaw rival nextRival observed active,
    original_grant_manifest model input cut raw nextRaw rival nextRival observed active,
    original_challenge_manifest model input cut raw nextRaw rival nextRival observed active,
    complete_grant_census model input cut raw nextRaw rival nextRival observed,
    complete_candidate_challenge_manifest model input cut raw nextRaw rival nextRival observed active⟩


end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Transport

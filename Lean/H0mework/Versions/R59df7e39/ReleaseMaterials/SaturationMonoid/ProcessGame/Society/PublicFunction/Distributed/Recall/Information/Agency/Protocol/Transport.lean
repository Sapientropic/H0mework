import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Replanning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Transport

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

private abbrev run (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) (n : Nat) :=
  Residual.run code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val)
    ⟨Cursor.controller cursor protocol rival,cursor.entry.budget⟩ (Residual.seed cursor.source cursor.entry cursor.cut) n

private theorem run_length (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code) (n : Nat) :
    (run cursor protocol rival n).history.length = cursor.source.history.length+1+cursor.cut+n := by
  have lengthAt : ∀ k, (cursor.source.feedbackState cursor.entry k).history.length = cursor.source.history.length+1+k := by
    intro k
    induction k with
    | zero => simp [Machine.feedbackState,Machine.feedbackInitial]
    | succ k ih =>
      change (Reaction.Feedback.advance code _ _ _).history.length = _
      rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
      omega
  induction n with
  | zero => exact lengthAt cursor.cut
  | succ n ih =>
    change (Reaction.Feedback.advance code _ _ _).history.length = _
    rw [history_keeps_every_actual_word,List.length_append,List.length_singleton,ih]
    omega

private theorem body_at_feedback (cursor : Cursor code) (protocol : Rule code) (rival : Opponent code)
    (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument) (n : Nat)
    (rounds : current.round = code.initial.round+(cursor.source.history.length+2+(cursor.cut+n))) :
    (Cursor.target cursor protocol rival).body current =
      word code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val n)
        ⟨Cursor.controller cursor protocol rival,cursor.entry.budget⟩ (run cursor protocol rival n) := by
  unfold Machine.body
  rw [rounds]
  have address : code.initial.round+(cursor.source.history.length+2+(cursor.cut+n))-code.initial.round-1 =
      cursor.source.history.length+1+(cursor.cut+n) := by omega
  rw [address,List.getElem?_eq_none (by dsimp only [Cursor.target,Future.target,Execution.target];omega),
    if_pos (by dsimp only [Cursor.target,Future.target,Execution.target];omega)]
  simp only []
  rw [show cursor.source.history.length+1+(cursor.cut+n)-(Cursor.target cursor protocol rival).history.length-1 =
    cursor.cut+n by change cursor.source.history.length+1+(cursor.cut+n)-cursor.source.history.length-1 = _;omega]
  change word code ((Cursor.target cursor protocol rival).feedbackPolicy (cursor.cut+n))
    (Cursor.targetInput cursor protocol rival)
    ((Cursor.target cursor protocol rival).feedbackState (Cursor.targetInput cursor protocol rival) (cursor.cut+n)) = _
  have policy := Execution.policy_at
    {cursor.source with feedback? := some (Cursor.targetInput cursor protocol rival)} cursor.cut
    (term cursor.source cursor.entry cursor.cut protocol).val n
  change (Cursor.target cursor protocol rival).feedbackPolicy (cursor.cut+n) =
    Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut protocol).val n at policy
  rw [policy,Future.the_whole_future_run_is_the_actual_state]
  simp only [word,decision,if_neg (show ¬(run cursor protocol rival n).history.length <
    cursor.source.history.length+1+cursor.cut by rw [run_length];omega)]

variable (cursor : Cursor code) (installed : Rule code) (environment : Opponent code)

private theorem old_runs (n : Nat) :
    run cursor installed (finiteRival cursor environment) n = run cursor installed environment n := by
  have same := one_original_external_table_preserves_every_actual_ordinal_state cursor installed environment n
  rw [Future.the_whole_future_run_is_the_actual_state,Future.the_whole_future_run_is_the_actual_state] at same
  exact same

private theorem old_words (n : Nat) :
    word code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut installed).val n)
        ⟨Cursor.controller cursor installed (finiteRival cursor environment),cursor.entry.budget⟩
        (run cursor installed (finiteRival cursor environment) n) =
      word code (Residual.scheduleAt cursor.source cursor.cut (term cursor.source cursor.entry cursor.cut installed).val n)
        ⟨Cursor.controller cursor installed environment,cursor.entry.budget⟩ (run cursor installed environment n) := by
  have words := congrArg State.history (old_runs cursor installed environment (n+1))
  simp only [run,Residual.run,history_keeps_every_actual_word] at words
  have same := old_runs cursor installed environment n
  dsimp only [run] at same
  rw [same] at words
  simpa only [run,same] using List.singleton_inj.mp (List.append_cancel_left words)

/-- Equality holds for the entire emitter, including currents outside the visited prefix. -/
theorem the_original_finite_table_preserves_the_complete_emitter :
    (Cursor.target cursor installed (finiteRival cursor environment)).body =
      (Cursor.target cursor installed environment).body := by
  funext current
  by_cases earlier : current.round-code.initial.round-1 < cursor.source.history.length+1+cursor.cut
  · exact (Future.earlier_body cursor.source cursor.entry cursor.cut
      (Cursor.controller cursor installed (finiteRival cursor environment))
      (term cursor.source cursor.entry cursor.cut installed).val rfl current earlier).trans
        (Future.earlier_body cursor.source cursor.entry cursor.cut (Cursor.controller cursor installed environment)
          (term cursor.source cursor.entry cursor.cut installed).val rfl current earlier).symm
  · let n := current.round-code.initial.round-(cursor.source.history.length+2+cursor.cut)
    have rounds : current.round = code.initial.round+(cursor.source.history.length+2+(cursor.cut+n)) := by
      have length : cursor.source.history.length = cursor.history.length := rfl
      dsimp only [n,Cursor.source]
      omega
    rw [body_at_feedback cursor installed (finiteRival cursor environment) current n rounds,
      body_at_feedback cursor installed environment current n rounds]
    exact old_words cursor installed environment n

theorem the_original_finite_table_preserves_the_complete_programme_input :
    (Cursor.target cursor installed (finiteRival cursor environment)).input =
      (Cursor.target cursor installed environment).input := by
  have same := the_original_finite_table_preserves_the_complete_emitter cursor installed environment
  have reports : (Cursor.target cursor installed (finiteRival cursor environment)).report =
      (Cursor.target cursor installed environment).report := by
    funext current
    exact congrArg (ProgrammeSource.ProgrammeReport.original current) (congrFun same current)
  simp only [Machine.input,same,reports]

abbrev representative := cursor.after installed (finiteRival cursor environment)
abbrev actual := cursor.after installed environment

variable (protocol : Rule code) (rival : Opponent code)

theorem the_next_seed_is_its_actual_unspent_state :
    (representative cursor installed environment).source.feedbackState
        (representative cursor installed environment).entry (cursor.cut+1) =
      (actual cursor installed environment).source.feedbackState
        (actual cursor installed environment).entry (cursor.cut+1) :=
  one_original_external_table_preserves_every_actual_ordinal_state cursor installed environment 1

private theorem next_term :
    (term (representative cursor installed environment).source (representative cursor installed environment).entry
        (cursor.cut+1) protocol).val =
      (term (actual cursor installed environment).source (actual cursor installed environment).entry
        (cursor.cut+1) protocol).val := by
  exact congrArg (fun state : State code => List.replicate state.remaining (some protocol.work.val))
    (the_next_seed_is_its_actual_unspent_state cursor installed environment)

private theorem inherited_policy (n : Nat) :
    (representative cursor installed environment).source.feedbackPolicy (cursor.cut+(1+n)) =
      (actual cursor installed environment).source.feedbackPolicy (cursor.cut+(1+n)) := by
  have left := Execution.policy_at
    {cursor.source with feedback? := some (Cursor.targetInput cursor installed (finiteRival cursor environment))}
    cursor.cut (term cursor.source cursor.entry cursor.cut installed).val (1+n)
  have right := Execution.policy_at
    {cursor.source with feedback? := some (Cursor.targetInput cursor installed environment)}
    cursor.cut (term cursor.source cursor.entry cursor.cut installed).val (1+n)
  exact left.trans right.symm

private theorem next_schedule :
    Residual.scheduleAt (representative cursor installed environment).source (cursor.cut+1)
        (term (representative cursor installed environment).source (representative cursor installed environment).entry
          (cursor.cut+1) protocol).val =
      Residual.scheduleAt (actual cursor installed environment).source (cursor.cut+1)
        (term (actual cursor installed environment).source (actual cursor installed environment).entry
          (cursor.cut+1) protocol).val := by
  funext n
  unfold Residual.scheduleAt
  rw [next_term]
  rw [show cursor.cut+1+n = cursor.cut+(1+n) by omega,inherited_policy]

private theorem next_runs (n : Nat) :
    run (representative cursor installed environment) protocol rival n =
      run (actual cursor installed environment) protocol rival n := by
  change Residual.run code
      (Residual.scheduleAt (representative cursor installed environment).source (cursor.cut+1)
        (term (representative cursor installed environment).source (representative cursor installed environment).entry
          (cursor.cut+1) protocol).val)
      ⟨driver code cursor.ownerStart protocol rival,cursor.entry.budget⟩
      ((representative cursor installed environment).source.feedbackState
        (representative cursor installed environment).entry (cursor.cut+1)) n =
    Residual.run code
      (Residual.scheduleAt (actual cursor installed environment).source (cursor.cut+1)
        (term (actual cursor installed environment).source (actual cursor installed environment).entry
          (cursor.cut+1) protocol).val)
      ⟨driver code cursor.ownerStart protocol rival,cursor.entry.budget⟩
      ((actual cursor installed environment).source.feedbackState
        (actual cursor installed environment).entry (cursor.cut+1)) n
  rw [next_schedule,the_next_seed_is_its_actual_unspent_state]

theorem the_new_rule_has_the_same_complete_actual_feedback_state (n : Nat) :
    (Cursor.target (representative cursor installed environment) protocol rival).feedbackState
        (Cursor.targetInput (representative cursor installed environment) protocol rival) (cursor.cut+1+n) =
      (Cursor.target (actual cursor installed environment) protocol rival).feedbackState
        (Cursor.targetInput (actual cursor installed environment) protocol rival) (cursor.cut+1+n) := by
  have left := Future.the_whole_future_run_is_the_actual_state
    (representative cursor installed environment).source (representative cursor installed environment).entry
    (representative cursor installed environment).cut (Cursor.controller (representative cursor installed environment) protocol rival)
    (term (representative cursor installed environment).source (representative cursor installed environment).entry
      (representative cursor installed environment).cut protocol).val n
  have right := Future.the_whole_future_run_is_the_actual_state
    (actual cursor installed environment).source (actual cursor installed environment).entry
    (actual cursor installed environment).cut (Cursor.controller (actual cursor installed environment) protocol rival)
    (term (actual cursor installed environment).source (actual cursor installed environment).entry
      (actual cursor installed environment).cut protocol).val n
  exact left.trans ((next_runs cursor installed environment protocol rival n).trans right.symm)

private theorem next_words (n : Nat) :
    word code (Residual.scheduleAt (representative cursor installed environment).source (cursor.cut+1)
        (term (representative cursor installed environment).source (representative cursor installed environment).entry
          (cursor.cut+1) protocol).val n)
        ⟨Cursor.controller (representative cursor installed environment) protocol rival,
          (representative cursor installed environment).entry.budget⟩
        (run (representative cursor installed environment) protocol rival n) =
      word code (Residual.scheduleAt (actual cursor installed environment).source (cursor.cut+1)
        (term (actual cursor installed environment).source (actual cursor installed environment).entry
          (cursor.cut+1) protocol).val n)
        ⟨Cursor.controller (actual cursor installed environment) protocol rival,
          (actual cursor installed environment).entry.budget⟩
        (run (actual cursor installed environment) protocol rival n) := by
  rw [next_schedule,next_runs]
  rfl

/-- Replanning preserves the entire actual emitter for the same new rule and external rival. -/
theorem the_new_rule_preserves_the_complete_actual_emitter :
    (Cursor.target (representative cursor installed environment) protocol rival).body =
      (Cursor.target (actual cursor installed environment) protocol rival).body := by
  funext current
  by_cases earlier : current.round-code.initial.round-1 < cursor.source.history.length+1+(cursor.cut+1)
  · have left := Future.earlier_body (representative cursor installed environment).source
      (representative cursor installed environment).entry (cursor.cut+1)
      (Cursor.controller (representative cursor installed environment) protocol rival)
      (term (representative cursor installed environment).source (representative cursor installed environment).entry
        (cursor.cut+1) protocol).val rfl current earlier
    have right := Future.earlier_body (actual cursor installed environment).source
      (actual cursor installed environment).entry (cursor.cut+1)
      (Cursor.controller (actual cursor installed environment) protocol rival)
      (term (actual cursor installed environment).source (actual cursor installed environment).entry
        (cursor.cut+1) protocol).val rfl current earlier
    exact left.trans ((congrFun (the_original_finite_table_preserves_the_complete_emitter
      cursor installed environment) current).trans right.symm)
  · let n := current.round-code.initial.round-(cursor.source.history.length+2+(cursor.cut+1))
    have rounds : current.round = code.initial.round+(cursor.source.history.length+2+(cursor.cut+1+n)) := by
      have length : cursor.source.history.length = cursor.history.length := rfl
      dsimp only [n,Cursor.source]
      omega
    rw [body_at_feedback (representative cursor installed environment) protocol rival current n rounds,
      body_at_feedback (actual cursor installed environment) protocol rival current n rounds]
    exact next_words cursor installed environment protocol rival n

theorem the_new_rule_preserves_the_complete_actual_programme_input :
    (Cursor.target (representative cursor installed environment) protocol rival).input =
      (Cursor.target (actual cursor installed environment) protocol rival).input := by
  have same := the_new_rule_preserves_the_complete_actual_emitter cursor installed environment protocol rival
  have reports : (Cursor.target (representative cursor installed environment) protocol rival).report =
      (Cursor.target (actual cursor installed environment) protocol rival).report := by
    funext current
    exact congrArg (ProgrammeSource.ProgrammeReport.original current) (congrFun same current)
  simp only [Machine.input,same,reports]

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
  (point : Cursor model.source.code) (old new : Rule model.source.code)
  (pastRival futureRival : Opponent model.source.code)

private abbrev finiteBound := Replanning.native model (representative point old pastRival)
private abbrev actualBound := Replanning.native model (actual point old pastRival)
private abbrev finiteTerm := term (representative point old pastRival).source
  (representative point old pastRival).entry (point.cut+1) new
private abbrev actualTerm := term (actual point old pastRival).source
  (actual point old pastRival).entry (point.cut+1) new
private abbrev finiteCandidate := Authority.candidate (finiteBound model point old pastRival)
  (representative point old pastRival).entry (point.cut+1)
  (Cursor.controller (representative point old pastRival) new futureRival) (finiteTerm model point old new pastRival)
private abbrev actualCandidate := Authority.candidate (actualBound model point old pastRival)
  (actual point old pastRival).entry (point.cut+1)
  (Cursor.controller (actual point old pastRival) new futureRival) (actualTerm model point old new pastRival)

private theorem same_finish :
    Cut.finish (representative point old pastRival).source (representative point old pastRival).entry (point.cut+1) =
      Cut.finish (actual point old pastRival).source (actual point old pastRival).entry (point.cut+1) := by
  exact congrArg (fun state : State model.source.code => point.source.history.length+2+(point.cut+1)+state.remaining)
    (the_next_seed_is_its_actual_unspent_state point old pastRival)

theorem the_new_rule_preserves_the_full_candidate_challenge_census :
    (Replanning.actualEvaluation model (representative point old pastRival) new futureRival).native.candidateChallenges =
      (Replanning.actualEvaluation model (actual point old pastRival) new futureRival).native.candidateChallenges := by
  let family := Native.Authority.programme model
  let first := Native.Authority.sourceIndex (actualCandidate model point old new pastRival futureRival)
  let second := Native.Authority.sourceIndex (finiteCandidate model point old new pastRival futureRival)
  have inputs : Mandate.Challenge.I family second = Mandate.Challenge.I family first :=
    the_new_rule_preserves_the_complete_actual_programme_input point old pastRival new futureRival
  let count := Cut.finish (actual point old pastRival).source (actual point old pastRival).entry (point.cut+1)
  have generated := Authority.Trace.LocalLifecycle.census_images model.source.code family
    (inputs := first) (nextInputs := second) count
    (congrArg ProgrammeSource.Input.initial inputs)
    (fun ordinal _ => by rw [inputs]) count (Nat.le_refl _)
  change ((Native.Authority.challengesAt (finiteCandidate model point old new pastRival futureRival)
    (Cut.finish (representative point old pastRival).source (representative point old pastRival).entry (point.cut+1))).map
      (fun record => (Authority.Trace.challengeImage model.source.code family second record.1,
        Authority.Trace.challengeStateImage model.source.code family second record.2.state.current))) = _
  rw [same_finish]
  exact generated

private theorem candidate_currents :
    Native.Authority.currentAt (finiteCandidate model point old new pastRival futureRival) =
      Native.Authority.currentAt (actualCandidate model point old new pastRival futureRival) := by
  funext ordinal
  have same : (finiteCandidate model point old new pastRival futureRival).source.input =
      (actualCandidate model point old new pastRival futureRival).source.input :=
    the_new_rule_preserves_the_complete_actual_programme_input point old pastRival new futureRival
  exact congrArg (fun input : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument =>
    ((ProgrammeLiving.projectionLaw input).project .execution
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (ordinal+1)).current) ()).before) same

private theorem candidate_words :
    Native.Authority.wordAt (finiteCandidate model point old new pastRival futureRival) =
      Native.Authority.wordAt (actualCandidate model point old new pastRival futureRival) := by
  funext ordinal
  have same : (finiteCandidate model point old new pastRival futureRival).source.input =
      (actualCandidate model point old new pastRival futureRival).source.input :=
    the_new_rule_preserves_the_complete_actual_programme_input point old pastRival new futureRival
  exact congrArg (fun input : ProgrammeSource.Input Party Good Port (Mandate.State Party Technology) Instrument =>
    ((ProgrammeLiving.projectionLaw input).project .execution
      (ProgrammeSource.emitted input (ProgrammeHistory.visitAt input (ordinal+1)).current) ()).submitted) same

private def grantCensus (basis : Code Party Good Port (Mandate.State Party Technology) Instrument)
    (base : RawLaw Party Good Port Technology Instrument) (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port))
    (last : Nat) (currentAt : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (wordAt : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument) :
    List (Authority.Trace.GrantImage Party Good Port Technology Instrument) :=
  (List.finRange (last+1)).flatMap fun birth =>
    (Mandate.grantsAt base scope (currentAt birth.val) (wordAt birth.val)).map fun grant =>
      let history := Mandate.Lifecycle.Observed.through (base := base) (scope := scope)
        (currentAt := currentAt) (wordAt := wordAt) (birth := birth.val) (grant := grant) last
      ⟨birth.val,Authority.Trace.itemImage basis grant.proposal.item.val,
        Authority.Trace.itemImage basis grant.acceptance.item.val,
        Authority.Trace.grantObligationImage (Mandate.Lifecycle.original base scope currentAt wordAt birth.val grant),
        Authority.Trace.grantObligationImage history.obligation,Authority.Trace.grantHistoryImage basis history⟩

private theorem grantCensus_factor
    (bound : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (last : Nat) :
    (Native.Authority.recordsAt bound last).map (fun record =>
      Authority.Trace.grantImage bound record.1.val last record.2) =
    grantCensus bound.source.code bound.base bound.scope last
      (Native.Authority.currentAt bound) (Native.Authority.wordAt bound) := by
  simp only [Native.Authority.recordsAt,List.map_flatMap,List.map_map,Function.comp_def,
    Authority.Trace.grantImage,Native.Authority.traceGrant,grantCensus,Mandate.admitGrant]

theorem the_new_rule_preserves_the_full_candidate_grant_census :
    (Replanning.actualEvaluation model (representative point old pastRival) new futureRival).native.candidateGrants =
      (Replanning.actualEvaluation model (actual point old pastRival) new futureRival).native.candidateGrants := by
  change ((Native.Authority.recordsAt (finiteCandidate model point old new pastRival futureRival)
    (Authority.terminalDepth (finiteBound model point old pastRival) (representative point old pastRival).entry (point.cut+1))).map
    (fun record => Authority.Trace.grantImage (finiteCandidate model point old new pastRival futureRival) record.1.val _ record.2)) =
    ((Native.Authority.recordsAt (actualCandidate model point old new pastRival futureRival)
    (Authority.terminalDepth (actualBound model point old pastRival) (actual point old pastRival).entry (point.cut+1))).map
    (fun record => Authority.Trace.grantImage (actualCandidate model point old new pastRival futureRival) record.1.val _ record.2))
  rw [grantCensus_factor,grantCensus_factor]
  have finish := same_finish model point old pastRival
  dsimp only [Authority.terminalDepth]
  rw [finish]
  exact congrArg₂ _ (candidate_currents model point old new pastRival futureRival)
    (candidate_words model point old new pastRival futureRival)

private theorem complete_finance (ordinal : Nat) :
    Native.Coupling.Match model.source.code
      (Cursor.target (actual point old pastRival) new futureRival).input
      (Cursor.target (representative point old pastRival) new futureRival).input
      (Financial.accountAt (Cursor.target (actual point old pastRival) new futureRival).input ordinal)
      (Financial.accountAt (Cursor.target (representative point old pastRival) new futureRival).input ordinal) := by
  let first := Cursor.target (actual point old pastRival) new futureRival
  let second := Cursor.target (representative point old pastRival) new futureRival
  have same : second.input = first.input :=
    the_new_rule_preserves_the_complete_actual_programme_input point old pastRival new futureRival
  exact Native.Coupling.History.complete_accounts model.source.code first.input second.input rfl rfl ordinal
    (fun index _ => congrArg (fun input => ProgrammeSource.rawEvent input
      (ProgrammeHistory.visitAt first.input index).current) same)
    first.body second.body rfl rfl ordinal (Nat.le_refl _)

structure SourceMatch (next : Cursor model.source.code) : Prop where
  legacy : Covers point old pastRival next
  original_input : next.source.input = (actual point old pastRival).source.input
  renewed_input : ∀ (rule : Rule model.source.code) (rival : Opponent model.source.code),
    (Cursor.target next rule rival).input = (Cursor.target (actual point old pastRival) rule rival).input
  renewed_grants : ∀ (rule : Rule model.source.code) (rival : Opponent model.source.code),
    (Replanning.actualEvaluation model next rule rival).native.candidateGrants =
      (Replanning.actualEvaluation model (actual point old pastRival) rule rival).native.candidateGrants
  renewed_challenges : ∀ (rule : Rule model.source.code) (rival : Opponent model.source.code),
    (Replanning.actualEvaluation model next rule rival).native.candidateChallenges =
      (Replanning.actualEvaluation model (actual point old pastRival) rule rival).native.candidateChallenges
  renewed_finance : ∀ (rule : Rule model.source.code) (rival : Opponent model.source.code) (ordinal : Nat),
    Native.Coupling.Match model.source.code (Cursor.target (actual point old pastRival) rule rival).input
      (Cursor.target next rule rival).input
      (Financial.accountAt (Cursor.target (actual point old pastRival) rule rival).input ordinal)
      (Financial.accountAt (Cursor.target next rule rival).input ordinal)

theorem the_public_representative_preserves_all_future_protocol_sources :
    SourceMatch model point old pastRival (representative point old pastRival) := by
  exact {
    legacy := ⟨rfl,rfl,one_original_external_table_preserves_every_actual_ordinal_state point old pastRival,
      one_external_table_preserves_the_complete_native_financial_history point old pastRival⟩
    original_input := the_original_finite_table_preserves_the_complete_programme_input point old pastRival
    renewed_input := the_new_rule_preserves_the_complete_actual_programme_input point old pastRival
    renewed_grants := fun rule rival => the_new_rule_preserves_the_full_candidate_grant_census model point old rule pastRival rival
    renewed_challenges := fun rule rival => the_new_rule_preserves_the_full_candidate_challenge_census model point old rule pastRival rival
    renewed_finance := fun rule rival => complete_finance model point old rule pastRival rival }

theorem one_public_successor_preserves_all_future_protocol_sources
    (domain : List (Cursor model.source.code)) (inside : point ∈ domain) :
    ∃ next ∈ advance model.source.code domain old, SourceMatch model point old pastRival next := by
  refine ⟨representative point old pastRival,
    every_generated_table_produces_its_own_successor model.source.code domain old point inside
      (externalTable point pastRival) (Residual.restriction_is_generated _ _ _ pastRival),?_⟩
  exact the_public_representative_preserves_all_future_protocol_sources model point old pastRival

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation.Transport

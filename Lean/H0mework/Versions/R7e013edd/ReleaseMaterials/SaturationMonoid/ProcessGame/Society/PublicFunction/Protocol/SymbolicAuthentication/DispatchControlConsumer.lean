import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ActualRoundNetworkSource (Network code start protocol window Subject)
open DispatchControlSource
variable (net : Network)

abbrev Related (left right : Node net) :=
  EnvelopeObservation.Compatible (start net) left.stages right.stages ∧ left.omissions = right.omissions

theorem related_states (left right : Node net) (one : Valid net left) (two : Valid net right)
    (same : Related net left right) : left.state = right.state :=
  ActualRoundNetworkConsumer.related_states net left.toNode right.toNode one two same.1

theorem related_cuts (left right : Node net) (one : Valid net left) (two : Valid net right)
    (same : Related net left right) : left.cursor.cut = right.cursor.cut := by
  rw [one.1,two.1]
  exact same.1.1.cut

theorem related_opportunities (left right : Node net) (one : Valid net left) (two : Valid net right)
    (same : Related net left right) : opportunity net left = opportunity net right := by
  have owners : left.cursor.ownerStart = right.cursor.ownerStart := by rw [one.1,two.1];exact same.1.1.ownerStart
  unfold opportunity StageTrace.capture
  rw [related_states net left right one two same,owners]

theorem related_spending (left right : Node net) (one : Valid net left) (two : Valid net right)
    (same : Related net left right) : spent net left = spent net right := by
  unfold spent
  rw [same.2,one.2.2,two.2.2,EnvelopeObservation.gap_equal (start net) same.1.2]

theorem related_controls (left right : Node net) (one : Valid net left) (two : Valid net right)
    (same : Related net left right) : controls net left = controls net right := by
  unfold controls
  rw [related_opportunities net left right one two same,related_spending net left right one two same]

theorem related_choices (left right : Node net) (one : Valid net left) (two : Valid net right)
    (same : Related net left right) : choices net left = choices net right := by
  have owners : left.cursor.ownerStart = right.cursor.ownerStart := by rw [one.1,two.1];exact same.1.1.ownerStart
  unfold choices
  rw [related_states net left right one two same,owners,related_spending net left right one two same]

theorem related_rules (left right : Node net) (one : Valid net left) (two : Valid net right)
    (same : Related net left right) (requested : Bool) : rule net left requested = rule net right requested := by
  unfold rule withholding
  rw [related_opportunities net left right one two same]

abbrev chosen (left right : Node net) (callback : Opponent (code net)) :=
  CausalLocalDomain.chosen (EventHistory.execute (start net) left.stages) (EventHistory.execute (start net) right.stages) callback

theorem chosen_is_actual (left right : Node net) (two : Valid net right)
    (same : Related net left right) (callback : Opponent (code net)) :
    chosen net left right callback = intake net right callback := by
  unfold chosen intake ActualRoundNetworkSource.intake
  rw [EnvelopeObservation.chosen_is_the_actual_intake (start net) _ _ same.1,← two.1]

theorem compact_step (left right : Node net) (one : Valid net left) (two : Valid net right)
    (same : Related net left right) (requested : Bool) (callback : Opponent (code net)) :
    Related net (step net left requested (EventStep.fixed (chosen net left right callback)))
      (step net right requested callback) := by
  have rules := related_rules net left right one two same requested
  refine ⟨?_,?_⟩
  · change EnvelopeObservation.Compatible (start net)
      (left.stages ++ [(rule net left requested,_)]) (right.stages ++ [(rule net right requested,_)])
    rw [← rules]
    exact EnvelopeObservation.compact_extension (start net) _ _ same.1 (rule net left requested) callback
  · change (if withholding net left requested then left.omissions ++ [left.cursor.cut] else left.omissions) =
      (if withholding net right requested then right.omissions ++ [right.cursor.cut] else right.omissions)
    unfold withholding
    rw [related_opportunities net left right one two same,same.2,related_cuts net left right one two same]

theorem every_compliant_control_and_callback_has_a_generated_actual_branch
    (control : Controller net) (callbacks : Nat → Opponent (code net)) (n : Nat)
    (within : Within net control callbacks n) :
    ∃ node ∈ generate net n, Related net node (actual net control callbacks n) := by
  induction n with
  | zero => exact ⟨initial net,List.mem_singleton_self _,⟨EventStep.matches_self _,EnvelopeObservation.reflexive _⟩,rfl⟩
  | succ n prior =>
    obtain ⟨node,member,same⟩ := prior (fun index bounded => within index (by omega))
    have one := generated_valid net n node member
    have two := actual_valid net control callbacks n
    let target := actual net control callbacks n
    let requested := control target.cursor.cut target.state
    let callback := callbacks target.cursor.cut
    have permitted : requested ∈ controls net node := by
      rw [related_controls net node target one two same]
      exact (within n (by omega)).1
    have allowed : chosen net node target callback ∈ choices net node := by
      rw [related_choices net node target one two same,chosen_is_actual net node target two same]
      exact (within n (by omega)).2
    exact ⟨step net node requested (EventStep.fixed (chosen net node target callback)),
      List.mem_flatMap.mpr ⟨node,member,List.mem_flatMap.mpr ⟨requested,permitted,List.mem_map.mpr ⟨_,allowed,rfl⟩⟩⟩,
      compact_step net node target one two same requested callback⟩

theorem related_results (left right : Node net) (same : Related net left right) : result net left = result net right :=
  ActualRoundNetworkConsumer.related_results net left.toNode right.toNode same.1

private theorem completion_checks (subject : Subject net) (made : completion net = some subject) :
    ∀ node ∈ generate net (window net), result net node = .decided true subject := by
  unfold completion at made
  cases verdict : assess net with
  | unresolved missing => simp only [verdict] at made;cases made
  | completed original origin checked =>
    simp only [verdict] at made
    cases Option.some.inj made
    exact checked
  | obstructed original origin node member failed => simp only [verdict] at made;cases made

theorem computed_completion_covers_arbitrary_compliant_local_and_network_controls
    (subject : Subject net) (made : completion net = some subject)
    (control : Controller net) (callbacks : Nat → Opponent (code net))
    (within : Within net control callbacks (window net)) :
    result net (actual net control callbacks (window net)) = .decided true subject := by
  obtain ⟨node,member,same⟩ := every_compliant_control_and_callback_has_a_generated_actual_branch net control callbacks _ within
  exact (related_results net node _ same).symm.trans (completion_checks net subject made node member)

theorem computed_obstruction_is_a_valid_executable_source_branch
    (node : Node net) (made : obstruction net = some node) :
    ∃ subject, ActualRoundNetworkSource.expected net = some subject ∧
      node ∈ generate net (window net) ∧ Valid net node ∧ result net node ≠ .decided true subject := by
  unfold obstruction at made
  cases verdict : assess net with
  | unresolved missing => simp only [verdict] at made;cases made
  | completed original origin checked => simp only [verdict] at made;cases made
  | obstructed original origin branch member failed =>
    simp only [verdict] at made
    cases Option.some.inj made
    exact ⟨original,origin,member,generated_valid net _ _ member,failed⟩

theorem actual_trace_is_source_generated (attempt : Attempt) : Valid attempt.network attempt.trace := by
  rw [attempt.trace_exact]
  exact actual_valid _ _ _ _

theorem reentry_retains_the_literal_source_cut_and_actual_current (attempt : Attempt) :
    (after attempt).model.source = attempt.trace.cursor.source ∧
      (after attempt).cut = attempt.trace.cursor.cut ∧
      RoundEpisodeSource.current (after attempt) = attempt.trace.state.current := by
  refine ⟨rfl,rfl,?_⟩
  have actual := attempt.trace.cursor.source.feedback_current_is_actual attempt.trace.cursor.entry rfl rfl attempt.trace.cursor.cut
  change attempt.trace.cursor.source.currentAt (attempt.trace.cursor.source.history.length+1+attempt.trace.cursor.cut+1) = _
  rw [show attempt.trace.cursor.source.history.length+1+attempt.trace.cursor.cut+1 =
    attempt.trace.cursor.source.history.length+2+attempt.trace.cursor.cut by omega,actual]
  exact (congrArg (fun state : Feedback.State (code attempt.network) => state.current) (actual_trace_is_source_generated attempt).2.1).symm

theorem actual_last_occurrence_consumes_its_own_native_ledger_and_next (attempt : Attempt) :
    RoundEpisodeConsumer.NativeConsumed (model attempt) (ordinal attempt) (disposition attempt) :=
  RoundEpisodeConsumer.native_generated_consumed _ _

theorem the_actual_next_keeps_all_legacy_attempts (state : State) (production feed : Bool) (settings : ActualRoundNetworkSource.Settings)
    (control : Controls) (callbacks : NetworkReentrySource.Callbacks) :
    (next state production feed settings control callbacks).legacy.evidence = state.legacy.evidence := by
  unfold next
  split <;> rfl

theorem the_actual_next_keeps_all_control_attempts (state : State) (production feed : Bool) (settings : ActualRoundNetworkSource.Settings)
    (control : Controls) (callbacks : NetworkReentrySource.Callbacks) :
    ∃ added, (next state production feed settings control callbacks).evidence = state.evidence ++ added := by
  unfold next
  split <;> simp
abbrev facade (control : Controller net) (callbacks : Nat → Opponent (code net)) :=
  let cursor := (actual net control callbacks (window net)).cursor
  Feedback.Runtime.facade cursor.source cursor.entry rfl rfl

def PaymentConsumed (subject : Subject net) (control : Controller net) (rivals : Nat → Opponent (code net)) : Prop :=
    let final := (actual net control rivals (window net)).cursor
    let runtime := (facade net control rivals).seed.advance (EventStep.boundary final)
    (∃ row ∈ (actual net control rivals (window net)).rows, ∃ item,
      item ∈ (Financial.inventoryAt final.source.input
        (ProgrammeHistory.visitAt final.source.input (EventStep.boundary row.cursor))).filterMap
        (Financial.InstructionOrigin.instruction? final.source.input) ∧
      (code net).law.Valid item.before item.request ∧ 0 < subject.2.amount ∧
      flowAt ((code net).law.actualDebit item.before item.request) subject.2.debtor subject.2.unit = subject.2.amount ∧
      flowAt ((code net).law.actualCredit item.before item.request) subject.2.creditor subject.2.unit = subject.2.amount ∧
      ((code net).law.step item.before item.request).claims subject.2.instrument subject.2.debtor subject.2.creditor =
        subject.2.priorClaim-subject.2.quantity) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade net control rivals).process.stateAt ((facade net control rivals).process.successor runtime.state)

theorem computed_completion_consumes_actual_payment_whole_ledger_and_next
    (subject : Subject net) (made : completion net = some subject)
    (control : Controller net) (rivals : Nat → Opponent (code net)) (within : Within net control rivals (window net)) :
    PaymentConsumed net subject control rivals := by
  have valid := actual_valid net control rivals (window net)
  have done := computed_completion_covers_arbitrary_compliant_local_and_network_controls net subject made control rivals within
  obtain ⟨row,inside,item,member,paid⟩ := StagePaymentQuorum.every_decision_consumes_actual_payment_effects
    (ActualRoundNetworkSource.vocabulary net) (start net) (ActualRoundNetworkSource.encoding net) (ActualRoundNetworkSource.reception net) (actual net control rivals (window net)).stages 0 (ActualRoundNetworkSource.scope net) net.settings.threshold true subject done
  have final := (actual net control rivals (window net)).cursor
  have native := StageTrace.final_financial_inventory_is_the_original_record_items (start net) (actual net control rivals (window net)).stages row inside
  rw [← valid.1] at native
  have rooted := (facade net control rivals).readoutAt_factorizes
    ((facade net control rivals).seed.advance (EventStep.boundary (actual net control rivals (window net)).cursor)) .feedback
  refine ⟨⟨row,by rwa [valid.2.2],item,?_,paid⟩,rooted.2.2.1,rooted.2.2.2.2⟩
  rw [native]
  exact member

theorem reentry_is_the_completed_native_next (attempt : Attempt) :
    RoundEpisodeSource.current (after attempt) = (code attempt.network).law.next
      ((model attempt).source.actualExecution (ordinal attempt)).before
      ((model attempt).source.actualExecution (ordinal attempt)).submitted := by
  have positive : 0 < MaterialRoundSource.depth (model attempt) attempt.trace.cursor.cut := by
    dsimp [MaterialRoundSource.depth,Machine.Continuation.depth]
    omega
  have next := (model attempt).source.next_is_actual (ordinal attempt)
  change (model attempt).source.currentAt (MaterialRoundSource.depth (model attempt) attempt.trace.cursor.cut+1) = _
  rw [show MaterialRoundSource.depth (model attempt) attempt.trace.cursor.cut+1 = ordinal attempt+2 by dsimp [ordinal];omega]
  exact next

theorem the_actual_next_keeps_all_original_archives (state : State) (production feed : Bool)
    (settings : ActualRoundNetworkSource.Settings) (control : Controls) (callbacks : NetworkReentrySource.Callbacks) :
    ∃ added, (next state production feed settings control callbacks).legacy.episode.archive = state.legacy.episode.archive ++ added := by
  let prepared := NetworkReentrySource.prepared state.legacy production feed
  have prior : ∃ added, prepared.archive = state.legacy.episode.archive ++ added := by
    exact ⟨[RoundEpisodeSource.Archive.native (DonorRegenerationSource.productionModel state.legacy.episode production)
      (MaterialRoundSource.depth state.legacy.episode.model state.legacy.episode.cut) (DonorRegenerationSource.disposition state.legacy.episode production)] ++
      [RoundEpisodeSource.Archive.native (UpstreamFeedSource.arrivalModel (DonorRegenerationSource.generated state.legacy.episode production) feed)
        (MaterialRoundSource.depth (DonorRegenerationSource.generated state.legacy.episode production).model (state.legacy.episode.cut+1))
        (UpstreamFeedSource.disposition (DonorRegenerationSource.generated state.legacy.episode production) feed)],
      by simp only [prepared,UpstreamFeedSource.arrived,DonorRegenerationSource.generated,List.append_assoc]⟩
  obtain ⟨old,sameOld⟩ := prior
  unfold next
  split
  · obtain ⟨fresh,sameNew⟩ := RoundEpisodeConsumer.each_actual_next_retains_every_old_archive_record prepared
      (RoundEpisodeSource.normal prepared (NetworkReentrySource.incoming state.legacy production feed))
    exact ⟨old ++ fresh,sameNew.trans (by rw [sameOld];simp only [List.append_assoc])⟩
  · rename_i network made
    have bound := NetworkReentryConsumer.admitted_network_uses_the_actual_prepared_state state.legacy production feed settings network made
    refine ⟨old ++ RoundEpisodeSource.nativeArchive network.state (RoundEpisodeSource.normal network.state network.raw) ++
      [.native (model (execute network (control network) (callbacks network))) (ordinal (execute network (control network) (callbacks network)))
        (disposition (execute network (control network) (callbacks network)))],?_⟩
    dsimp only [after,execute]
    rw [bound,sameOld]
    simp only [List.append_assoc]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DispatchControlConsumer

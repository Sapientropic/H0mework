import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueRuntime
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueControls

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information
open Distributed.Recall.Information.Agency.Protocol Continuation

abbrev foundation := AdmissionControls.foundation
abbrev model := AdmissionControls.model
abbrev code := AdmissionControls.code
abbrev start := AdmissionControls.start
abbrev pastStages := (AdmissionControls.stages .normal).take 5
abbrev current := EventHistory.execute start pastStages
def protocols (index : Nat) : Rule code := AdmissionControls.rule (index = 3) (index = 3)
abbrev vocabulary := AdmissionControls.vocabulary
abbrev encoding := AdmissionControls.encoding
abbrev law := AdmissionControls.law
abbrev slot := AdmissionControls.slot
abbrev full := StageQueueProgress.completeStages start pastStages protocols
abbrev observed := StageReception.run vocabulary encoding law start full 1 full.length
abbrev plan (threshold : Nat) := StageQueueProgress.windowPlan vocabulary AdmissionControls.base encoding law start pastStages protocols 1 slot threshold
abbrev decision (threshold : Nat) := AdmissionQuorum.produce AdmissionControls.base vocabulary encoding law start full 1 slot threshold

theorem the_nonzero_cursor_generates_its_own_bounded_queue_window :
    current.cut = 5 ∧ current.ownerStart = start.ownerStart ∧ StageQueue.horizon current = 6 ∧
      (StageQueue.stages current protocols (StageQueue.horizon current)).length = 6 ∧ full.length = 11 ∧
      (EventHistory.execute start full).cut = 11 ∧
      (EventHistory.execute start full).ownerStart = start.ownerStart ∧
      (StageReception.run vocabulary encoding law start pastStages 1 pastStages.length).receipts = [] ∧
      (observed.receipts) = AdmissionControls.expected.take 2 ∧ plan 2 = .ready true ∧ decision 2 = .decided true := by
  decide +kernel

theorem changing_owned_work_and_paid_equivocation_do_not_prevent_the_generated_completion :
    StageBudget.ledger vocabulary start full = [AdmissionControls.first, AdmissionControls.second, AdmissionControls.third] ∧
      StageBudget.evidenceKeys vocabulary start full = {0} ∧
      (StageQueue.row current protocols 3).submitted = [AdmissionControls.no] ∧
      plan 2 = .ready true ∧ decision 2 = .decided true := by
  decide +kernel

theorem an_independent_consumer_uses_the_general_finite_attempt_producer :
    ∃ index < StageQueue.horizon current, StageReception.delivered (StageQueue.row current protocols index) 0 = true :=
  StageQueue.the_source_window_generates_an_actual_delivery_attempt current protocols 0
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

abbrev restarted : Cursor code := {current with ownerStart := Distributed.Recall.Information.Agency.start current.source current.cut}
theorem restarting_the_owner_clock_substitutes_an_owned_send_for_the_real_external_delivery :
    StageReception.delivered (StageQueue.row current protocols 0) 0 = true ∧
      StageTransport.outgoing (StageQueue.row current protocols 0) = none ∧
      StageReception.delivered (StageTrace.material restarted (protocols 0) (StageQueue.environment current)) 0 = false ∧
      StageTransport.outgoing (StageTrace.material restarted (protocols 0) (StageQueue.environment current)) = some (0, 1) := by
  decide +kernel

def resetBaseline : Opponent code := fun history past frame => QueueScheduler.opponent code past.length history past frame
abbrev resetStages := pastStages ++ (List.range (StageQueue.horizon current)).map (fun index => (protocols index, resetBaseline))
abbrev noDeliveryStages : List (EventHistory.Stage (code := code)) :=
  pastStages ++ (List.range (StageQueue.horizon current)).map (fun index => (protocols index, fun _ _ _ => none))
theorem resetting_the_baseline_repeats_old_delivery_and_starves_the_next_packet :
    (StageReception.run vocabulary encoding {law with maxDelay := 10} start resetStages 1 resetStages.length).receipts = AdmissionControls.expected.take 1 ∧
      ((StageReception.run vocabulary encoding {law with maxDelay := 10} start resetStages 1 resetStages.length).audit[7]?).map
        (fun row => row.2.2) = some (.rejected .duplicate) ∧
      StageQueueProgress.plan vocabulary AdmissionControls.base encoding {law with maxDelay := 10} start resetStages 1 slot 2 = .blocked .insufficientReadySupport ∧
      AdmissionQuorum.produce AdmissionControls.base vocabulary encoding {law with maxDelay := 10} start resetStages 1 slot 2 = .blocked := by
  decide +kernel

abbrev lateLaw : StageReception.Law code := {law with maxDelay := 0}
abbrev staleLaw : StageReception.Law code := {law with scope := fun _ _ => ⟨1, 0, 0⟩}
abbrev forged : StageTransport.Encoding (code := code) := fun _ => some {AdmissionControls.first with actor := true}
theorem delivery_scope_timing_and_forgery_fail_before_a_ready_window_or_decision :
    StageQueueProgress.plan vocabulary AdmissionControls.base encoding law start noDeliveryStages 1 slot 2 = .blocked .insufficientReadySupport ∧
      (StageReception.run vocabulary encoding law start noDeliveryStages 1 noDeliveryStages.length).receipts = [] ∧
      StageQueueProgress.windowPlan vocabulary AdmissionControls.base encoding lateLaw start pastStages protocols 1 slot 2 = .blocked .insufficientReadySupport ∧
      ((StageReception.run vocabulary encoding lateLaw start full 1 full.length).audit[5]?).map (fun row => row.2.2) = some (.rejected .late) ∧
      StageQueueProgress.windowPlan vocabulary AdmissionControls.base encoding staleLaw start pastStages protocols 1 slot 2 = .blocked .insufficientReadySupport ∧
      ((StageReception.run vocabulary encoding staleLaw start full 1 full.length).audit[5]?).map (fun row => row.2.2) = some (.rejected .staleScope) ∧
      StageQueueProgress.windowPlan vocabulary AdmissionControls.base forged law start pastStages protocols 1 slot 2 = .blocked .insufficientReadySupport ∧
      AdmissionQuorum.produce AdmissionControls.base vocabulary forged law start full 1 slot 2 = .blocked := by
  decide +kernel

abbrev shortStart := EventHistory.ofOrigin model 6 AdmissionControls.origin
theorem insufficient_source_cuts_or_quorum_have_typed_blocked_branches :
    StageQueueProgress.windowPlan vocabulary AdmissionControls.base encoding law shortStart pastStages protocols 1 slot 2 = .blocked .insufficientCuts ∧
      plan 0 = .blocked .zeroThreshold ∧ plan 1 = .blocked .unsafeBudget ∧ plan 3 = .blocked .insufficientReadySupport ∧
      decision 0 = .blocked ∧ decision 1 = .blocked ∧ decision 3 = .blocked := by
  decide +kernel

abbrev poorBase := {AdmissionControls.base with
  initial := {AdmissionControls.base.initial with stock := fun party _ => if party then 100 else 5}}
abbrev poorSource : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := poorBase
  reference := fun _ _ => []
  reference_generated := by
    apply poorBase.every_local_policy_is_enumerated
    intro key member
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := poorBase.publicPrefix
  original := poorBase.public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev poorFoundation : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨foundation.base, foundation.scope, poorSource, rfl, rfl⟩
abbrev poorModel := AdmissionRuntime.profile poorFoundation
abbrev poorOrigin : Origin poorModel where
  history := ⟨poorModel.source.history, poorModel.source.original⟩
  response := ⟨Reaction.restrict poorModel.source.code poorModel.source.opponent,
    Reaction.restriction_is_generated poorModel.source.code poorModel.source.opponent⟩
  side := .original
abbrev poorStart := EventHistory.ofOrigin poorModel 14 poorOrigin
def poorWork (oppose : Bool) : poorModel.source.code.Policy := fun key _ =>
  if key.1 = 0 then [if oppose then AdmissionControls.no else AdmissionControls.yes]
  else [if oppose then AdmissionControls.ownNo else AdmissionControls.ownYes]
theorem poorWork_generated (oppose : Bool) : poorWork oppose ∈ poorModel.source.code.policies := by
  apply poorModel.source.code.every_local_policy_is_enumerated
  intro key member
  apply (mem_words_iff _ _ _).mpr
  unfold poorWork
  split <;> cases oppose <;> simp
def poorActivation (site : Fin poorModel.source.code.sites) : LocalMove poorModel.source.code site :=
  ⟨some ⟨.activate site, by fin_cases site <;> simp [poorModel, poorBase, AdmissionControls.base, DeviationControls.code]⟩,
    by fin_cases site <;> simp [ownMoves, poorModel, poorBase, AdmissionControls.base, DeviationControls.code]⟩
def poorSending (site : Fin poorModel.source.code.sites) : LocalMove poorModel.source.code site :=
  ⟨some ⟨.send site 1, by fin_cases site <;> simp [poorModel, poorBase, AdmissionControls.base, DeviationControls.code]⟩,
    by fin_cases site <;> simp [ownMoves, poorModel, poorBase, AdmissionControls.base, DeviationControls.code]⟩
def poorRule (oppose activating : Bool) : Rule poorModel.source.code :=
  ⟨⟨poorWork oppose, poorWork_generated oppose⟩, fun key _ => if activating then poorActivation key.1 else poorSending key.1⟩
abbrev poorPast : List (EventHistory.Stage (code := poorModel.source.code)) :=
  [(poorRule false true, fun _ _ _ => none), (poorRule false true, fun _ _ _ => none),
    (poorRule false true, fun _ _ _ => none), (poorRule false true, fun _ _ _ => none),
    (poorRule false false, fun _ _ _ => none)]
abbrev poorProtocols : Nat → Rule poorModel.source.code := fun _ => poorRule false false
abbrev poorEncoding : StageTransport.Encoding (code := poorModel.source.code) := fun signal =>
  if AdmissionCode.content poorBase signal = 0 then some ⟨0, 0, 0, false, slot, true, 1⟩
  else some ⟨2, 0, 1, true, slot, true, 1⟩
abbrev poorLaw : StageReception.Law poorModel.source.code := ⟨fun _ _ => slot, 1⟩
abbrev poorFull := StageQueueProgress.completeStages poorStart poorPast poorProtocols
theorem a_real_scheduled_attempt_without_delivery_resources_does_not_become_a_receipt :
    StageReception.delivered (StageQueue.row (EventHistory.execute poorStart poorPast) poorProtocols 0) 0 = true ∧
      ((StageReception.run vocabulary poorEncoding poorLaw poorStart poorFull 1 poorFull.length).audit[5]?).map
        (fun row => row.2.2) = some (.rejected .unpaidDelivery) ∧
      StageQueueProgress.windowPlan vocabulary poorBase poorEncoding poorLaw poorStart poorPast poorProtocols 1 slot 2 = .blocked .insufficientReadySupport ∧
      AdmissionQuorum.produce poorBase vocabulary poorEncoding poorLaw poorStart poorFull 1 slot 2 = .blocked := by
  decide +kernel

abbrev rooted := StageQueueRuntime.rooted foundation start pastStages protocols vocabulary encoding law slot 2
abbrev runtime := StageQueueRuntime.activated foundation start pastStages protocols vocabulary encoding law slot 2
  (StageQueueRuntime.ordinal foundation start pastStages protocols)
theorem an_independent_original_root_consumes_the_generated_completion_and_actual_next :
    rooted.plans 1 = .ready true ∧ rooted.source.decisions 1 = .decided true ∧
      (rooted.source.receivers 1).receipts = AdmissionControls.expected.take 2 ∧
      (StageQueueRuntime.authority foundation start pastStages protocols vocabulary encoding law slot 2).current =
        Native.Authority.fullGenerate (StageQueueRuntime.actualBound foundation start pastStages protocols)
          ((EventHistory.execute start full).source.history.length + 1 + (EventHistory.execute start full).cut) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (StageQueueRuntime.facade foundation start pastStages protocols vocabulary encoding law slot 2).process.stateAt
        ((StageQueueRuntime.facade foundation start pastStages protocols vocabulary encoding law slot 2).process.successor runtime.state) := by
  have consumed := StageQueueRuntime.the_original_root_consumes_the_generated_window_completion_responsibilities_ledger_and_next
    foundation start pastStages protocols vocabulary encoding law slot 2
  have ready : rooted.plans 1 = .ready true := by decide +kernel
  exact ⟨ready, consumed.1 1 true ready, by decide +kernel,
    consumed.2.2.1, consumed.2.2.2.2.2.2.1, consumed.2.2.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageQueueControls

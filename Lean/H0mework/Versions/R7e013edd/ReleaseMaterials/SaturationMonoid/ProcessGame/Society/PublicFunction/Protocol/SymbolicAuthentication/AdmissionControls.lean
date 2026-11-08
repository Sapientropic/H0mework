import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionRuntime
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeviationControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionControls

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information
open Distributed.Recall.Information.Agency.Protocol Continuation

inductive Mode where
  | normal | noDelivery | withholdLast | duplicate
  deriving DecidableEq

abbrev yes := DeviationControls.yes
abbrev no := DeviationControls.no
def ownYes : Mandate.Source.Action := ⟨true, [], .resource, [], .use true [((), 1)] .external⟩
def ownNo : Mandate.Source.Action := ⟨true, [], .challenge, [], .use true [((), 1)] .external⟩
abbrev base := {DeviationControls.code with
  siteParty := fun site => decide (site = 1)
  actions := [yes, no, ownYes, ownNo]}
abbrev underlying : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := base
  reference := fun _ _ => []
  reference_generated := by
    apply base.every_local_policy_is_enumerated
    intro key member
    exact (mem_words_iff _ _ _).mpr (by simp)
  history := base.publicPrefix
  original := base.public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev foundation : Native.Authority.Bound (Party := Bool) (Good := Unit) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit) :=
  ⟨Distributed.Recall.Information.Regression.base, Distributed.Recall.Information.Regression.scope, underlying, rfl, rfl⟩
abbrev model := AdmissionRuntime.profile foundation
abbrev code := model.source.code
abbrev origin : Origin model where
  history := ⟨model.source.history, model.source.original⟩
  response := ⟨Reaction.restrict code model.source.opponent, Reaction.restriction_is_generated code model.source.opponent⟩
  side := .original
abbrev start := EventHistory.ofOrigin model 14 origin

def work (oppose : Bool) : code.Policy := fun key _ =>
  if key.1 = 0 then [if oppose then no else yes] else [if oppose then ownNo else ownYes]
theorem work_generated (oppose : Bool) : work oppose ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key member
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split <;> cases oppose <;> simp

def activation (site : Fin code.sites) : LocalMove code site :=
  ⟨some ⟨.activate site, by fin_cases site <;> simp [code, base, DeviationControls.code]⟩,
    by fin_cases site <;> simp [ownMoves, code, base, DeviationControls.code]⟩
def sending (site : Fin code.sites) : LocalMove code site :=
  ⟨some ⟨.send site 1, by fin_cases site <;> simp [code, base, DeviationControls.code]⟩,
    by fin_cases site <;> simp [ownMoves, code, base, DeviationControls.code]⟩
def rule (oppose activating : Bool) : Rule code :=
  ⟨⟨work oppose, work_generated oppose⟩, fun key _ => if activating then activation key.1 else sending key.1⟩

def environment (mode : Mode) : Opponent code := fun history _ _ =>
  if mode = .noDelivery then none else
  match history.length - 2 with
  | 5 => some ⟨.deliver 0, by simp [code, base, DeviationControls.code]⟩
  | 7 => some ⟨.deliver 1, by simp [code, base, DeviationControls.code]⟩
  | 13 => if mode = .withholdLast then none else if mode = .duplicate then
      some ⟨.deliver 0, by simp [code, base, DeviationControls.code]⟩
    else some ⟨.deliver 2, by simp [code, base, DeviationControls.code]⟩
  | _ => none
def stages (mode : Mode) : List (EventHistory.Stage (code := code)) :=
  ((List.replicate 4 (rule false true)) ++ (List.replicate 4 (rule false false)) ++
    (List.replicate 4 (rule true true)) ++ (List.replicate 2 (rule true false))).map fun protocol => (protocol, environment mode)
abbrev vocabulary := DeviationControls.vocabulary
abbrev slot := DeviationControls.slot
abbrev law : StageReception.Law code := ⟨fun _ _ => slot, 1⟩
abbrev first : StageBudget.Ballot (code := code) := ⟨0, 0, 0, false, slot, true, 1⟩
abbrev second : StageBudget.Ballot (code := code) := ⟨2, 0, 1, true, slot, true, 1⟩
abbrev third : StageBudget.Ballot (code := code) := ⟨8, 0, 0, false, slot, false, 1⟩
def encoding : StageTransport.Encoding (code := code) := fun signal =>
  if AdmissionCode.content base signal = 0 then some first
  else if AdmissionCode.content base signal = 1 then some second else some third
abbrev firstWire : StageTransport.Wire (code := code) := ⟨4, 0, 1, 0, 2, first⟩
abbrev secondWire : StageTransport.Wire (code := code) := ⟨6, 1, 1, 2, 4, second⟩
abbrev thirdWire : StageTransport.Wire (code := code) := ⟨12, 2, 1, 4, 7, third⟩
abbrev expected : List (StageReception.Receipt (code := code)) :=
  [⟨firstWire, 5, 5⟩, ⟨secondWire, 7, 7⟩, ⟨thirdWire, 13, 13⟩]
abbrev observed (mode : Mode) := StageReception.run vocabulary encoding law start (stages mode) 1 (stages mode).length
abbrev produce (mode : Mode) (threshold : Nat) := AdmissionQuorum.produce base vocabulary encoding law start (stages mode) 1 slot threshold

theorem genesis_admission_is_generated_before_any_stage :
    AdmissionCode.affected base = {0} ∧ AdmissionCode.budget base = 1 ∧
      AdmissionCode.mayRewrite base 1 = false ∧
      (StageBudget.ledger vocabulary start []).isEmpty = true := by
  decide +kernel

theorem actual_paid_equivocation_and_a_safe_online_decision_coexist :
    StageBudget.ledger vocabulary start (stages .normal) = [first, second, third] ∧
      StageBudget.evidenceKeys vocabulary start (stages .normal) = {0} ∧
      (observed .normal).receipts = expected ∧
      produce .normal 2 = .decided true ∧
      AdmissionQuorum.produce base vocabulary encoding law start ((stages .normal).take 8) 1 slot 2 = .decided true := by
  decide +kernel

theorem a_non_admitted_repeat_is_sealed_despite_real_delivery_and_new_work :
    (StageTrace.records start (stages .normal))[10]?.map (fun row => row.submitted) = some [] ∧
      (work true (1, 3) (by decide +kernel)) = [ownNo] ∧
      AdmissionCode.ready base ((EventStep.seed (EventHistory.execute start ((stages .normal).take 8))).frame.inbox 1) = false ∧
      AdmissionCode.ready base ((EventStep.seed (EventHistory.execute start (stages .normal))).frame.inbox 1) = false := by
  decide +kernel

theorem missing_delivery_timing_quorum_and_source_have_distinct_failures :
    (observed .noDelivery).receipts = [] ∧ produce .noDelivery 2 = .blocked ∧
      produce .normal 1 = .blocked ∧ produce .normal 3 = .blocked ∧ produce .normal 0 = .blocked ∧
      AdmissionQuorum.produce base vocabulary encoding {law with maxDelay := 0} start (stages .normal) 1 slot 2 = .blocked ∧
      StageTransport.verify vocabulary encoding start [] firstWire = false ∧
      StageBudget.verify vocabulary start (stages .normal) {first with actor := true} = false ∧
      StageBudget.verify vocabulary start (stages .normal) {first with scope := ⟨1, 0, 0⟩} = false := by
  decide +kernel

theorem withholding_or_duplicate_receipts_do_not_hide_paid_equivocation_or_create_votes :
    (observed .withholdLast).receipts = expected.take 2 ∧ produce .withholdLast 2 = .decided true ∧
      StageBudget.evidenceKeys vocabulary start (stages .withholdLast) = {0} ∧
      (StageReception.run vocabulary encoding {law with maxDelay := 10} start (stages .duplicate) 1 14).receipts = expected.take 2 ∧
      ((StageReception.run vocabulary encoding {law with maxDelay := 10} start (stages .duplicate) 1 14).audit[13]?).map
        (fun row => row.2.2) = some (.rejected .duplicate) := by
  decide +kernel

abbrev beforeDelivery := EventStep.seed (EventHistory.execute start ((stages .normal).take 5))
abbrev peerReset := {code with
  afterDelivery := fun recipient sender old reading =>
    AdmissionCode.pack base (AdmissionCode.ready base reading)
      (base.afterDelivery recipient sender (AdmissionCode.content base old) (AdmissionCode.content base reading))}
abbrev resetFrame : peerReset.Frame :=
  ⟨[], beforeDelivery.frame.sent.map (fun packet =>
    ⟨packet.sender, packet.recipient, packet.signal, packet.sentAfter⟩),
    beforeDelivery.frame.inbox, beforeDelivery.frame.localLegal⟩

theorem letting_a_peer_reset_the_latch_reopens_an_actually_sealed_key :
    AdmissionCode.ready base (beforeDelivery.frame.inbox 1) = false ∧
      AdmissionCode.ready base ((code.step (work false) beforeDelivery.current
        {beforeDelivery.frame with word := []} (.deliver 0)).inbox 1) = false ∧
      AdmissionCode.ready base ((peerReset.step (work false) beforeDelivery.current
        resetFrame (.deliver 0)).inbox 1) = true := by
  decide +kernel

abbrev batched := {code with actionLimit := 2}
def batchWork : batched.Policy := fun key _ => if key.1 = 1 then [ownYes, ownNo] else []
theorem batch_generated : batchWork ∈ batched.policies := by
  apply batched.every_local_policy_is_enumerated
  intro key member
  apply (mem_words_iff _ _ _).mpr
  unfold batchWork
  split <;> simp
abbrev batchStart : Cursor batched where
  reference := batchWork
  reference_generated := batch_generated
  history := batched.publicPrefix
  original := batched.public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
  entry := ⟨fun _ _ _ => none, 3⟩
  overrides := []
  cut := 0
  ownerStart := start.ownerStart
abbrev batchRule : Rule batched := ⟨⟨batchWork, batch_generated⟩, fun key _ => activation key.1⟩
abbrev batchStages : List (EventHistory.Stage (code := batched)) := List.replicate 3 (batchRule, fun _ _ _ => none)

theorem removing_the_single_request_limit_mints_a_real_unbudgeted_same_cut_double_vote :
    StageBudget.evidenceKeys vocabulary batchStart batchStages = {1} ∧
      AdmissionCode.mayRewrite base 1 = false ∧
      (StageBudget.ledger vocabulary batchStart batchStages).map (fun body => (body.cut, body.position, body.key.val, body.choice)) =
        [(2, 0, 1, true), (2, 1, 1, false)] := by
  decide +kernel

theorem a_decision_at_the_completed_prefix_controls_every_future_decision
    (future : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites) (choice : Bool)
    (decided : AdmissionQuorum.produce base vocabulary encoding law start
      ((stages .normal).take 8 ++ future) receiver slot 2 = .decided choice) : choice = true := by
  exact (AdmissionQuorum.produced_decisions_agree_across_every_actual_extension base vocabulary encoding law start
    ((stages .normal).take 8) future 1 receiver slot 2 true choice
    actual_paid_equivocation_and_a_safe_online_decision_coexist.2.2.2.2 decided).symm

abbrev rooted := AdmissionRuntime.rooted foundation start (stages .normal) vocabulary encoding law slot 2
abbrev runtime := AdmissionRuntime.activated foundation start (stages .normal) vocabulary encoding law slot 2
  (AdmissionRuntime.ordinal foundation start (stages .normal))

theorem an_independent_root_consumes_the_online_decision_responsibilities_and_next :
    rooted.decisions 1 = .decided true ∧ (rooted.receivers 1).receipts = expected ∧
      (AdmissionRuntime.authority foundation start (stages .normal) vocabulary encoding law slot 2).current =
        Native.Authority.fullGenerate (AdmissionRuntime.actualBound foundation start (stages .normal))
          ((EventHistory.execute start (stages .normal)).source.history.length + 1 + (EventHistory.execute start (stages .normal)).cut) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (AdmissionRuntime.facade foundation start (stages .normal) vocabulary encoding law slot 2).process.stateAt
        ((AdmissionRuntime.facade foundation start (stages .normal) vocabulary encoding law slot 2).process.successor runtime.state) := by
  have consumed := AdmissionRuntime.the_original_root_consumes_online_agreement_responsibilities_ledger_and_next
    foundation start (stages .normal) vocabulary encoding law slot 2
  exact ⟨actual_paid_equivocation_and_a_safe_online_decision_coexist.2.2.2.1,
    actual_paid_equivocation_and_a_safe_online_decision_coexist.2.2.1,
    consumed.2.1, consumed.2.2.2.2.2.1, consumed.2.2.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AdmissionControls

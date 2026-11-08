import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.BallotQuorum
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AvailabilityAudit
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.AttestationControls
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptFold

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 30000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeviationControls

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol

inductive Mode where
  | normal | noDelivery | withholdLast
  deriving DecidableEq

abbrev yes := AttestationControls.yes
abbrev no := AttestationControls.no
abbrev code : Code Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  law := AttestationControls.origin.code.law
  initial := ⟨fun _ _ => 100, AttestationControls.origin.code.initial.claims,
    AttestationControls.origin.code.initial.technology, AttestationControls.origin.code.initial.clock,
    AttestationControls.origin.code.initial.round⟩
  bootstrap := AttestationControls.origin.code.bootstrap
  task := AttestationControls.origin.code.task
  actions := [yes, no]
  actionLimit := 2
  sites := 2
  signals := 3
  initialSignal := 0
  siteParty := fun _ => false
  readLocal := fun site snapshot =>
    if site = 0 then (if snapshot.round < 11 then 0 else 2) else 1
  memoryReady := fun _ => true
  afterAction := fun _ _ _ => 1
  afterSend := fun _ _ old _ => old
  afterDelivery := fun _ _ old _ => old
  sendCost := fun _ _ => [yes]
  deliveryCost := fun _ => [yes]
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := [.activate 0, .activate 1, .send 0 1, .send 1 1,
    .deliver 0, .deliver 1, .deliver 2]
  eventLimit := 0
  eligible := fun _ => true
  parties := [false, true]
  goods := [()]
  instruments := [()]
  parties_cover := by intro party; cases party <;> simp
  goods_cover := by intro good; cases good; simp
  instruments_cover := by intro instrument; cases instrument; simp

def work : code.Policy := fun key _ => if key.1 = 0 then [yes, no] else [yes]
theorem work_generated : work ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  apply (mem_words_iff _ _ _).mpr
  unfold work
  split <;> simp

def activation (site : Fin code.sites) : LocalMove code site :=
  ⟨some ⟨.activate site, by fin_cases site <;> simp [code]⟩,
    by fin_cases site <;> simp [ownMoves, code]⟩
def sending (site : Fin code.sites) : LocalMove code site :=
  ⟨some ⟨.send site 1, by fin_cases site <;> simp [code]⟩,
    by fin_cases site <;> simp [ownMoves, code]⟩
abbrev rule : Rule code := ⟨⟨work, work_generated⟩,
  fun key _ => if key.2 = 0 then activation key.1 else sending key.1⟩
abbrev source : Machine Bool Unit Mandate.Source.Port (Mandate.State Bool Unit) Unit where
  code := code
  reference := work
  reference_generated := work_generated
  history := code.publicPrefix
  original := code.public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original
abbrev entry : Input code := ⟨fun _ _ _ => none, 10⟩

def environment (mode : Mode) : Opponent code := fun history _ _ =>
  if mode = .noDelivery then none else
  match history.length - 2 with
  | 5 => some ⟨.deliver 0, by simp [code]⟩
  | 7 => some ⟨.deliver 1, by simp [code]⟩
  | 9 => if mode = .withholdLast then none else some ⟨.deliver 2, by simp [code]⟩
  | _ => none

abbrev slot : Scope := ⟨0, 0, 0⟩
abbrev vocabulary := AttestationControls.vocabulary
abbrev law : AttestationReception.ReceptionLaw source := ⟨fun _ _ => slot, 1⟩
def encoding : AttestationTransport.Encoding source := fun signal =>
  if signal = 0 then some ⟨0, 0, 0, false, slot, true, 1⟩
  else if signal = 1 then some ⟨2, 0, 1, false, slot, true, 1⟩
  else some ⟨0, 1, 0, false, slot, false, 1⟩
abbrev observed (mode : Mode) (count : Nat) := AttestationReception.run source entry 0 rule (environment mode) vocabulary encoding law 1 count
abbrev affected (mode : Mode) := DeviationBudget.affectedThrough source entry 0 rule (environment mode) vocabulary 10
abbrev budget (mode : Mode) := DeviationBudget.budget source entry 0 rule (environment mode) vocabulary 10
abbrev decision (mode : Mode) (count threshold : Nat) := BallotQuorum.readout source (observed mode count) slot threshold
abbrev omissions (mode : Mode) := AvailabilityAudit.rows source entry 0 rule (environment mode) vocabulary encoding law 1 10

private theorem normalAffected : affected .normal = {0} := by decide +kernel
private theorem absentAffected : affected .noDelivery = {0} := by decide +kernel
private theorem withheldAffected : affected .withholdLast = {0} := by decide +kernel

private def firstTwo : List (AttestationReception.Receipt source) :=
  [⟨⟨4, 0, 1, 0, 3, ⟨0, 0, 0, false, slot, true, 1⟩⟩, 5⟩,
   ⟨⟨6, 1, 1, 1, 5, ⟨2, 0, 1, false, slot, true, 1⟩⟩, 7⟩]
private def third : AttestationReception.Receipt source :=
  ⟨⟨8, 2, 1, 2, 7, ⟨0, 1, 0, false, slot, false, 1⟩⟩, 9⟩

private abbrev baseVerdict (mode : Mode) (n : Nat) :=
  ReceiptFold.baseVerdict source entry 0 rule (environment mode) vocabulary encoding law 1 n
private abbrev receiptStep := ReceiptFold.step source

private def expectedVerdict (mode : Mode) (n : Nat) : AttestationReception.Verdict source :=
  if mode = .noDelivery then .rejected .missingWire else
  match n with
  | 5 => .accepted (firstTwo.get ⟨0, by decide⟩).wire
  | 7 => .accepted (firstTwo.get ⟨1, by decide⟩).wire
  | 9 => if mode = .withholdLast then .rejected .missingWire else .accepted third.wire
  | _ => .rejected .missingWire

private theorem actual_verdict_table (mode : Mode) :
    (List.range 10).map (fun n => (n, baseVerdict mode n)) =
      (List.range 10).map (fun n => (n, expectedVerdict mode n)) := by
  cases mode <;>
    simp only [baseVerdict, ReceiptFold.baseVerdict, AttestationReception.incoming, AttestationReception.check,
      AttestationTransport.verify, AttestationTransport.issuedAt,
      OwnedAttestation.verify, OwnedAttestation.issuedAt, OwnedAttestation.inspect, ReceiptFold.before_is_feedback, ReceiptFold.word_is_feedback] <;>
    decide +kernel

private theorem verdict_at (mode : Mode) (n : Nat) (bounded : n < 10) :
    baseVerdict mode n = expectedVerdict mode n := by
  have entryAt := congrArg (fun items => items[n]?) (actual_verdict_table mode)
  have position : (List.range 10)[n]? = some n := by simp [bounded]
  simpa only [List.getElem?_map, position, Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] using entryAt

private theorem computed_prefix (mode : Mode) (count : Nat) (bounded : count ≤ 10) :
    (observed mode count).receipts =
      ((List.range count).map (fun n => (n, expectedVerdict mode n))).foldl receiptStep [] := by
  rw [ReceiptFold.receipts_are_fold]
  congr 1
  apply List.map_congr_left
  intro n member
  exact congrArg (Prod.mk n) (verdict_at mode n (lt_of_lt_of_le (List.mem_range.mp member) bounded))

private theorem computedReceipts :
    (observed .normal 10).receipts = firstTwo ++ [third] ∧
      (observed .normal 8).receipts = firstTwo ∧
      (observed .normal 6).receipts = firstTwo.take 1 ∧
      (observed .noDelivery 10).receipts = [] ∧
      (observed .withholdLast 10).receipts = firstTwo := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [computed_prefix _ _ (by omega)] <;> decide +kernel

private theorem normalReceipts : (observed .normal 10).receipts = firstTwo ++ [third] := computedReceipts.1
private theorem earlierReceipts : (observed .normal 8).receipts = firstTwo := computedReceipts.2.1
private theorem insufficientReceipts : (observed .normal 6).receipts = firstTwo.take 1 := computedReceipts.2.2.1
private theorem absentReceipts : (observed .noDelivery 10).receipts = [] := computedReceipts.2.2.2.1
private theorem withheldReceipts : (observed .withholdLast 10).receipts = firstTwo := computedReceipts.2.2.2.2

private theorem budget_values (mode : Mode) : budget mode = 1 := by
  cases mode
  · change (affected .normal).card = 1
    rw [normalAffected]
    decide
  · change (affected .noDelivery).card = 1
    rw [absentAffected]
    decide
  · change (affected .withholdLast).card = 1
    rw [withheldAffected]
    decide

theorem actual_selected_work_generates_one_affected_key :
    DeviationBudget.hazardsAt source entry 0 rule (environment .normal) vocabulary 0 = {0} ∧
      DeviationBudget.labelsAt source entry 0 rule (environment .normal) vocabulary 0 0 = [(slot, true), (slot, false)] ∧
      affected .normal = {0} ∧ budget .normal = 1 ∧
      1 ∉ affected .normal := by
  refine ⟨by decide +kernel, by decide +kernel, normalAffected, budget_values .normal, ?_⟩
  rw [normalAffected]
  decide

theorem deleting_the_work_hazard_would_miss_actual_same_cut_equivocation :
    OwnedAttestation.verify source entry 0 rule (environment .normal) vocabulary
        ⟨0, 0, 0, false, slot, true, 1⟩ = true ∧
      OwnedAttestation.verify source entry 0 rule (environment .normal) vocabulary
        ⟨0, 1, 0, false, slot, false, 1⟩ = true ∧
      DeviationBudget.changesAt source entry 0 rule (environment .normal) vocabulary 0 = ∅ ∧
      DeviationBudget.budget source entry 0 rule (environment .normal) vocabulary 1 = 1 := by
  decide +kernel

theorem a_legitimate_ballot_and_another_phase_are_not_intrinsic_faults :
    OwnedAttestation.verify source entry 0 rule (environment .normal) vocabulary
        ⟨2, 0, 1, false, slot, true, 1⟩ = true ∧
      1 ∉ affected .normal ∧
      DeviationBudget.contradictory [(slot, true), (⟨0, 0, 1⟩, false)] = false := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  rw [normalAffected]
  decide

theorem normal_own_memory_progress_does_not_create_extra_fault_identities :
    (AttestationTransport.state source entry 0 rule (environment .normal) 0).frame.inbox 1 = 0 ∧
      (AttestationTransport.state source entry 0 rule (environment .normal) 3).frame.inbox 1 = 1 ∧
      1 ∉ affected .normal := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  rw [normalAffected]
  decide

theorem two_real_distinct_keys_decide_despite_delivered_equivocation :
    (observed .normal 10).receipts.length = 3 ∧
      (AttestationReception.evidence source (observed .normal 10)).length = 2 ∧
      (BallotQuorum.support source (observed .normal 10) slot true).card = 2 ∧
      (BallotQuorum.support source (observed .normal 10) slot false).card = 1 ∧
      decision .normal 8 2 = .decided true ∧ decision .normal 10 2 = .decided true ∧
      code.sites + budget .normal < 2 + 2 := by
  simp only [decision, BallotQuorum.readout, BallotQuorum.support, AttestationReception.evidence,
    normalReceipts, earlierReceipts, budget_values]
  decide +kernel

theorem insufficient_threshold_allows_conflicting_actual_readouts :
    decision .normal 6 1 = .decided true ∧ decision .normal 10 1 = .decided false ∧
      ¬ code.sites + budget .normal < 1 + 1 := by
  simp only [decision, BallotQuorum.readout, BallotQuorum.support,
    insufficientReceipts, normalReceipts, budget_values]
  decide +kernel

theorem an_independent_consumer_uses_the_generated_budget_for_agreement :
    ∀ second : Bool, decision .normal 10 2 = .decided second → second = true := by
  intro second decided
  exact BallotQuorum.agreement_of_actual_source_budget source entry 0 rule (environment .normal) vocabulary encoding law
    1 1 10 8 10 (by omega) (by omega) slot 2 second true decided
    two_real_distinct_keys_decide_despite_delivered_equivocation.2.2.2.2.1
    two_real_distinct_keys_decide_despite_delivered_equivocation.2.2.2.2.2.2

theorem missing_delivery_does_not_turn_a_safety_budget_into_a_decision :
    budget .noDelivery = 1 ∧ (observed .noDelivery 10).receipts = [] ∧
      decision .noDelivery 10 2 = .blocked ∧ decision .normal 10 0 = .blocked ∧
      decision .normal 10 3 = .blocked ∧ decision .normal 6 2 = .blocked ∧
      (omissions .noDelivery).map (fun row => row.2.2) =
        [.noDelivery, .noDelivery, .noDelivery] := by
  refine ⟨budget_values .noDelivery, absentReceipts, ?_, by decide +kernel, ?_, ?_, ?_⟩
  · simp only [decision, BallotQuorum.readout, BallotQuorum.support, absentReceipts]
    decide +kernel
  · simp only [decision, BallotQuorum.readout, BallotQuorum.support, normalReceipts]
    decide +kernel
  · simp only [decision, BallotQuorum.readout, BallotQuorum.support, insufficientReceipts]
    decide +kernel
  · simp only [omissions, AvailabilityAudit.rows, AvailabilityAudit.classify, absentReceipts]
    simp only [AttestationTransport.issuedAt, OwnedAttestation.verify, OwnedAttestation.issuedAt,
      OwnedAttestation.inspect, ReceiptFold.before_is_feedback, ReceiptFold.word_is_feedback]
    decide +kernel

theorem a_withheld_message_and_a_safe_decision_can_coexist :
    decision .withholdLast 10 2 = .decided true ∧ budget .withholdLast = 1 ∧
      (omissions .withholdLast).map (fun row => row.2.2) =
        [.bodyAcknowledged, .bodyAcknowledged, .noDelivery] ∧
      (AttestationReception.evidence source (observed .withholdLast 10)).isEmpty = true := by
  refine ⟨?_, budget_values .withholdLast, ?_, ?_⟩
  · simp only [decision, BallotQuorum.readout, BallotQuorum.support, withheldReceipts]
    decide +kernel
  · simp only [omissions, AvailabilityAudit.rows, AvailabilityAudit.classify, withheldReceipts]
    simp only [AttestationTransport.issuedAt, OwnedAttestation.verify, OwnedAttestation.issuedAt,
      OwnedAttestation.inspect, ReceiptFold.before_is_feedback, ReceiptFold.word_is_feedback]
    decide +kernel
  · simp only [AttestationReception.evidence, withheldReceipts]
    decide +kernel

theorem attempted_but_late_is_not_reported_as_no_delivery :
    (AvailabilityAudit.rows source entry 0 rule (environment .normal) vocabulary encoding {law with maxDelay := 0} 1 10).map
      (fun row => row.2.2) = [.attemptedButUnaccepted, .attemptedButUnaccepted, .attemptedButUnaccepted] := by
  simp only [AvailabilityAudit.rows, AvailabilityAudit.classify,
    AttestationTransport.issuedAt, OwnedAttestation.verify, OwnedAttestation.issuedAt,
    OwnedAttestation.inspect, ReceiptFold.before_is_feedback, ReceiptFold.word_is_feedback]
  decide +kernel

abbrev firstWire : AttestationTransport.Wire source :=
  ⟨4, 0, 1, 0, 3, ⟨0, 0, 0, false, slot, true, 1⟩⟩

theorem an_independent_consumer_recovers_actual_emission_and_absent_delivery :
    AttestationTransport.issuedAt source entry 0 rule (environment .noDelivery) vocabulary encoding 4 = some firstWire ∧
      ∀ n < 10, firstWire.sendCut < n →
        AttestationReception.deliveredAt source entry 0 rule (environment .noDelivery) n firstWire.serial ≠ true := by
  have row := AvailabilityAudit.every_row_has_actual_emission source entry 0 rule (environment .noDelivery)
    vocabulary encoding law 1 10 4 firstWire .noDelivery (by
      simp only [AvailabilityAudit.rows, AvailabilityAudit.classify, absentReceipts,
        AttestationTransport.issuedAt, OwnedAttestation.verify, OwnedAttestation.issuedAt,
        OwnedAttestation.inspect, ReceiptFold.before_is_feedback, ReceiptFold.word_is_feedback]
      decide +kernel)
  exact ⟨row.2.1, (AvailabilityAudit.no_delivery_has_expired_and_has_no_actual_attempt
    source entry 0 rule (environment .noDelivery) vocabulary encoding law 1 10 firstWire row.2.2.2.symm).2.1⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DeviationControls

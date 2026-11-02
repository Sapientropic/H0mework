import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalAuthenticationSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalReceiptRuntime

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalReceiptControls

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RequestResponseSource


abbrev query (mode : Mode) := LocalReceiptAuthentication.generate vocabulary (encoding mode) (law mode)
  (start mode) ((stages mode).map Prod.fst) 1 ((EventStep.seed (beforeResponse mode)).frame.inbox 1)
abbrev rule (mode : Mode) := LocalReceiptAuthentication.protocol vocabulary (encoding mode) (law mode)
  (start mode) ((stages mode).map Prod.fst)
abbrev responseRow (mode : Mode) := StageTrace.material (beforeResponse mode) (rule mode) (environment mode)
abbrev authenticatedFull (mode : Mode) := LocalReceiptAuthentication.produce vocabulary (encoding mode) (law mode)
  (start mode) (stages mode) (environment mode)
abbrev authenticatedFinal (mode : Mode) := EventHistory.execute (start mode) (authenticatedFull mode)
abbrev receipt (mode : Mode) : RequestReadback.Receipt (code := code mode) :=
  ⟨⟨⟨4, 0, 1, 1, 1, ballot mode⟩, 5, 5⟩, statement mode, 1⟩

theorem an_actual_paid_delivery_is_locally_authenticated_with_its_entire_receipt :
    (query .normal).status = .authenticated ∧ (query .normal).receipts = [receipt .normal] := by
  constructor <;> decide +kernel

theorem the_receipt_gated_local_response_is_actually_executed_and_paid :
    (authenticatedFull .normal).length = 8 ∧
    (responseRow .normal).submitted = [positive] ∧
    RequestAttestation.issued vocabulary (responseRow .normal) 0 = some (responseStatement .normal) ∧
    (EventStep.seed (authenticatedFinal .normal)).current.stock true () = 8 ∧
    (EventStep.seed (authenticatedFinal .normal)).frame.inbox 1 = 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem missing_payment_or_available_content_cannot_generate_a_local_receipt :
    (query .unpaidSend).receipts = [] ∧ (query .unpaidDelivery).receipts = [] ∧
    (query .erased).receipts = [] ∧ (query .rewritten).receipts = [] ∧
    (query .unreadable).receipts = [] ∧ (query .wrongWire).receipts = [] ∧
    (responseRow .unpaidDelivery).submitted = [] ∧ (responseRow .wrongWire).submitted = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

abbrev noTiming : StageReception.Law (code .normal) := {(law .normal) with maxDelay := 0}

theorem source_authentication_cannot_supply_the_missing_communication_timing :
    (LocalAuthenticationSource.query .normal).status = .authenticated ∧
    (LocalReceiptAuthentication.generate vocabulary (encoding .normal) noTiming (start .normal)
      ((stages .normal).map Prod.fst) 1 1).receipts = [] ∧
    LocalReceiptAuthentication.work vocabulary (encoding .normal) noTiming (start .normal)
      ((stages .normal).map Prod.fst) 1 1 = [] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem forged_encoding_wrong_signer_deleted_origin_and_stale_replay_are_rejected :
    (LocalReceiptAuthentication.generate vocabulary (fun _ => some {(ballot .normal) with actor := true})
      (law .normal) (start .normal) ((stages .normal).map Prod.fst) 1 1).receipts = [] ∧
    (LocalReceiptAuthentication.generate vocabulary (encoding .normal) (law .normal) (start .normal)
      (LocalAuthenticationSource.wrongSigner.map Prod.fst) 1 1).receipts = [] ∧
    (LocalReceiptAuthentication.generate vocabulary (encoding .normal) (law .normal) (start .normal)
      (LocalAuthenticationSource.noOrigin.map Prod.fst) 1 1).receipts = [] ∧
    (LocalReceiptAuthentication.generate vocabulary (encoding .normal) LocalAuthenticationSource.expiring (start .normal)
      (LocalAuthenticationSource.stale.map Prod.fst) 1 1).receipts = [] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem a_local_receipt_does_not_supply_missing_own_resources_actions_or_quorum :
    (query .poor).status = .authenticated ∧
    RequestAttestation.outcome vocabulary (responseRow .poor) 0 = .rejected (.source .invalid) ∧
    (query .noReply).status = .authenticated ∧ (responseRow .noReply).submitted = [] ∧
    StageQuorum.produce vocabulary (encoding .normal) (law .normal) (start .normal) (stages .normal) 1 6 slot 2 = .blocked := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

-- The signal carries content, not a private timestamp. Two real delivery cuts
-- therefore need not have a commonly knowable full receipt.
def timingPast (late : Bool) : List (EventHistory.Stage (code := code .normal)) :=
  (stages .normal).take 5 ++
    [(quiet .normal, if late then environment .normal else deliver .normal),
      (quiet .normal, environment .normal), (quiet .normal, deliver .normal)]
abbrev wider : StageReception.Law (code .normal) := {(law .normal) with maxDelay := 3}
abbrev laterReceipt : RequestReadback.Receipt (code := code .normal) :=
  {(receipt .normal) with confirmation := {(receipt .normal).confirmation with index := 7, delivery := 7}}
abbrev timingQuery (late : Bool) := LocalReceiptAuthentication.generate vocabulary (encoding .normal) wider
  (start .normal) ((timingPast late).map Prod.fst) 1
  ((EventStep.seed (EventHistory.execute (start .normal) (timingPast late))).frame.inbox 1)

theorem duplicate_delivery_and_delayed_delivery_keep_distinct_real_histories_with_the_same_local_word :
    (timingPast false).map Prod.fst = (timingPast true).map Prod.fst ∧
    (EventStep.seed (EventHistory.execute (start .normal) (timingPast false))).frame.inbox 1 = 1 ∧
    (EventStep.seed (EventHistory.execute (start .normal) (timingPast true))).frame.inbox 1 = 1 ∧
    (RequestReadback.produce vocabulary (encoding .normal) wider (start .normal) (timingPast false) 1 8).receipts = [receipt .normal] ∧
    (RequestReadback.produce vocabulary (encoding .normal) wider (start .normal) (timingPast true) 1 8).receipts = [laterReceipt] ∧
    receipt .normal ≠ laterReceipt := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem a_valid_actual_receipt_does_not_override_indistinguishable_delivery_metadata :
    (timingQuery false).receipts = [] := by
  obtain ⟨rules, earlyRead, lateRead, early, late, distinct⟩ :=
    duplicate_delivery_and_delayed_delivery_keep_distinct_real_histories_with_the_same_local_word
  have queries : timingQuery false = timingQuery true := by
    unfold timingQuery
    rw [rules, earlyRead, lateRead]
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro body inside
  have first := (LocalReceiptAuthentication.local_receipt_authentication_recovers_the_actual_paid_delivery
    vocabulary (encoding .normal) wider (start .normal) (timingPast false) 1 body inside).1
  rw [queries] at inside
  have second := (LocalReceiptAuthentication.local_receipt_authentication_recovers_the_actual_paid_delivery
    vocabulary (encoding .normal) wider (start .normal) (timingPast true) 1 body inside).1
  have earlyLength : (timingPast false).length = 8 := by decide +kernel
  have lateLength : (timingPast true).length = 8 := by decide +kernel
  rw [earlyLength, early, List.mem_singleton] at first
  rw [lateLength, late, List.mem_singleton] at second
  exact distinct (first.symm.trans second)

theorem consuming_the_local_slot_cannot_reopen_a_receipt :
    (LocalReceiptAuthentication.generate vocabulary (encoding .normal) (law .normal) (start .normal)
      ((authenticatedFull .normal).map Prod.fst) 1 3).receipts = [] := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalReceiptControls

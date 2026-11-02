import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponse

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponseRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (past : List (EventHistory.Stage (code := model.source.code)))
  (rival : Opponent model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code))
  (law : StageReception.Law model.source.code) (scope : Scope) (threshold : Nat)

abbrev stages := RequestResponse.produce start past rival
abbrev root := RequestReadbackRuntime.root model start (stages model start past rival) vocabulary encoding law scope threshold
abbrev runtime := RequestReadbackRuntime.runtime model start (stages model start past rival) vocabulary encoding law scope threshold
abbrev facade := RequestReadbackRuntime.facade model start (stages model start past rival) vocabulary encoding law scope threshold
abbrev authority := RequestReadbackRuntime.authority model start (stages model start past rival) vocabulary encoding law scope threshold
abbrev requests := RequestReadbackRuntime.inheritedRequests model start (stages model start past rival) vocabulary encoding law scope threshold
abbrev actualBound := RequestReadbackRuntime.actualBound model start (stages model start past rival) vocabulary encoding law
abbrev final := RequestReadbackRuntime.final model start (stages model start past rival) vocabulary encoding law

theorem the_actual_response_source_preserves_all_original_stages :
    past <+: RequestReadbackRuntime.full model start (stages model start past rival) vocabulary encoding law :=
  (RequestResponse.the_producer_keeps_the_complete_actual_prefix start past rival).trans
    (LocalJointRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law _ _)

theorem every_attested_response_is_in_the_original_root_request_face
    (row : StageTrace.Record (code := model.source.code))
    (inside : row ∈ StageTrace.records start (stages model start past rival))
    (position : Nat) (body : RequestAttestation.Statement (code := model.source.code))
    (made : RequestAttestation.issued vocabulary row position = some body) :
    body ∈ requests model start past rival vocabulary encoding law scope threshold := by
  obtain ⟨more, same⟩ := LocalJointRun.every_run_keeps_the_whole_source_history model start vocabulary encoding law
    (LocalJointResponse.fuel model start (stages model start past rival)) (stages model start past rival)
  change stages model start past rival ++ more =
    RequestReadbackRuntime.full model start (stages model start past rival) vocabulary encoding law at same
  change body ∈ RequestAttestation.ledger vocabulary start
    (RequestReadbackRuntime.full model start (stages model start past rival) vocabulary encoding law)
  rw [← same]
  unfold RequestAttestation.ledger
  rw [StageQueue.records_append, List.flatMap_append]
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨row, inside,
    List.mem_filterMap.mpr ⟨position, by
      obtain ⟨_, item, actual, _, _⟩ := RequestAttestation.issued_binds_the_complete_original_request vocabulary row position body made
      have bounded := List.getElem?_eq_some_iff.mp actual
      have length := congrArg List.length (model.source.code.law.inventory_requests_exact row.before.current 0 row.submitted)
      simp only [List.length_map] at length
      change position ∈ List.range row.submitted.length
      rw [List.mem_range]
      exact bounded.1.trans_eq length, made⟩⟩

theorem an_attested_generated_local_response_has_local_content_paid_origin_and_root_next
    (row : StageTrace.Record (code := model.source.code))
    (inside : row ∈ StageTrace.records start (stages model start past rival))
    (generated : row.protocol = RequestResponse.protocol)
    (position : Nat) (body : RequestAttestation.Statement (code := model.source.code))
    (made : RequestAttestation.issued vocabulary row position = some body) :
    body ∈ requests model start past rival vocabulary encoding law scope threshold ∧
    (∃ incoming item,
      RequestReadback.localRead (code := model.source.code) (row.before.frame.inbox body.ballot.key) = some incoming ∧
      RequestResponse.ownReply (model.source.code.siteParty body.ballot.key) incoming = some body.request ∧
      (StageTrace.items row)[position]? = some item ∧ item.request = body.request ∧
      model.source.code.law.Valid item.before item.request ∧
      item.request.signer = model.source.code.siteParty body.ballot.key ∧
      body.ballot.fee = flowAt (model.source.code.law.actualDebit item.before item.request)
        (model.source.code.siteParty body.ballot.key) vocabulary.feeUnit ∧ 0 < body.ballot.fee) ∧
    (authority model start past rival vocabulary encoding law scope threshold).current = Native.Authority.fullGenerate
      (actualBound model start past rival vocabulary encoding law)
      ((final model start past rival vocabulary encoding law).source.history.length + 1 +
        (final model start past rival vocabulary encoding law).cut) ∧
    HEq (runtime model start past rival vocabulary encoding law scope threshold).tick.generated.wholeLedgerWriteBack
      ((runtime model start past rival vocabulary encoding law scope threshold).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtime model start past rival vocabulary encoding law scope threshold).current.visit.current) ∧
    (runtime model start past rival vocabulary encoding law scope threshold).tick.nextCurrent =
      (facade model start past rival vocabulary encoding law scope threshold).process.stateAt
        ((facade model start past rival vocabulary encoding law scope threshold).process.successor
          (runtime model start past rival vocabulary encoding law scope threshold).state) := by
  have member := every_attested_response_is_in_the_original_root_request_face model start past rival vocabulary encoding law scope threshold row inside position body made
  obtain ⟨legacy, item, actual, request, _⟩ :=
    RequestAttestation.issued_binds_the_complete_original_request vocabulary row position body made
  obtain ⟨site, oldItem, activated, oldActual, valid, signer, _, _, key, _, _, fee, paid⟩ :=
    StageBudget.issued_has_an_owned_valid_paid_origin vocabulary row position body.ballot legacy
  have identical : oldItem = item := Option.some.inj (oldActual.symm.trans actual)
  subst oldItem
  have requested : body.request ∈ row.submitted := by
    rw [← model.source.code.law.inventory_requests_exact row.before.current 0 row.submitted]
    exact List.mem_map.mpr ⟨item, List.mem_of_getElem? actual, request⟩
  obtain ⟨earlier, protocol, opponent, suffix, _, rowSame⟩ := StageTrace.every_record_retains_its_actual_stage start (stages model start past rival) row inside
  subst row
  change protocol = RequestResponse.protocol at generated
  subst protocol
  rw [RequestResponse.an_actual_owned_response_submits_only_its_current_local_word _ opponent site activated] at requested
  obtain ⟨incoming, read, reply, _, _⟩ :=
    RequestResponse.every_submitted_reply_has_its_local_input_and_own_registered_signer site _ body.request requested
  have factor := (facade model start past rival vocabulary encoding law scope threshold).readoutAt_factorizes
    (runtime model start past rival vocabulary encoding law scope threshold) .readback
  refine ⟨member, ⟨incoming, item, ?_, ?_, actual, request, valid, ?_, ?_, paid⟩,
    (authority model start past rival vocabulary encoding law scope threshold).current_exact, factor.2.2.1, factor.2.2.2.2⟩
  · simpa only [StageTrace.material, key] using read
  · simpa only [key] using reply
  · simpa only [key] using signer
  · simpa only [key] using fee

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RequestResponseRuntime

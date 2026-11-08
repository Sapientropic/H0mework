import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningReception
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SuccessorSigningConsumer

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RecursiveSigningSource

abbrev model := SuccessorSigningConsumer.model
abbrev start := SuccessorSigningConsumer.start
abbrev base := RenewedDispatchSource.vocabulary SuccessorSigningConsumer.point
abbrev law := SuccessorSigningConsumer.law
def seed := initial model start
def first := segment model start seed SuccessorSigningConsumer.commands
def installed := next model start seed SuccessorSigningConsumer.commands

attribute [local irreducible] SuccessorSigningSource.Material.generate HeaderTransport.verify
 HeaderReception.run ActorStageEnvelope.affected CachedWorkDispatch.wires

theorem the_recursive_producer_starts_from_the_same_paid_history :
 installed.current model start = SuccessorSigningConsumer.final ∧
 installed.stages = SuccessorSigningConsumer.actual.stages ∧ installed.archive=[first] :=
 first_round_is_the_same_native_execution model start SuccessorSigningConsumer.commands

theorem the_first_issuing_context_is_the_original_unmodified_context :
 first.origin=start ∧ first.vocabulary model base=SuccessorSigningConsumer.vocabulary ∧
 first.stages=SuccessorSigningConsumer.actual.stages := ⟨rfl,rfl,rfl⟩

theorem the_recursive_domain_has_four_real_paid_messages_and_remaining_resources :
 (first.wires model base).length=4 ∧ (EventStep.seed (installed.current model start)).remaining=22 ∧
 (installed.current model start).cut=114 := by
 have facts := SuccessorSigningConsumer.actual_fuel_and_packet_growth_are_paid_by_the_same_retained_endpoint
 have context := the_first_issuing_context_is_the_original_unmodified_context
 have wires : first.wires model base = HeaderTransport.wires SuccessorSigningConsumer.vocabulary
  start SuccessorSigningConsumer.actual.stages :=
  congrArg₂ (fun origin stages => HeaderTransport.wires (SuccessorSigningSource.vocabulary model origin base) origin stages)
   context.1 context.2.2
 have endpoint := the_recursive_producer_starts_from_the_same_paid_history.1
 exact ⟨(congrArg List.length wires).trans facts.2.2.2.2,
  (congrArg (fun cursor : Cursor model.source.code => (EventStep.seed cursor).remaining) endpoint).trans facts.2.1,
  (congrArg (fun cursor : Cursor model.source.code => cursor.cut) endpoint).trans facts.2.2.2.1⟩

abbrev descendants (control : Controller model start) (rounds : Nat) := RecursiveSigningSource.run model start installed control rounds
abbrev endpoint (control : Controller model start) (rounds : Nat) := (descendants control rounds).current model start
abbrev dynamicDescendants (control : State model start → Nat × Policy model) (rounds : Nat) :=
 RecursiveSigningSource.runDynamic model start installed control rounds

theorem arbitrary_later_control_retains_the_actual_original_signing_context
 (control : Controller model start) (rounds : Nat) :
 first ∈ (descendants control rounds).archive ∧
 installed.stages <+: (descendants control rounds).stages := by
 have kept := arbitrary_later_control_keeps_all_prior_issuing_contexts model start installed control rounds
 exact ⟨kept.2.subset (List.mem_singleton_self _),kept.1⟩

theorem all_original_financial_accounts_survive_arbitrary_later_control
 (control : Controller model start) (rounds ordinal : Nat) (bounded : ordinal ≤ EventStep.boundary start) :
 Native.Coupling.Match model.source.code start.source.input (endpoint control rounds).source.input
  (Financial.accountAt start.source.input ordinal)
  (Financial.accountAt (endpoint control rounds).source.input ordinal) :=
 every_archived_origin_keeps_the_complete_financial_prefix model start _ ordinal bounded

theorem every_cross_round_receipt_is_paid_in_the_actual_final_native_inventory
 (control : Controller model start) (rounds : Nat)
 (origin : Segment model) (member : origin ∈ (descendants control rounds).archive)
 (receiver : Fin model.source.code.sites) (receipt : HeaderReception.Receipt (code := model.source.code))
 (accepted : receipt ∈ (RecursiveSigningReception.observed model base law start (descendants control rounds) origin receiver).receipts) :
 ∃ row ∈ (descendants control rounds).rows model start, ∃ position,
  StageBudget.issued (origin.vocabulary model base) row position=some receipt.wire.ballot ∧
  (Financial.inventoryAt (endpoint control rounds).source.input
   (ProgrammeHistory.visitAt (endpoint control rounds).source.input (EventStep.boundary row.cursor))).filterMap
    (Financial.InstructionOrigin.instruction? (endpoint control rounds).source.input)=StageTrace.items row := by
 have paid := RecursiveSigningReception.receipt_has_its_own_original_paid_ballot model base law start _ origin receiver receipt accepted
 obtain ⟨row,inside,position,made⟩ := StageBudget.ledger_origin _ _ _ receipt.wire.ballot paid
 have actual := an_archived_row_is_in_the_actual_cumulative_history model start _ origin member row inside
 exact ⟨row,actual,position,made,StageTrace.final_financial_inventory_is_the_original_record_items start _ row actual⟩

theorem every_cross_round_receipt_has_a_real_paid_delivery
 (control : Controller model start) (rounds : Nat) (origin : Segment model)
 (receiver : Fin model.source.code.sites) (receipt : HeaderReception.Receipt (code := model.source.code))
 (accepted : receipt ∈ (RecursiveSigningReception.observed model base law start (descendants control rounds) origin receiver).receipts) :
 ∃ row ∈ (descendants control rounds).rows model start,
  receipt.delivery=row.cursor.cut ∧ HeaderReception.delivered row receipt.wire.serial=true ∧
  HeaderReception.matchingPacket row receipt.wire=true ∧ row.cursor.cut ≤ receipt.wire.sendCut+law.maxDelay ∧
  (∀ item ∈ StageTrace.items row, model.source.code.law.Valid item.before item.request) :=
 RecursiveSigningReception.every_receipt_has_an_actual_paid_delivery_in_the_cumulative_history model base law start _ origin receiver receipt accepted

theorem actual_cross_round_decisions_agree
 (control : Controller model start) (rounds index : Nat)
 (left right : Fin model.source.code.sites) (scope : Scope) (threshold : Nat) (a b : Bool)
 (one : RecursiveSigningReception.produce model base law start (descendants control rounds) index left scope threshold=.decided a)
 (two : RecursiveSigningReception.produce model base law start (descendants control rounds) index right scope threshold=.decided b) : a=b :=
 RecursiveSigningReception.produced_decisions_agree_across_receivers_after_arbitrary_rounds model base law start _ index left right scope threshold a b one two

theorem source_birth_rejects_a_relabelled_predecessor_ballot
 (origin : Segment model) (body : StageBudget.Ballot (code := model.source.code)) (early : body.cut<origin.origin.cut) :
 body ∉ StageBudget.ledger (origin.vocabulary model base) origin.origin origin.stages := by
 intro member
 have born := (each_new_ballot_is_born_in_its_own_actual_phase model base origin body member).1
 omega

theorem deleting_the_issuing_archive_blocks_even_with_the_same_actual_native_endpoint
 (receiver : Fin model.source.code.sites) (scope : Scope) (threshold : Nat) :
 RecursiveSigningReception.produce model base law SuccessorSigningConsumer.final
  (initial model SuccessorSigningConsumer.final) 0 receiver scope threshold=.blocked .missingQuorum := rfl

theorem cross_round_receipt_origins_are_never_counted_twice
 (control : Controller model start) (rounds : Nat) (origin : Segment model) (receiver : Fin model.source.code.sites) :
 ((RecursiveSigningReception.observed model base law start (descendants control rounds) origin receiver).receipts.map
  fun receipt => (receipt.wire.ballot.cut,receipt.wire.ballot.position)).Nodup :=
 RecursiveSigningReception.duplicate_origin_cannot_add_another_receipt model base law origin receiver _ _ _ (by simp)

theorem every_dynamic_descendant_keeps_the_original_whole_ledger_and_own_generated_next
 (control : State model start → Nat × Policy model) (rounds : Nat) :
 PaidOriginQueueConsumer.NativeContinuation model ((dynamicDescendants control rounds).current model start) := by
 unfold PaidOriginQueueConsumer.NativeContinuation
 exact (WithdrawalInquiryRuntime.the_actual_inquiry_source_consumes_all_original_histories_ledger_and_own_next
  model ((dynamicDescendants control rounds).current model start)).2.2.2

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecursiveSigningConsumer

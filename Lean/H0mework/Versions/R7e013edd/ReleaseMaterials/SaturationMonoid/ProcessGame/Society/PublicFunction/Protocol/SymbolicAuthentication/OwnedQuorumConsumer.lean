import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumCensus
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumEvidence
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EncodingAgreement
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 24000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open OwnedQuorumSource OwnedQuorumDomain
abbrev finished (control : Controller) (external : Nat → Opponent code) := actual control external window

theorem all_owned_signing_supply_and_delivery_controls_generate_the_original_quorum
    (control : Controller) (external : Nat → Opponent code) (within : Within control external window) :
    result (finished control external) = .decided true ∧
      (observed (finished control external)).receipts.length = 2 ∧
      ((finished control external).rows.all fun row => (StageTrace.audit row).all Prod.snd) = true ∧
      (finished control external).state.current.stock 0 .feedstock = 0 ∧
      (finished control external).state.current.stock 1 .service = 0 ∧
      (finished control external).state.current.claims () 1 2 = 7 ∧
      ((ballots (finished control external)).filter fun body => decide (body.scope = RenewedQuorumSource.slot true)).length = 2 := by
  obtain ⟨node,member,same⟩ := every_actual_local_and_network_controller_has_a_generated_branch control external window within
  have success := OwnedQuorumCensus.generated_success node member
  have one := every_generated_node_is_source_generated window node member
  have two := every_actual_cut_is_source_generated control external window
  have states := related_states node _ one two same
  have receipts := related_observations node _ one two same
  have bodies := related_ballots node _ one two same
  have audits : (node.rows.all fun row => (StageTrace.audit row).all Prod.snd) =
      ((finished control external).rows.all fun row => (StageTrace.audit row).all Prod.snd) := by
    have rows := EnvelopeObservation.communication same.1.2
    rw [← one.2.2,← two.2.2] at rows
    generalize node.rows = a at rows ⊢
    generalize (finished control external).rows = b at rows ⊢
    induction rows with
    | nil => rfl
    | @cons a b _ _ item rest ih =>
      have head : StageTrace.audit a = StageTrace.audit b := by
        simp only [StageTrace.audit,StageTrace.items,item.before,item.submitted]
      simp only [List.all_cons,head,ih]
  rw [related_results node _ one two same,receipts,audits,states,bodies] at success
  exact success

theorem every_actual_admitted_delivery_is_paid_without_a_funding_premise
    (control : Controller) (external : Nat → Opponent code) (within : Within control external window)
    (row : StageTrace.Record (code := code)) (inside : row ∈ (finished control external).rows)
    (serial : Nat) (packet : code.Packet) (present : row.before.frame.sent[serial]? = some packet)
    (delivered : StageReception.delivered row serial = true) : QueueMemoryEffect.paid row packet := by
  have completed := all_owned_signing_supply_and_delivery_controls_generate_the_original_quorum control external within
  have audited := List.all_eq_true.mp completed.2.2.1 row inside
  have items : ∀ item ∈ StageTrace.items row, code.law.Valid item.before item.request := by
    simpa only [StageTrace.audit,List.all_map,Function.comp_def,List.all_eq_true,decide_eq_true_eq] using audited
  have source := every_actual_cut_is_source_generated control external window
  have actual : row ∈ StageTrace.records start (finished control external).stages := by
    rwa [← source.2.2]
  have word := StageReception.actual_delivery_submits_the_original_cost start (finished control external).stages
    row actual serial packet present delivered
  unfold QueueMemoryEffect.paid
  rw [← word]
  exact items

theorem every_actual_receipt_retains_its_original_paid_ballot
    (control : Controller) (external : Nat → Opponent code) (receipt : StageReception.Receipt (code := code))
    (inside : receipt ∈ (observed (finished control external)).receipts) :
    receipt.wire.ballot ∈ StageBudget.ledger vocabulary start (finished control external).stages :=
  StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary (encoding (finished control external)) reception start _ 2 _ receipt inside

theorem actual_decisions_agree_even_when_actual_signing_times_and_encodings_differ
    (control : Controller) (external : Nat → Opponent code) (within : Within control external window)
    (other : List (EventHistory.Stage (code := code))) (otherEncoding : StageTransport.Encoding (code := code))
    (otherLaw : StageReception.Law code) (receiver : Fin code.sites) (value : Bool)
    (decided : InterfaceQuorum.produce start vocabulary otherEncoding otherLaw other receiver
      (RenewedQuorumSource.slot true) 2 = .decided value) : value = true :=
  EncodingAgreement.original_decisions_agree_with_distinct_actual_encodings start vocabulary otherEncoding
    (encoding (finished control external)) otherLaw reception other (finished control external).stages receiver 2 _ 2 value true decided
      (all_owned_signing_supply_and_delivery_controls_generate_the_original_quorum control external within).1

abbrev facade (control : Controller) (external : Nat → Opponent code) :=
  Feedback.Runtime.facade (finished control external).cursor.source (finished control external).cursor.entry rfl rfl

theorem every_actual_supply_and_delivery_consumes_its_whole_ledger_and_literal_next
    (control : Controller) (external : Nat → Opponent code) :
    let runtime := (facade control external).seed.advance (EventStep.boundary (finished control external).cursor)
    (∀ row ∈ (finished control external).rows,
      (Financial.inventoryAt (finished control external).cursor.source.input
        (ProgrammeHistory.visitAt (finished control external).cursor.source.input (EventStep.boundary row.cursor))).filterMap
          (Financial.InstructionOrigin.instruction? (finished control external).cursor.source.input) = StageTrace.items row) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (facade control external).process.stateAt ((facade control external).process.successor runtime.state) := by
  have valid := every_actual_cut_is_source_generated control external window
  have rooted := (facade control external).readoutAt_factorizes
    ((facade control external).seed.advance (EventStep.boundary (finished control external).cursor)) .feedback
  refine ⟨?_,rooted.2.2.1,rooted.2.2.2.2⟩
  intro row member
  rw [valid.2.2] at member
  rw [valid.1]
  exact StageTrace.final_financial_inventory_is_the_original_record_items start _ row member

theorem every_owned_omission_retains_source_evidence_alongside_a_successful_decision
    (control : Controller) (external : Nat → Opponent code) (within : Within control external window) :
    result (finished control external) = .decided true ∧
      (finished control external).omissions.length ≤ controlCapacity ∧
      ∀ entry ∈ (finished control external).omissions,
        OwnedQuorumEvidence.Witness control external window entry :=
  ⟨(all_owned_signing_supply_and_delivery_controls_generate_the_original_quorum control external within).1,
    every_actual_control_is_within_the_original_clock_capacity control external window,
    fun entry inside => OwnedQuorumEvidence.every_actual_omission_is_indexed_by_its_actual_source_prefix
      control external window entry inside⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumConsumer

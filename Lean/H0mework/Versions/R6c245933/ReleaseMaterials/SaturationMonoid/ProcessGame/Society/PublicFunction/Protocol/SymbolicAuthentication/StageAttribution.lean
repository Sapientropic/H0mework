import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountability

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountability

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (cursor : Cursor code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := code)) (law : StageReception.Law code)

def OwnedOrigin (stages : List (EventHistory.Stage (code := code))) (body : StageBudget.Ballot (code := code)) : Prop :=
  ∃ row ∈ StageTrace.records cursor stages, ∃ position item,
    StageBudget.issued vocabulary row position = some body ∧ (StageTrace.items row)[position]? = some item ∧
      StageTrace.activation row = some body.key ∧ code.law.Valid item.before item.request ∧
      item.request.signer = code.siteParty body.key ∧
      body.fee = flowAt (code.law.actualDebit item.before item.request) (code.siteParty body.key) vocabulary.feeUnit ∧
      0 < body.fee ∧ (body.scope, body.choice) ∈ StageBudget.labels vocabulary row body.key ∧
      (Financial.inventoryAt (EventHistory.execute cursor stages).source.input
        (ProgrammeHistory.visitAt (EventHistory.execute cursor stages).source.input (EventStep.boundary row.cursor))).filterMap
          (Financial.InstructionOrigin.instruction? (EventHistory.execute cursor stages).source.input) = StageTrace.items row ∧
      ∃ pastStages protocol rival suffix, stages = pastStages ++ (protocol, rival) :: suffix ∧
        row = StageTrace.material (EventHistory.execute cursor pastStages) protocol rival

theorem receipt_has_its_owned_control_payment_and_original_financial_inventory
    (stages : List (EventHistory.Stage (code := code))) (receiver : Fin code.sites)
    (receipt : Receipt (code := code)) (inside : receipt ∈ receipts cursor vocabulary encoding law stages receiver) :
    OwnedOrigin cursor vocabulary stages receipt.wire.ballot := by
  have issued := StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law cursor stages receiver stages.length receipt inside
  obtain ⟨row, member, position, made⟩ := StageBudget.ledger_origin vocabulary cursor stages _ issued
  obtain ⟨site, item, owned, actual, valid, signer, _, _, key, _, _, fee, positive⟩ :=
    StageBudget.issued_has_an_owned_valid_paid_origin vocabulary row position _ made
  have localWord := StageBudget.issued_is_in_the_actual_installed_local_word vocabulary cursor stages row member position _ made
  refine ⟨row, member, position, item, made, actual, localWord.2.1, valid, ?_, ?_, positive, localWord.2.2,
    StageTrace.final_financial_inventory_is_the_original_record_items cursor stages row member,
    StageTrace.every_record_retains_its_actual_stage cursor stages row member⟩
  · simpa only [key] using signer
  · simpa only [key] using fee

theorem incident_receipts_are_in_the_same_whole_history
    (stages : List (EventHistory.Stage (code := code))) (entry : Incident cursor vocabulary encoding law)
    (inside : entry ∈ ledger cursor vocabulary encoding law stages) :
    entry.pair.1 ∈ receipts cursor vocabulary encoding law stages entry.receiver ∧
      entry.pair.2 ∈ receipts cursor vocabulary encoding law stages entry.receiver := by
  have original := query_sound _ entry.slot entry.pair entry.detected
  have prefixHistory : entry.birthStages <+: stages := by
    simpa only [List.nil_append] using every_generated_incident_has_its_original_birth_prefix cursor vocabulary encoding law [] stages entry inside
  obtain ⟨more, same⟩ := prefixHistory
  rw [← same]
  have persisted := StagePrefix.receipts_survive_actual_extension cursor entry.birthStages more vocabulary encoding law entry.receiver
  exact ⟨persisted.subset original.1, persisted.subset original.2.1⟩

theorem every_incident_has_two_actual_owned_paid_origins_and_two_actual_deliveries
    (stages : List (EventHistory.Stage (code := code))) (entry : Incident cursor vocabulary encoding law)
    (inside : entry ∈ ledger cursor vocabulary encoding law stages) :
    OwnedOrigin cursor vocabulary stages entry.pair.1.wire.ballot ∧
      OwnedOrigin cursor vocabulary stages entry.pair.2.wire.ballot ∧
      (∀ receipt ∈ [entry.pair.1, entry.pair.2], ∃ row seen,
        (StageTrace.records cursor stages)[receipt.index]? = some row ∧ receipt.delivery = row.cursor.cut ∧
          receipt.index < stages.length ∧ StageReception.check vocabulary encoding law cursor stages entry.receiver row seen receipt.wire = .accepted receipt.wire) ∧
      entry.pair.1.wire.ballot.key = entry.slot.1 ∧ entry.pair.1.wire.ballot.scope = entry.slot.2 ∧
      StageBudget.conflicts entry.pair.1.wire.ballot entry.pair.2.wire.ballot = true := by
  have received := incident_receipts_are_in_the_same_whole_history cursor vocabulary encoding law stages entry inside
  refine ⟨receipt_has_its_owned_control_payment_and_original_financial_inventory cursor vocabulary encoding law stages _ _ received.1,
    receipt_has_its_owned_control_payment_and_original_financial_inventory cursor vocabulary encoding law stages _ _ received.2, ?_,
    (query_sound _ entry.slot entry.pair entry.detected).2.2⟩
  intro receipt member
  have actual : receipt ∈ receipts cursor vocabulary encoding law stages entry.receiver := by
    rcases List.mem_cons.mp member with same | second
    · exact same ▸ received.1
    · have same := List.mem_singleton.mp second
      exact same ▸ received.2
  exact StageReception.every_receipt_retains_its_actual_delivery vocabulary encoding law cursor stages entry.receiver stages.length receipt actual

theorem every_incident_is_within_its_actual_source_capacity
    (stages : List (EventHistory.Stage (code := code))) (entry : Incident cursor vocabulary encoding law)
    (inside : entry ∈ ledger cursor vocabulary encoding law stages) : entry.slot.1 ∈ StageBudget.capacityKeys vocabulary cursor stages := by
  have received := incident_receipts_are_in_the_same_whole_history cursor vocabulary encoding law stages entry inside
  have facts := query_sound _ entry.slot entry.pair entry.detected
  obtain ⟨key, scope, different⟩ := of_decide_eq_true facts.2.2.2.2
  rw [← facts.2.2.1]
  exact StageBudget.every_actual_equivocation_is_covered_by_the_source_capacity_budget vocabulary cursor stages _ _
    (StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law cursor stages _ _ _ received.1)
    (StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encoding law cursor stages _ _ _ received.2) key scope different

theorem every_incident_is_in_the_genesis_admission_budget
    (base : Code Party Good Port (Mandate.State Party Technology) Instrument)
    (start : Cursor (AdmissionCode.lift base))
    (encode : StageTransport.Encoding (code := AdmissionCode.lift base)) (reception : StageReception.Law (AdmissionCode.lift base))
    (stages : List (EventHistory.Stage (code := AdmissionCode.lift base)))
    (entry : Incident start vocabulary encode reception) (inside : entry ∈ ledger start vocabulary encode reception stages) :
    entry.slot.1 ∈ AdmissionCode.affected base := by
  have received := incident_receipts_are_in_the_same_whole_history start vocabulary encode reception stages entry inside
  have facts := query_sound _ entry.slot entry.pair entry.detected
  obtain ⟨key, _, different⟩ := of_decide_eq_true facts.2.2.2.2
  rw [← facts.2.2.1]
  exact AdmissionEnvelope.every_actual_equivocator_is_in_the_genesis_admission_budget base vocabulary start stages _ _
    (StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encode reception start stages _ _ _ received.1)
    (StageQuorum.supporting_receipt_has_actual_owned_paid_origin vocabulary encode reception start stages _ _ _ received.2) key different

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountability

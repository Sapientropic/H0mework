import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountabilityRuntime
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageDutyControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountabilityControls

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

abbrev foundation := AdmissionControls.foundation
abbrev start := AdmissionControls.start
abbrev vocabulary := AdmissionControls.vocabulary
abbrev encoding := AdmissionControls.encoding
abbrev law := AdmissionControls.law
abbrev slot := AdmissionControls.slot
abbrev normal := AdmissionControls.stages .normal
abbrev events (stages) := StageAccountability.ledger start vocabulary encoding law stages
def coordinates (stages) := (events stages).map fun entry => (entry.receiver, entry.slot.1, entry.slot.2, entry.pastStages.length)

theorem an_actual_local_conflict_generates_one_incident_at_its_actual_second_delivery :
    coordinates normal = [(1, 0, slot, 13)] ∧
      (events normal).map (fun entry => (entry.pair.1.wire.ballot, entry.pair.2.wire.ballot)) =
        [(AdmissionControls.first, AdmissionControls.third)] ∧
      coordinates (normal.take 9) = [] ∧ StageBudget.evidenceKeys vocabulary start (normal.take 9) = {0} := by
  decide +kernel

theorem withholding_or_duplicate_delivery_does_not_fabricate_local_knowledge :
    coordinates (AdmissionControls.stages .withholdLast) = [] ∧
      coordinates (AdmissionControls.stages .duplicate) = [] ∧
      coordinates (AdmissionControls.stages .noDelivery) = [] ∧
      AdmissionQuorum.produce AdmissionControls.base vocabulary encoding law start
        (AdmissionControls.stages .withholdLast) 1 slot 2 = .decided true := by
  decide +kernel

theorem neither_a_missing_receipt_nor_a_blocked_quorum_rewrites_the_incident :
    StageAccountability.query (AdmissionControls.expected.take 2) (0, slot) = none ∧
      StageAccountability.query [AdmissionControls.expected[2]'(by decide)] (0, slot) = none ∧
      AdmissionQuorum.produce AdmissionControls.base vocabulary encoding law start normal 1 slot 3 = .blocked ∧
      coordinates normal = [(1, 0, slot, 13)] := by
  decide +kernel

theorem forged_expired_late_and_deleted_sources_do_not_create_local_incidents :
    (StageAccountability.ledger start vocabulary StageQueueControls.forged law normal).isEmpty = true ∧
      (StageAccountability.ledger start vocabulary encoding StageQueueControls.staleLaw normal).isEmpty = true ∧
      (StageAccountability.ledger start vocabulary encoding StageQueueControls.lateLaw normal).isEmpty = true ∧
      (events []).isEmpty = true ∧
      StageBudget.verify vocabulary start normal {AdmissionControls.third with actor := true} = false ∧
      StageBudget.verify vocabulary start normal {AdmissionControls.third with key := 1} = false := by
  decide +kernel

abbrev phaseReceipt : StageReception.Receipt (code := AdmissionControls.code) :=
  {AdmissionControls.expected[2]'(by decide) with wire :=
    {AdmissionControls.thirdWire with ballot := {AdmissionControls.third with scope := {slot with phase := 1}}}}
theorem different_phase_signatures_do_not_form_a_same_scope_incident :
    StageAccountability.query [AdmissionControls.expected[0]'(by decide), phaseReceipt] (0, slot) = none := by
  decide +kernel

theorem arbitrary_later_actual_stages_preserve_the_original_incident
    (more : List (EventHistory.Stage (code := AdmissionControls.code))) :
    events normal <+: events (normal ++ more) := by
  change StageAccountability.ledger start vocabulary encoding law normal <+:
    StageAccountability.ledger start vocabulary encoding law (normal ++ more)
  rw [StageAccountability.ledger_extends_by_its_generated_next]
  exact List.prefix_append _ _

abbrev entry := (events normal).head (by decide +kernel)
theorem later_actual_stages_do_not_readmit_the_same_receiver_key_and_scope
    (more : List (EventHistory.Stage (code := AdmissionControls.code)))
    (stage : EventHistory.Stage (code := AdmissionControls.code)) :
    StageAccountability.birth start vocabulary encoding law (entry.birthStages ++ more) stage entry.receiver entry.slot = none :=
  StageAccountability.later_stages_do_not_readmit_an_already_observed_incident start vocabulary encoding law entry more stage

abbrev protocols := StageQueueControls.protocols
abbrev full := StageAccountabilityRuntime.full foundation start normal protocols
abbrev rooted := StageAccountabilityRuntime.rooted foundation start normal protocols vocabulary encoding law slot 2
abbrev runtime := StageAccountabilityRuntime.activated foundation start normal protocols vocabulary encoding law slot 2
  (StageAccountabilityRuntime.ordinal foundation start normal protocols)

theorem the_independent_root_consumer_uses_actual_attribution_original_duties_and_same_next :
    ∃ incident ∈ rooted.incidents,
      StageAccountability.OwnedOrigin start vocabulary full incident.pair.1.wire.ballot ∧
      StageAccountability.OwnedOrigin start vocabulary full incident.pair.2.wire.ballot ∧
      incident.slot.1 ∈ AdmissionCode.affected AdmissionControls.base ∧
      rooted.source.source.source.decisions 1 = .decided true ∧
      rooted.source.duties = (StageDutyRuntime.rooted foundation start normal protocols vocabulary encoding law slot 2).duties ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (StageAccountabilityRuntime.facade foundation start normal protocols vocabulary encoding law slot 2).process.stateAt
        ((StageAccountabilityRuntime.facade foundation start normal protocols vocabulary encoding law slot 2).process.successor runtime.state) := by
  have found : ∃ pair, StageAccountability.query (StageAccountability.receipts start vocabulary encoding law full 1) (0, slot) = some pair := by
    refine ⟨(AdmissionControls.expected[0]'(by decide), AdmissionControls.expected[2]'(by decide)), ?_⟩
    decide +kernel
  obtain ⟨incident, inside, _, _⟩ := StageAccountability.every_locally_observed_conflict_generates_an_incident
    start vocabulary encoding law full 1 (0, slot) found
  have consumed := StageAccountabilityRuntime.the_original_root_consumes_local_incidents_source_budget_duties_ledger_and_next
    foundation start normal protocols vocabulary encoding law slot 2 incident inside
  rcases consumed with ⟨one, two, _, _, budget, retained, _, _, _, whole, next⟩
  exact ⟨incident, inside, one, two, budget, by decide +kernel, retained, whole, next⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.StageAccountabilityControls

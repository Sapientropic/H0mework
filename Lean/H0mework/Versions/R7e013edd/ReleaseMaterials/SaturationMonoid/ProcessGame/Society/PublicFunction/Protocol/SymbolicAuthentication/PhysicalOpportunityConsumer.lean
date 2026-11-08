import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityBudget

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityConsumer
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem primitive_physical_opportunities_force_the_original_service_and_same_roots_next
    (rounds : Nat) (past : JointResponse.Stages model)
    (enough : PhysicalOpportunityBudget.remaining model start vocabulary encoding law past <
      PhysicalOpportunityClock.physical model start vocabulary encoding law rounds past) :
    let full := (JointResponseRun.run model start vocabulary encoding law rounds past).stages
    let final := EventHistory.execute start full
    let runtime := WithdrawalInquiryRuntime.runtime model final
    ∃ ready : PriorityServiceTrace.Ready model start vocabulary encoding law rounds past,
      PriorityServiceTrace.produce model start vocabulary encoding law rounds past = .served ready ∧
      past <+: full ∧ past.length ≤ ready.index ∧ ready.index < full.length ∧
      RejectionService.ServedAt model start vocabulary encoding law full ready.index ∧
      (∀ original : Native.Authority.Challenge (WithdrawalInquiryRuntime.native model final),
        let history := Mandate.Challenge.through (WithdrawalInquiryRuntime.family model final)
          (WithdrawalInquiryRuntime.sourceIndex model final) original (WithdrawalInquiryRuntime.depth model final + 2)
        history.state.current.history = history.state.generated.events) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
      runtime.tick.nextCurrent = (WithdrawalInquiryRuntime.facade model final).process.stateAt
        ((WithdrawalInquiryRuntime.facade model final).process.successor runtime.state) := by
  dsimp only
  cases selected : PriorityServiceTrace.produce model start vocabulary encoding law rounds past with
  | served ready =>
    have actual := PriorityServiceTrace.the_first_source_selected_service_is_an_actual_row
      model start vocabulary encoding law rounds past ready.index ready.selected
    have rooted := PriorityServiceConsumer.the_original_root_consumes_the_generated_service_without_erasing_native_responsibilities
      model start vocabulary encoding law rounds past ready
    exact ⟨ready, rfl, rooted.1, actual.1, actual.2.1, rooted.2⟩
  | noRejectionEdge absent budget =>
    have bounded := PhysicalOpportunityBudget.no_selected_rejection_edge_has_a_source_generated_physical_opportunity_bound
      model start vocabulary encoding law rounds past absent
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityConsumer

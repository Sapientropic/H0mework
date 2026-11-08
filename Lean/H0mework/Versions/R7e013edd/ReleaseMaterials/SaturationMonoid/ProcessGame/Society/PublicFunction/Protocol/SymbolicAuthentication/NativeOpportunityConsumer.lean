import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunitySearch

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunityConsumer
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (foundation : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor (AdmissionRuntime.profile foundation).source.code)
  (past : NativeReviewRun.Stages (AdmissionRuntime.profile foundation))
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := (AdmissionRuntime.profile foundation).source.code))
  (law : StageReception.Law (AdmissionRuntime.profile foundation).source.code) (scope : Scope) (threshold : Nat)

theorem the_original_root_consumes_the_generated_opportunity_and_its_actual_terminal_row
    (answer : NativeOpportunitySearch.Ready (AdmissionRuntime.profile foundation) start past vocabulary encoding law) :
    let model := AdmissionRuntime.profile foundation
    let stages := NativeOpportunitySearch.full model start past vocabulary encoding law answer
    let runtime := AdmissionRuntime.activated foundation start stages vocabulary encoding law scope threshold
      (AdmissionRuntime.ordinal foundation start stages)
    let authority := AdmissionRuntime.authority foundation start stages vocabulary encoding law scope threshold
    stages = (JointResponseRun.run model start vocabulary encoding law (answer.offset + 1) past).stages ∧
    stages <+: (JointResponseRun.produce model start vocabulary encoding law past).stages ∧
    NativeOpportunity.beforePending model start answer.prior
      answer.answer.native.ready answer.answer.native.original = true ∧
    (∃ row ∈ authority.current.challenges, row.1 = answer.answer.native.original ∧ row.2.isPending _ _ = false) ∧
    HEq runtime.tick.generated.wholeLedgerWriteBack
      (runtime.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt runtime.current.visit.current) ∧
    runtime.tick.nextCurrent = (AdmissionRuntime.facade foundation start stages vocabulary encoding law scope threshold).process.stateAt
      ((AdmissionRuntime.facade foundation start stages vocabulary encoding law scope threshold).process.successor runtime.state) := by
  dsimp only
  have settled := NativeOpportunity.every_selected_opportunity_terminates_the_actual_original_inventory_row
    (AdmissionRuntime.profile foundation) start
    answer.prior answer.answer.native
  have installed := (AdmissionRuntime.facade foundation start
    (NativeOpportunitySearch.full (AdmissionRuntime.profile foundation) start past vocabulary encoding law answer) vocabulary encoding law scope threshold).readoutAt_factorizes
    (AdmissionRuntime.activated foundation start
      (NativeOpportunitySearch.full (AdmissionRuntime.profile foundation) start past vocabulary encoding law answer) vocabulary encoding law scope threshold
      (AdmissionRuntime.ordinal foundation start (NativeOpportunitySearch.full (AdmissionRuntime.profile foundation) start past vocabulary encoding law answer))) .communication
  refine ⟨NativeOpportunitySearch.every_ready_opportunity_is_the_next_actual_original_run_prefix
      (AdmissionRuntime.profile foundation) start past vocabulary encoding law answer,
    NativeOpportunitySearch.every_ready_opportunity_is_a_prefix_of_the_original_source_budget_run
      (AdmissionRuntime.profile foundation) start past vocabulary encoding law answer,
    answer.answer.native.pending, ?_, installed.2.2.1, installed.2.2.2.2⟩
  rw [(AdmissionRuntime.authority foundation start
    (NativeOpportunitySearch.full (AdmissionRuntime.profile foundation) start past vocabulary encoding law answer) vocabulary encoding law scope threshold).current_exact]
  exact settled

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeOpportunityConsumer

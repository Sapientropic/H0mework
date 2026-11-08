import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplySource

set_option autoImplicit false
set_option maxRecDepth 100000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplyConsumer
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open WholeCursorLaw
open WholeCursorSupplySource

variable (saved : Cursor code) (original : saved.side = .original)
  (submit : Bool) (rival : Opponent (active saved))

include original in
theorem every_resumption_keeps_the_entire_actual_live_state :
    EventStep.seed (start saved) = Extension.state code
      (CatalogueHandoffSource.supply code (AtomicWorkSource.catalogue code (batch saved))) (EventStep.seed saved) :=
  CatalogueHandoffSource.seed code (AtomicWorkSource.catalogue code (batch saved)) saved original

theorem the_actual_source_batch_has_its_one_original_raw_occurrence
    (success : assess saved submit rival = .executed) :
    ProgrammeSource.rawEvent (after saved submit rival).source.input
      (ProgrammeHistory.visitAt (after saved submit rival).source.input
        (EventStep.boundary (start saved))).current = batch saved :=
  AtomicWorkConsumer.executed_batch_has_one_raw_occurrence code (batch saved) saved submit rival success

abbrev every_future_keeps_the_original_financial_items
    (future : List (EventHistory.Stage (code := active saved))) :=
  AtomicWorkConsumer.the_final_ledger_consumes_the_original_batch code (batch saved) saved submit rival future

abbrev native (future : List (EventHistory.Stage (code := active saved))) :=
  StageRuntime.the_final_root_consumes_actual_budget_native_responsibility_ledger_and_next
    (bound saved) (start saved) ((work saved submit,rival)::future) vocabulary

abbrev priorFinancialPrefix (future : List (EventHistory.Stage (code := active saved))) :=
  CatalogueHandoffSource.completeFinancialPrefix code (AtomicWorkSource.catalogue code (batch saved))
    saved original future
end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.WholeCursorSupplyConsumer

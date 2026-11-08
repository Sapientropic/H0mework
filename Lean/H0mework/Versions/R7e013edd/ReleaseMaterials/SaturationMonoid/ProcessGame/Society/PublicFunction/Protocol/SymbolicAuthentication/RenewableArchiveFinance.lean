import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveFinance
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewableArchiveSource

variable {Party Good Port Technology Instrument : Type}
 [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
 [DecidableEq Technology] [DecidableEq Instrument]
 {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

private theorem suffix_body (before : Cursor code) (stages : List (EventHistory.Stage (code := code)))
 (location : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
 (early : location.round-code.initial.round-1 < before.history.length+1+before.cut) :
 (EventHistory.execute before stages).source.body location=before.source.body location := by
 induction stages generalizing before with
 | nil => rfl
 | cons stage tail ih =>
   have later : location.round-code.initial.round-1 <
    (before.after stage.1 stage.2).history.length+1+(before.after stage.1 stage.2).cut := by
     change location.round-code.initial.round-1 < before.history.length+1+(before.cut+1)
     omega
   exact (ih (before.after stage.1 stage.2) later).trans
    (Future.earlier_body before.source before.entry before.cut (Cursor.controller before stage.1 stage.2)
     (term before.source before.entry before.cut stage.1).val rfl location early)

variable (contract : PaidInvocationSource.Contract (Party := Party) (Good := Good) (Port := Port)
 (Technology := Technology) (Instrument := Instrument))
 (state : RenewableArchiveSource.State (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)) (enabled accept : Bool)

theorem the_paid_window_and_all_later_execution_keep_the_original_financial_prefix
 (original : state.point.side=.original)
 (admitted : PaidInvocationSource.admitted state.model.source.code contract state.point enabled accept=true)
 (stages : List (EventHistory.Stage (code := (renew contract state enabled accept).model.source.code)))
 (ordinal : Nat) (bounded : ordinal≤EventStep.boundary state.point) :
 Native.Coupling.Match state.model.source.code state.point.source.input
  (EventHistory.execute (renew contract state enabled accept).point stages).source.input
  (Financial.accountAt state.point.source.input ordinal)
  (Financial.accountAt (EventHistory.execute (renew contract state enabled accept).point stages).source.input ordinal) := by
 have funded := (admitted_payment_generates_the_exact_next_window contract state enabled accept admitted).2
 have within := (PaidInvocationSource.actual_admission_requires_both_original_valid_occurrences
  state.model.source.code contract state.point enabled accept admitted).2.2.2.2.2.2.2.2.2.2
 have events : ∀ n, n<EventStep.boundary state.point →
  ProgrammeSource.rawEvent (EventHistory.execute (renew contract state enabled accept).point stages).source.input
   (ProgrammeHistory.visitAt state.point.source.input n).current=
  ProgrammeSource.rawEvent state.point.source.input (ProgrammeHistory.visitAt state.point.source.input n).current := by
   intro n small
   cases view : (ProgrammeHistory.visitAt state.point.source.input n).current with
   | bootstrap => rfl
   | running location past =>
     change (EventHistory.execute (renew contract state enabled accept).point stages).source.body location=state.point.source.body location
     have rounds := ProgrammeHistory.visit_round state.point.source.input n
     rw [view] at rounds
     change location.round=state.model.source.code.initial.round+n at rounds
     have early : location.round-state.model.source.code.initial.round-1 < state.point.history.length+1+state.point.cut := by
      change n<state.point.history.length+2+state.point.cut at small
      omega
     have later : location.round-(renew contract state enabled accept).model.source.code.initial.round-1 <
      (renew contract state enabled accept).point.history.length+1+(renew contract state enabled accept).point.cut := by
      rw [funded]
      change location.round-state.model.source.code.initial.round-1 < state.point.history.length+1+(state.point.cut+1+1)
      omega
     refine (suffix_body _ stages location later).trans ?_
     rw [funded]
     refine (PaidInvocationRebase.body_before _ contract.steps within location ?_).trans ?_
     · change location.round-state.model.source.code.initial.round-1 < state.point.history.length+1+(state.point.cut+1+1)
       omega
     · exact (suffix_body (PaidInvocationSource.start state.model.source.code contract state.point)
        (PaidInvocationSource.stages state.model.source.code contract enabled accept) location early).trans
        (CatalogueHandoffSource.body state.model.source.code (PaidInvocationSource.catalogue state.model.source.code contract)
        state.point original location)
 exact Native.Coupling.History.complete_accounts state.model.source.code state.point.source.input
  (EventHistory.execute (renew contract state enabled accept).point stages).source.input rfl rfl
  (EventStep.boundary state.point) events state.point.source.body
  (EventHistory.execute (renew contract state enabled accept).point stages).source.body rfl rfl ordinal bounded

theorem a_refused_window_also_keeps_the_actual_financial_prefix
 (original : state.point.side=.original)
 (unpaid : PaidInvocationSource.admitted state.model.source.code contract state.point enabled accept=false)
 (stages : List (EventHistory.Stage (code := (renew contract state enabled accept).model.source.code)))
 (ordinal : Nat) (bounded : ordinal≤EventStep.boundary state.point) :
 Native.Coupling.Match state.model.source.code state.point.source.input
  (EventHistory.execute (renew contract state enabled accept).point stages).source.input
  (Financial.accountAt state.point.source.input ordinal)
  (Financial.accountAt (EventHistory.execute (renew contract state enabled accept).point stages).source.input ordinal) := by
 change List (EventHistory.Stage (code := PaidInvocationSource.code state.model.source.code contract)) at stages
 rw [(refused_payment_keeps_the_actual_attempt_endpoint_without_credit contract state enabled accept unpaid).2]
 have preserved := CatalogueHandoffSource.completeFinancialPrefix state.model.source.code
  (PaidInvocationSource.catalogue state.model.source.code contract) state.point original
  (PaidInvocationSource.stages state.model.source.code contract enabled accept ++ stages) ordinal bounded
 rw [StageQueue.execute_append] at preserved
 exact preserved

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RenewableArchiveFinance

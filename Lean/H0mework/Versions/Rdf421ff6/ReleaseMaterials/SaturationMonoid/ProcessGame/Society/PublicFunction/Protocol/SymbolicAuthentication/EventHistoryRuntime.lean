import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventHistoryRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Continuation LocalContentRuntime

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)) (budget : Nat)
  (world : Distributed.Recall.Information.World model budget)
  (stages : List (EventHistory.Stage (code := model.source.code)))

theorem the_actual_history_consumes_its_own_payment_root_ledger_and_next
    (site : Fin model.source.code.sites) (scope : Scope)
    (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (known : EventHistory.generate model budget (stages.map Prod.fst) site
      (CursorSettlement.observation (EventHistory.execute (ofWorld model budget world) stages) site) scope = .available body) :
    let actual := EventHistory.execute (ofWorld model budget world) stages
    CursorSettlement.quote actual scope = some body ∧
      (∃ item, item ∈ (Financial.inventoryAt actual.source.input
          (ProgrammeHistory.visitAt actual.source.input (CursorSettlement.depth actual scope + 1))).filterMap
          (Financial.InstructionOrigin.instruction? actual.source.input) ∧
        model.source.code.law.Valid item.before item.request ∧ 0 < body.amount ∧
        flowAt (model.source.code.law.actualDebit item.before item.request) body.debtor body.unit = body.amount ∧
        flowAt (model.source.code.law.actualCredit item.before item.request) body.creditor body.unit = body.amount ∧
        (model.source.code.law.step item.before item.request).claims body.instrument body.debtor body.creditor = body.priorClaim - body.quantity) ∧
      (authority model actual).current = Native.Authority.fullGenerate (native model actual)
        (actual.source.history.length + 1 + actual.cut) ∧
      HEq (runtime model actual).tick.generated.wholeLedgerWriteBack
        ((runtime model actual).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (runtime model actual).current.visit.current) ∧
      (runtime model actual).tick.nextCurrent =
        (Feedback.Authority.Runtime.facade (native model actual) actual.entry rfl rfl).process.stateAt
          ((Feedback.Authority.Runtime.facade (native model actual) actual.entry rfl rfl).process.successor (runtime model actual).state) := by
  have quoted := EventHistory.available_is_correct_after_any_finite_adaptive_installation model budget world stages site scope body known
  have consumed := a_quoted_past_payment_is_consumed_with_the_current_native_root model _ scope body quoted
  exact ⟨quoted, consumed.1, consumed.2.1, consumed.2.2.2.1, consumed.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.EventHistoryRuntime

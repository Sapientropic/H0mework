import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalContent

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalContentRuntime

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol
open Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (currentCursor : Cursor model.source.code)

abbrev native : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) := {model with source := currentCursor.source}
abbrev ordinal := currentCursor.source.history.length + 2 + currentCursor.cut
abbrev runtime := Feedback.Authority.Runtime.activated (native model currentCursor) currentCursor.entry rfl rfl (ordinal model currentCursor)

def authority : Feedback.Authority.Disposition (native model currentCursor) currentCursor.entry currentCursor.cut rfl rfl :=
  match (Feedback.Authority.Runtime.facade (native model currentCursor) currentCursor.entry rfl rfl).readoutAt
      (runtime model currentCursor) .responsibilities with
  | .inl payload => payload.2 currentCursor.cut (by
      change (ProgrammeHistory.visitAt currentCursor.source.input (runtime model currentCursor).state).current = _
      rw [Feedback.Authority.Runtime.activated_state_is_the_generated_ordinal])
  | .inr impossible => nomatch impossible

theorem a_quoted_past_payment_is_consumed_with_the_current_native_root
    (scope : Scope) (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (quoted : CursorSettlement.quote currentCursor scope = some body) :
    (∃ item, item ∈ (Financial.inventoryAt currentCursor.source.input
        (ProgrammeHistory.visitAt currentCursor.source.input (CursorSettlement.depth currentCursor scope + 1))).filterMap
        (Financial.InstructionOrigin.instruction? currentCursor.source.input) ∧
      model.source.code.law.Valid item.before item.request ∧ 0 < body.amount ∧
      flowAt (model.source.code.law.actualDebit item.before item.request) body.debtor body.unit = body.amount ∧
      flowAt (model.source.code.law.actualCredit item.before item.request) body.creditor body.unit = body.amount ∧
      (model.source.code.law.step item.before item.request).claims body.instrument body.debtor body.creditor = body.priorClaim - body.quantity) ∧
      (authority model currentCursor).current = Native.Authority.fullGenerate (native model currentCursor)
        (currentCursor.source.history.length + 1 + currentCursor.cut) ∧
      HEq ((Feedback.Authority.Runtime.facade (native model currentCursor) currentCursor.entry rfl rfl).readoutAt
        (runtime model currentCursor) .responsibilities)
        ((runtime model currentCursor).tick.generated.projectionOutcome (.component ())) ∧
      HEq (runtime model currentCursor).tick.generated.wholeLedgerWriteBack
        ((runtime model currentCursor).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtime model currentCursor).current.visit.current) ∧
      (runtime model currentCursor).tick.nextCurrent =
        (Feedback.Authority.Runtime.facade (native model currentCursor) currentCursor.entry rfl rfl).process.stateAt
          ((Feedback.Authority.Runtime.facade (native model currentCursor) currentCursor.entry rfl rfl).process.successor
            (runtime model currentCursor).state) := by
  obtain ⟨item, inventory, valid, positive, debit, credit, claims, _⟩ :=
    CursorSettlement.quoted_has_original_financial_item_and_effects currentCursor scope body quoted
  have rooted := (Feedback.Authority.Runtime.facade (native model currentCursor) currentCursor.entry rfl rfl).readoutAt_factorizes
    (runtime model currentCursor) .responsibilities
  exact ⟨⟨item, inventory, valid, positive, debit, credit, claims⟩,
    (authority model currentCursor).current_exact, rooted.2.2.2.1, rooted.2.2.1, rooted.2.2.2.2⟩

variable (budget : Nat) (world : Distributed.Recall.Information.World model budget) (protocol : Rule model.source.code)
  (rival : Opponent model.source.code)

theorem actual_local_availability_consumes_its_own_financial_occurrence_and_current_root
    (site : Fin model.source.code.sites) (scope : Scope)
    (body : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (known : LocalContent.generate model budget [protocol] site
      (CursorSettlement.observation ((ofWorld model budget world).after protocol rival) site) scope = .available body) :
    (authority model ((ofWorld model budget world).after protocol rival)).current =
      Native.Authority.fullGenerate (native model ((ofWorld model budget world).after protocol rival))
        (((ofWorld model budget world).after protocol rival).source.history.length + 1 +
          ((ofWorld model budget world).after protocol rival).cut) ∧
      CursorSettlement.quote ((ofWorld model budget world).after protocol rival) scope = some body ∧
      HEq (runtime model ((ofWorld model budget world).after protocol rival)).tick.generated.wholeLedgerWriteBack
        ((runtime model ((ofWorld model budget world).after protocol rival)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtime model ((ofWorld model budget world).after protocol rival)).current.visit.current) ∧
      (runtime model ((ofWorld model budget world).after protocol rival)).tick.nextCurrent =
        (Feedback.Authority.Runtime.facade (native model ((ofWorld model budget world).after protocol rival))
          ((ofWorld model budget world).after protocol rival).entry rfl rfl).process.stateAt
          ((Feedback.Authority.Runtime.facade (native model ((ofWorld model budget world).after protocol rival))
            ((ofWorld model budget world).after protocol rival).entry rfl rfl).process.successor
              (runtime model ((ofWorld model budget world).after protocol rival)).state) := by
  have quoted := LocalContent.the_first_actual_local_query_is_correct_for_any_adaptive_external_input
    model budget world protocol rival site scope body known
  have consumed := a_quoted_past_payment_is_consumed_with_the_current_native_root model
    ((ofWorld model budget world).after protocol rival) scope body quoted
  exact ⟨consumed.2.1, quoted, consumed.2.2.2.1, consumed.2.2.2.2⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.LocalContentRuntime

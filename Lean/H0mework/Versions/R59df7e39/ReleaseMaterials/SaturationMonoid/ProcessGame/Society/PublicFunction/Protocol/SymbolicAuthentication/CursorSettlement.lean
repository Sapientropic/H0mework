import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SubjectQuorum
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Replanning

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CursorSettlement

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol.Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
  (cursor : Cursor code)

abbrev current := (cursor.source.feedbackState cursor.entry cursor.cut).current
abbrev observation (site : Fin code.sites) := (cursor.source.feedbackState cursor.entry cursor.cut).frame.inbox site
def depth (_cursor : Cursor code) (scope : Scope) : Nat := scope.epoch - code.initial.round - 1

/-- Read a completed occurrence of the retained source. In particular, do not
restart a controller at the cursor's new cut or infer it from its active input. -/
def quote (scope : Scope) : Option (Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument)) :=
  if scope.phase ≠ 0 then none
  else if ¬ code.initial.round < scope.epoch then none
  else if ¬ scope.epoch < (current cursor).round then none
  else match Settlement.issuedAt code.law (cursor.source.actualExecution (depth cursor scope)).before
      (cursor.source.actualExecution (depth cursor scope)).submitted scope.instanceId with
    | none => none
    | some payment => if payment.scope = scope then some payment else none

theorem quoted_is_the_original_completed_execution (scope : Scope)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (quoted : quote cursor scope = some payment) :
    Settlement.issuedAt code.law (cursor.source.actualExecution (depth cursor scope)).before
        (cursor.source.actualExecution (depth cursor scope)).submitted scope.instanceId = some payment ∧
      payment.scope = scope ∧ scope.phase = 0 ∧
      (cursor.source.actualExecution (depth cursor scope)).before.round = scope.epoch ∧
      scope.epoch < (current cursor).round := by
  unfold quote at quoted
  split at quoted <;> try contradiction
  rename_i phase
  split at quoted <;> try contradiction
  rename_i origin
  split at quoted <;> try contradiction
  rename_i past
  split at quoted <;> try contradiction
  rename_i statement generated
  split at quoted <;> try contradiction
  rename_i same
  cases Option.some.inj quoted
  refine ⟨generated, same, by omega, ?_, by omega⟩
  change (cursor.source.currentAt (depth cursor scope + 1)).round = _
  rw [Machine.current_round]
  change code.initial.round + (depth cursor scope + 1) = _
  unfold depth
  omega

theorem quoted_has_original_financial_item_and_effects (scope : Scope)
    (payment : Settlement.Statement (Party := Party) (Good := Good) (Instrument := Instrument))
    (quoted : quote cursor scope = some payment) :
    ∃ item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument,
      item ∈ (Financial.inventoryAt cursor.source.input
        (ProgrammeHistory.visitAt cursor.source.input (depth cursor scope + 1))).filterMap
        (Financial.InstructionOrigin.instruction? cursor.source.input) ∧
      code.law.Valid item.before item.request ∧ 0 < payment.amount ∧
      flowAt (code.law.actualDebit item.before item.request) payment.debtor payment.unit = payment.amount ∧
      flowAt (code.law.actualCredit item.before item.request) payment.creditor payment.unit = payment.amount ∧
      (code.law.step item.before item.request).claims payment.instrument payment.debtor payment.creditor =
        payment.priorClaim - payment.quantity ∧
      cursor.source.currentAt (depth cursor scope + 2) = code.law.next
        (cursor.source.currentAt (depth cursor scope + 1)) (cursor.source.actualExecution (depth cursor scope)).submitted := by
  have original := (quoted_is_the_original_completed_execution cursor scope payment quoted).1
  obtain ⟨item, actual, valid, positive, _, debit, credit, claims⟩ := Settlement.issued_payment_has_actual_material_and_claim_effects
    code.law (cursor.source.actualExecution (depth cursor scope)).before
      (cursor.source.actualExecution (depth cursor scope)).submitted scope.instanceId payment original
  refine ⟨item, ?_, valid, positive, debit, credit, claims, cursor.source.next_is_actual _⟩
  rw [Native.both_consumers_use_the_same_actual_word]
  exact List.mem_of_getElem? actual

theorem actual_successor_quote_is_preserved_by_the_generated_external_table
    (protocol : Distributed.Recall.Information.Agency.Protocol.Rule code) (rival : Opponent code) (scope : Scope) :
    quote (cursor.after protocol (finiteRival cursor rival)) scope = quote (cursor.after protocol rival) scope := by
  let original := Cursor.target cursor protocol rival
  let represented := Cursor.target cursor protocol (finiteRival cursor rival)
  let ordinal := depth cursor scope + 1
  have events : ∀ n, n < ordinal + 1 → ProgrammeSource.rawEvent represented.input
      (ProgrammeHistory.visitAt original.input n).current =
        ProgrammeSource.rawEvent original.input (ProgrammeHistory.visitAt original.input n).current := by
    intro n _
    exact one_external_table_preserves_every_raw_occurrence cursor protocol rival n
  have before := Native.Coupling.History.raw_current original.input represented.input rfl rfl (ordinal + 1) events ordinal (by omega)
  have word := (Native.Coupling.History.occurrences original.input represented.input rfl rfl (ordinal + 1) events ordinal (by omega)).2
  change (represented.actualExecution (depth cursor scope)).before = (original.actualExecution (depth cursor scope)).before at before
  change (represented.actualExecution (depth cursor scope)).submitted = (original.actualExecution (depth cursor scope)).submitted at word
  have stateEq := one_original_external_table_preserves_every_actual_ordinal_state cursor protocol rival 1
  have rounds := congrArg (fun state : State code => state.current.round) stateEq
  change (current (cursor.after protocol (finiteRival cursor rival))).round = (current (cursor.after protocol rival)).round at rounds
  unfold quote
  rw [rounds]
  change (if scope.phase ≠ 0 then none else if ¬ code.initial.round < scope.epoch then none else
    if ¬ scope.epoch < (current (cursor.after protocol rival)).round then none else
      match Settlement.issuedAt code.law (represented.actualExecution (depth cursor scope)).before
          (represented.actualExecution (depth cursor scope)).submitted scope.instanceId with
      | none => none
      | some payment => if payment.scope = scope then some payment else none) = _
  rw [before, word]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CursorSettlement

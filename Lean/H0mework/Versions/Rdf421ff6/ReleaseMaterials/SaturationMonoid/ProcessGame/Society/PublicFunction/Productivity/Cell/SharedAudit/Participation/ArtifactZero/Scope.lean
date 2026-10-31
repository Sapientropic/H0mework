import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero.Support

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero

open ResponsibilityLifecycle
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root

/-- The common semantic contract; the two replays supply different inventory
calculations and their own payment/history witnesses. -/
structure Completion (inventory : Party → Good → ℚ) where
  exact_inventory : ∀ actor good, inventory actor good = (productionSource.currentAt 25).stock actor good
  every_cut_floor : ∀ event : Observation, ∀ actor : Party,
    ((actor < 3 ∨ 0 < event.val.item.before.stock actor .seed) →
      1 ≤ event.val.item.before.stock actor .life ∧ 1 ≤ event.val.item.before.stock actor .spare) ∧
    ((actor < 3 ∨ 0 < (law.step event.val.item.before event.val.item.request).stock actor .seed) →
      1 ≤ (law.step event.val.item.before event.val.item.request).stock actor .life ∧
        1 ≤ (law.step event.val.item.before event.val.item.request).stock actor .spare)
  full_cost : ∀ actor good,
    law.totalCredit (Participation.receipts true 25) actor good = law.totalCredit (Participation.receipts false 25) actor good ∧
    law.totalDebit (Participation.receipts true 25) actor good + (if actor = 0 ∧ good = .labor then 1 else 0) =
      law.totalDebit (Participation.receipts false 25) actor good
  exact_origin : ∀ event, (occurrenceOrigin event).instruction? productionSource.input = some event.item
  own_resources : ∀ event : Observation, law.Valid event.val.item.before event.val.item.request →
    ∀ entry ∈ law.debit event.val.item.before event.val.item.request, entry.1.1 = event.val.item.request.signer
  full_claims : ∀ ordinal, Financial.BalanceConservation.ledgerClaims productionSource.input
    (account true ordinal).current = (productionSource.currentAt ordinal).claims
  finance : (Financial.process productionSource.input).Run (account true 0).current (account true 25).current
  no_capital : ∀ later word,
    ¬ Nonempty (Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.CapitalRelationKernel law
      (productionSource.currentAt (3 + later)) word)
  original_rows : ∀ depth, ProgrammeLedger.transferReceiptOf productionSource.input (productionSource.taskWrite depth).2 =
    some (productionSource.writtenReceipt depth)
  own_next : (productionSource.actualExecution 23).after = productionSource.currentAt 25

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Participation.ArtifactZero

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Regression

set_option autoImplicit false

namespace SaturationMonoid.Tracks.LivingLawPublicDividendInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Productivity
open ProcessGame.Society.Institutions.Capitalism.Universal
open Source.Program Instances.OpenReplication Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev publicDividendFacade := Dividend.Runtime.facade 2 true
abbrev exclusiveDividendFacade := Dividend.Runtime.facade 2 false

/-- Both actual occurrences retain their own whole ledger and literal next.
The positive number is the first-window fuel saving; its later use is not
added as a second gain. -/
theorem strict_dividend_and_its_actual_use_are_consumed_by_the_original_root (n : Nat) (shared : Bool) :
    let certificate := (Dividend.Runtime.projectionLaw n shared).project .dividend
      (ProgrammeSource.emitted (Dividend.input n shared)
        (ProgrammeHistory.visitAt (Dividend.input n shared) 2).current) () rfl
    certificate.amount = (n : ℚ) + 1 ∧ 0 < certificate.amount ∧
      Dividend.extraDebit n true false false - Dividend.extraDebit n false false false = certificate.amount ∧
      Dividend.taskDebit n true false false + Dividend.extraDebit n true false false =
        Dividend.taskDebit n false false false + Dividend.extraDebit n false false false ∧
      (Dividend.execution n shared 2).submitted =
        List.replicate (Dividend.maintenanceBudget (Dividend.currentAt n shared 2)) maintain ∧
      (Dividend.writtenReceipt n shared 1).val =
        .original (Dividend.currentAt n shared 2) (Dividend.execution n shared 2).submitted ∧
      ProgrammeLedger.transferReceiptOf (Dividend.input n shared) (Dividend.taskWrite n shared 1).2 =
        some (Dividend.writtenReceipt n shared 1) ∧
      (Dividend.execution n shared 2).after = Dividend.currentAt n shared 3 ∧
      (Dividend.currentAt n shared 3).stock false false = 1 ∧
      HEq ((Dividend.Runtime.facade n shared).readoutAt (Dividend.Runtime.activated n shared 2) .dividend)
        ((Dividend.Runtime.activated n shared 2).tick.generated.projectionOutcome (.component .dividend)) ∧
      HEq (Dividend.Runtime.activated n shared 2).tick.generated.wholeLedgerWriteBack
        ((Dividend.Runtime.activated n shared 2).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (Dividend.Runtime.activated n shared 2).current.visit.current) ∧
      (Dividend.Runtime.activated n shared 2).tick.nextCurrent = (Dividend.Runtime.facade n shared).process.stateAt
        ((Dividend.Runtime.facade n shared).process.successor (Dividend.Runtime.activated n shared 2).state) := by
  dsimp only
  let certificate := Dividend.Runtime.certificate n shared
  have factor := (Dividend.Runtime.facade n shared).readoutAt_factorizes (Dividend.Runtime.activated n shared 2) .dividend
  refine ⟨certificate.generated_amount.trans (Dividend.exact_strict_dividend_and_actual_payment n).1,
    certificate.positive, certificate.payment, certificate.no_double_count, ?_, certificate.written,
    certificate.row, certificate.own_next, ?_, factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩
  · rw [Dividend.reinvestment_word, Dividend.reinvestment_budget]
  · rw [Dividend.reinvested_current]; rfl

theorem every_later_access_response_is_consumed_by_its_own_root (n : Nat) (shared : Bool) (later : Nat) :
    let certificate := (Dividend.Runtime.projectionLaw n shared).project .access
      (ProgrammeSource.emitted (Dividend.input n shared)
        (ProgrammeHistory.visitAt (Dividend.input n shared) (3 + later)).current) () later rfl
    (Dividend.execution n shared (3 + later)).submitted = certificate.response.word ∧
      (law n).totalDebit (Dividend.execution n shared (3 + later)).interpreted.items false false = 0 ∧
      (law n).totalCredit (Dividend.execution n shared (3 + later)).interpreted.items true true =
        (if shared then (n : ℚ) + 1 else 0) ∧
      (law n).totalDebit (Dividend.execution n shared (3 + later)).interpreted.items true true =
        (if shared then (n : ℚ) + 1 else 0) ∧
      ServiceAdequate (law n) (Dividend.currentAt n true (3 + later)) (Dividend.Access.taskAt n later)
        (Dividend.execution n true (3 + later)).submitted ∧
      ¬ Nonempty (Source.ProgrammeControl.Kernel.CapitalRelationKernel (law n)
        (Dividend.currentAt n true (3 + later)) (Dividend.execution n true (3 + later)).submitted) ∧
      (Dividend.writtenReceipt n shared (2 + later)).val =
        .original (Dividend.currentAt n shared (3 + later)) (Dividend.execution n shared (3 + later)).submitted ∧
      ProgrammeLedger.transferReceiptOf (Dividend.input n shared) (Dividend.taskWrite n shared (2 + later)).2 =
        some (Dividend.writtenReceipt n shared (2 + later)) ∧
      (Dividend.execution n shared (3 + later)).after = Dividend.currentAt n shared (3 + (later + 1)) ∧
      (Dividend.currentAt n shared (3 + (later + 1))).stock false false = 1 ∧
      HEq ((Dividend.Runtime.facade n shared).readoutAt (Dividend.Runtime.activated n shared (3 + later)) .access)
        ((Dividend.Runtime.activated n shared (3 + later)).tick.generated.projectionOutcome (.component .access)) ∧
      HEq (Dividend.Runtime.activated n shared (3 + later)).tick.generated.wholeLedgerWriteBack
        ((Dividend.Runtime.activated n shared (3 + later)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (Dividend.Runtime.activated n shared (3 + later)).current.visit.current) ∧
      (Dividend.Runtime.activated n shared (3 + later)).tick.nextCurrent = (Dividend.Runtime.facade n shared).process.stateAt
        ((Dividend.Runtime.facade n shared).process.successor (Dividend.Runtime.activated n shared (3 + later)).state) := by
  dsimp only
  let certificate := Dividend.Runtime.accessCertificate n shared later
  have factor := (Dividend.Runtime.facade n shared).readoutAt_factorizes
    (Dividend.Runtime.activated n shared (3 + later)) .access
  refine ⟨certificate.word, certificate.fuel, certificate.produced, certificate.used, certificate.public_service, certificate.no_capital,
    certificate.written, certificate.row, certificate.own_next, ?_, factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩
  rw [Dividend.Access.every_later_current]; rfl

theorem every_later_window_has_actual_strict_service_gain (n later : Nat) :
    (law n).totalCredit (Dividend.execution n true (3 + later)).interpreted.items true true -
      (law n).totalCredit (Dividend.execution n false (3 + later)).interpreted.items true true = (n : ℚ) + 1 ∧
      (law n).totalDebit (Dividend.execution n true (3 + later)).interpreted.items true true -
        (law n).totalDebit (Dividend.execution n false (3 + later)).interpreted.items true true = (n : ℚ) + 1 ∧
      0 < (law n).totalCredit (Dividend.execution n true (3 + later)).interpreted.items true true -
        (law n).totalCredit (Dividend.execution n false (3 + later)).interpreted.items true true := by
  have opened := Dividend.Access.every_later_service_has_zero_fuel_cost n true later
  have closed :=  Dividend.Access.every_later_service_has_zero_fuel_cost n false later
  rw [opened.2.1, closed.2.1, opened.2.2, closed.2.2]
  norm_num
  positivity

end SaturationMonoid.Tracks.LivingLawPublicDividendInstance

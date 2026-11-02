import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicNativeIdentityInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicNativeMigrationInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicSettlementInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicFeedbackInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicQuotaInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicOpenContinuationInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicReactiveNativeInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicArtifactZeroInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicDistributedInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicReactiveComparisonInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicCellParticipationInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicDividendInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicCellDividendInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawPublicBornCellInstance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.CopyRegression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback.Regression
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Validation
import Lean.LibrarySuggestions.Basic

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.Tracks.LivingLawPublicProductivityInstance

open ProcessGame.Society.PublicFunction
open ProcessGame.Society.PublicFunction.Productivity
open ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority

abbrev productionSource := Cell.source
abbrev publicProductivityFacade := Cell.Runtime.facade
abbrev activated := Cell.Runtime.activated

theorem actual_copy_resources (which : Fin 2) :
    Cell.CopyResources (productionSource.currentAt (Cell.copyVisit which))
      (Cell.child which) (Cell.descendant which) := by
  rcases which with ⟨value, bound⟩
  interval_cases value <;>
    dsimp only [Cell.copyVisit, Cell.child, Cell.descendant] <;>
    constructor <;> try simp only [Cell.raw_current_frame]
  all_goals decide +kernel +revert

theorem actual_copy_next (which : Fin 2) :
    productionSource.currentAt (Cell.copyVisit which + 1) =
      Cell.law.next (productionSource.currentAt (Cell.copyVisit which))
        (Cell.copy (Cell.child which) (Cell.descendant which)) := by
  rcases which with ⟨value, bound⟩
  interval_cases value
  · simpa [Cell.copyVisit, Cell.child, Cell.descendant, Cell.candidate, Cell.source_round]
      using Cell.actual_next ⟨7, by decide⟩
  · simpa [Cell.copyVisit, Cell.child, Cell.descendant, Cell.candidate, Cell.source_round]
      using Cell.actual_next ⟨8, by decide⟩

theorem resource_generated_copy_is_the_actual_request_and_next (which : Fin 2) :
    ∃ admitted,
      Cell.copyFrom (productionSource.currentAt (Cell.copyVisit which))
        (Cell.child which) (Cell.descendant which) = some admitted ∧
      (productionSource.actualExecution (Cell.copyVisit which - 1)).submitted = admitted.word ∧
      productionSource.currentAt (Cell.copyVisit which + 1) =
        Cell.law.next (productionSource.currentAt (Cell.copyVisit which)) admitted.word ∧
      Cell.CopyEffect (productionSource.currentAt (Cell.copyVisit which))
        (Cell.child which) (Cell.descendant which) ∧
      (productionSource.currentAt (Cell.copyVisit which + 1)).claims =
        (productionSource.currentAt (Cell.copyVisit which)).claims ∧
      ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity.AllNeedsPaid Cell.law
        (productionSource.currentAt (Cell.copyVisit which)) [Cell.descendant which] admitted.word ∧
      HEq (publicProductivityFacade.readoutAt (activated (Cell.copyVisit which)) .productivity)
        ((activated (Cell.copyVisit which)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (Cell.copyVisit which)).tick.generated.wholeLedgerWriteBack
        ((activated (Cell.copyVisit which)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (Cell.copyVisit which)).current.visit.current) ∧
      (activated (Cell.copyVisit which)).tick.nextCurrent = publicProductivityFacade.process.stateAt
        (publicProductivityFacade.process.successor (activated (Cell.copyVisit which)).state) := by
  obtain ⟨admitted, generated, word⟩ := Cell.physical_resources_generate_the_copy_request
    _ _ _ (actual_copy_resources which)
  have factor := publicProductivityFacade.readoutAt_factorizes (activated (Cell.copyVisit which)) .productivity
  refine ⟨admitted, generated, (Cell.actual_copy_word which).trans word.symm, ?_,
    Cell.resources_generate_legal_copy _ _ _ (actual_copy_resources which), ?_, ?_,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩
  · rw [word]
    exact actual_copy_next which
  · rw [actual_copy_next]
    exact Cell.copy_preserves_every_financial_position _ _ _ (actual_copy_resources which)
  · rw [word]
    exact Cell.resource_generated_copy_pays_child_services _ _ _ (actual_copy_resources which)

theorem resource_generated_attempt_is_the_actual_word (which : Fin 2) :
    (Cell.attemptCopy (productionSource.currentAt (Cell.copyVisit which))
      (Cell.child which) (Cell.descendant which)).word =
        (productionSource.actualExecution (Cell.copyVisit which - 1)).submitted := by
  have paid := Cell.resources_generate_paid_attempt _ _ _ (actual_copy_resources which)
  cases selected : Cell.attemptCopy (productionSource.currentAt (Cell.copyVisit which))
      (Cell.child which) (Cell.descendant which) with
  | paid accepted => exact (Cell.actual_copy_word which).symm
  | blocked item original refused =>
      rw [selected] at paid
      cases paid

theorem actual_two_generation_production_is_in_original_root (which : Fin 2) :
    ∃ tail : Cell.Runtime.ActualTail (Cell.copyVisit which - 1),
      Cell.Runtime.actualTail (Cell.copyVisit which - 1) = some tail ∧
      (productionSource.actualExecution (Cell.copyVisit which - 1)).submitted =
        Cell.copy (Cell.child which) (Cell.descendant which) ∧
      (productionSource.currentAt (Cell.copyVisit which + 1)).stock (Cell.descendant which) .seed = 3 ∧
      (productionSource.currentAt (Cell.copyVisit which + 1)).stock (Cell.descendant which) .life = 5 ∧
      (productionSource.currentAt (Cell.copyVisit which + 1)).stock (Cell.descendant which) .spare = 1 ∧
      (productionSource.actualExecution (Cell.copyVisit which - 1)).submitted = tail.response.word ∧
      (productionSource.writtenReceipt (Cell.copyVisit which - 1)).val =
        .original (productionSource.currentAt (Cell.copyVisit which - 1 + 1)) tail.response.word ∧
      HEq (publicProductivityFacade.readoutAt (activated (Cell.copyVisit which)) .productivity)
        ((activated (Cell.copyVisit which)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (Cell.copyVisit which)).tick.generated.wholeLedgerWriteBack
        ((activated (Cell.copyVisit which)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (Cell.copyVisit which)).current.visit.current) ∧
      (activated (Cell.copyVisit which)).tick.nextCurrent = publicProductivityFacade.process.stateAt
        (publicProductivityFacade.process.successor (activated (Cell.copyVisit which)).state) := by
  obtain ⟨tail, found⟩ := Cell.Runtime.generated_tail (Cell.copyVisit which - 1)
    (by unfold Cell.copyVisit; split <;> omega)
  have facts := Cell.actual_second_generation which
  have factor := publicProductivityFacade.readoutAt_factorizes (activated (Cell.copyVisit which)) .productivity
  exact ⟨tail, found, Cell.actual_copy_word which, facts.2.1, facts.2.2.1, facts.2.2.2.1,
    tail.submitted, tail.written, factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem public_execution_has_no_complete_capital_relation (later : Nat) :
    ¬ Nonempty (ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.CapitalRelationKernel Cell.law
      (productionSource.currentAt (3 + later))
      (ProgrammeSource.rawEvent productionSource.input
        (ProgrammeHistory.visitAt productionSource.input (3 + later)).current)) ∧
    (∀ item : RootFace.Item productionSource.input
        (ProgrammeHistory.visitAt productionSource.input (3 + later)),
      Structural.familyAtVisit productionSource.input
        (ProgrammeHistory.visitAt productionSource.input (3 + later)) item = []) ∧
    HEq (publicProductivityFacade.readoutAt (activated (3 + later)) .productivity)
      ((activated (3 + later)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (activated (3 + later)).tick.generated.wholeLedgerWriteBack
      ((activated (3 + later)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated (3 + later)).current.visit.current) ∧
    (activated (3 + later)).tick.nextCurrent = publicProductivityFacade.process.stateAt
      (publicProductivityFacade.process.successor (activated (3 + later)).state) := by
  have factor := publicProductivityFacade.readoutAt_factorizes (activated (3 + later)) .productivity
  exact ⟨Cell.no_capital_kernel _ _ (Cell.every_later_actual_current_is_open later),
    Cell.actual_root_capital_family_is_empty later, factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem old_services_remain_paid_in_the_production_runtime (index : productionSource.Slot) (later : Nat) :
    (OutstandingSource.NativeService.historyAt productionSource index (1 + later)).state =
      (OutstandingSource.NativeService.historyAt productionSource index 1).state ∧
    HEq (publicProductivityFacade.readoutAt (activated (1 + later)) (.previous (.service index)))
      ((activated (1 + later)).tick.generated.projectionOutcome (.inherited (.component index))) := by
  have factor := publicProductivityFacade.readoutAt_factorizes (activated (1 + later)) (.previous (.service index))
  exact ⟨Cell.original_service_archives_survive index later, factor.2.2.2.1⟩

theorem actual_feedback_is_consumed_with_the_whole_inventory (depth : Nat) (started : 10 ≤ depth) :
    ∃ tail : Cell.Runtime.ActualTail depth,
      Cell.Runtime.actualTail depth = some tail ∧
      (productionSource.actualExecution depth).submitted = tail.response.word ∧
      (productionSource.writtenReceipt depth).val =
        .original (productionSource.currentAt (depth + 1)) tail.response.word ∧
      tail.remaining = Cell.Feedback.deficits (productionSource.actualExecution depth).after
        (Cell.Feedback.parent (productionSource.currentAt (depth + 1))) ∧
      (productionSource.actualExecution depth).after.claims =
        (productionSource.actualExecution depth).before.claims ∧
      tail.inventoryActors = Cell.Feedback.participants (depth + 2) ∧
      (∀ actor ∉ tail.inventoryActors, ∀ good,
        (productionSource.actualExecution depth).after.stock actor good = 0) ∧
      (∀ actor good, Cell.Feedback.stockFromReceipts (depth + 2) actor good =
        (productionSource.actualExecution depth).after.stock actor good) ∧
      tail.financialAccount = Cell.Finance.account (depth + 2) ∧
      Financial.BalanceConservation.ledgerClaims productionSource.input tail.financialAccount.current =
        (productionSource.actualExecution depth).after.claims ∧
      Nonempty ((Financial.process productionSource.input).Run
        (Cell.Finance.account (depth + 1)).current tail.financialAccount.current) ∧
      (Cell.Finance.account (depth + 1)).current.slots.map (Financial.slotClaim productionSource.input) <+:
        tail.financialAccount.current.slots.map (Financial.slotClaim productionSource.input) ∧
      (Cell.Finance.account (depth + 1)).current.history <+: tail.financialAccount.current.history ∧
      tail.audit = Cell.Audit.generate (depth + 2) ∧
      (productionSource.actualExecution (depth + 1)).submitted =
        (Cell.Feedback.respond (productionSource.actualExecution depth).after).word ∧
      HEq (publicProductivityFacade.readoutAt (activated (depth + 1)) .productivity)
        ((activated (depth + 1)).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated (depth + 1)).tick.generated.wholeLedgerWriteBack
        ((activated (depth + 1)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated (depth + 1)).current.visit.current) ∧
      (activated (depth + 1)).tick.nextCurrent = publicProductivityFacade.process.stateAt
        (publicProductivityFacade.process.successor (activated (depth + 1)).state) := by
  obtain ⟨tail, found⟩ := Cell.Runtime.generated_tail depth (by omega)
  have factor := publicProductivityFacade.readoutAt_factorizes (activated (depth + 1)) .productivity
  exact ⟨tail, found, tail.submitted, tail.written, tail.remaining_generated,
    tail.keeps_claims started, tail.inventory_generated, tail.inventory_complete,
    tail.inventory_accounted, tail.financial_generated, tail.financial_matrix,
    ⟨tail.financial_crossing⟩, tail.financial_origins, tail.financial_history,
    tail.audit_generated,
    Cell.Feedback.next_word_uses_actual_after depth started,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩

theorem feedback_births_pay_their_first_services_in_the_original_root (which : Fin 2) :
    let visit := Cell.Feedback.birthVisit which
    let current := productionSource.currentAt visit
    let parent := Cell.Feedback.parent current
    let newborn := Cell.Feedback.newborn which
    (∀ good, current.stock newborn good = 0) ∧
    (productionSource.actualExecution (visit - 1)).submitted = Cell.copy parent newborn ∧
    Cell.CopyEffect current parent newborn ∧
    ProcessGame.Society.Institutions.Capitalism.Universal.Exit.Necessity.AllNeedsPaid Cell.law
      current [newborn] (productionSource.actualExecution (visit - 1)).submitted ∧
    (productionSource.currentAt (visit + 1)).stock newborn .seed = 3 ∧
    (productionSource.currentAt (visit + 1)).stock newborn .life = 5 ∧
    (productionSource.currentAt (visit + 1)).stock newborn .spare = 1 ∧
    HEq (publicProductivityFacade.readoutAt (activated visit) .productivity)
      ((activated visit).tick.generated.projectionOutcome (.component ())) ∧
    HEq (activated visit).tick.generated.wholeLedgerWriteBack
      ((activated visit).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated visit).current.visit.current) ∧
    (activated visit).tick.nextCurrent = publicProductivityFacade.process.stateAt
      (publicProductivityFacade.process.successor (activated visit).state) := by
  dsimp only
  have facts := Cell.Feedback.births_are_from_actual_shared_resources which
  have started : 10 ≤ Cell.Feedback.birthVisit which - 1 := by
    unfold Cell.Feedback.birthVisit; split <;> omega
  have same : Cell.Feedback.birthVisit which - 1 + 1 = Cell.Feedback.birthVisit which := by omega
  have resources : Cell.CopyResources (productionSource.currentAt (Cell.Feedback.birthVisit which))
      (Cell.Feedback.parent (productionSource.currentAt (Cell.Feedback.birthVisit which)))
      (Cell.Feedback.child (productionSource.currentAt (Cell.Feedback.birthVisit which))) := by
    rw [facts.2.1]
    exact facts.2.2.1
  have emitted : (productionSource.actualExecution (Cell.Feedback.birthVisit which - 1)).submitted =
      Cell.copy (Cell.Feedback.parent (productionSource.currentAt (Cell.Feedback.birthVisit which)))
        (Cell.Feedback.newborn which) := by
    rw [Cell.Feedback.actual_word _ started, same,
      Cell.Feedback.paid_word _ resources (by rw [Cell.source_round]; omega), facts.2.1]
  have factor := publicProductivityFacade.readoutAt_factorizes (activated (Cell.Feedback.birthVisit which)) .productivity
  refine ⟨facts.2.2.2.1, emitted, Cell.resources_generate_legal_copy _ _ _ facts.2.2.1,
    ?_, facts.2.2.2.2.1, facts.2.2.2.2.2.1, facts.2.2.2.2.2.2,
    factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩
  rw [emitted]
  exact Cell.resource_generated_copy_pays_child_services _ _ _ facts.2.2.1

theorem actual_service_cut_inventory_and_finance_audit_is_in_the_original_root :
    ∃ tail : Cell.Runtime.ActualTail 17,
      Cell.Runtime.actualTail 17 = some tail ∧
      tail.audit = .certified Cell.Audit.actualCertificate ∧
      Cell.Audit.traceCheck (Cell.Audit.visits 19) = true ∧ Cell.Audit.nativeCheck 19 = true ∧
      (∀ index : productionSource.Slot,
        (Cell.Audit.actualCertificate.payment index).item ∈ (productionSource.actualExecution 0).interpreted.items ∧
        productionSource.ActualSlotPaid 1 index ∧
        (Cell.Audit.actualCertificate.native index).state.TerminalAt 0) ∧
      (∀ item ∈ Cell.Feedback.receipts 19, ∀ actor,
        Cell.Audit.livingFloor item.before actor ∧
          Cell.Audit.livingFloor (Cell.law.step item.before item.request) actor) ∧
      (∀ item ∈ Cell.Feedback.receipts 19, ∀ actor,
        0 < item.before.stock actor .seed → 0 < (Cell.law.step item.before item.request).stock actor .seed) ∧
      (∀ start later, start + later ≤ 19 → ∀ actor,
        0 < (productionSource.currentAt start).stock actor .seed →
          0 < (productionSource.currentAt (start + later)).stock actor .seed) ∧
      (∀ actor good, Cell.Feedback.stockFromReceipts 19 actor good = (productionSource.currentAt 19).stock actor good) ∧
      Financial.BalanceConservation.ledgerClaims productionSource.input (Cell.Finance.account 19).current =
        (productionSource.currentAt 19).claims ∧
      Nonempty ((Financial.process productionSource.input).Run
        (Cell.Finance.account 0).current (Cell.Finance.account 19).current) ∧
      ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeLedger.transferReceiptOf
        productionSource.input (productionSource.taskWrite 17).2 = some (productionSource.writtenReceipt 17) ∧
      (productionSource.actualExecution 18).submitted =
        (Cell.Feedback.respond (productionSource.actualExecution 17).after).word ∧
      HEq (publicProductivityFacade.readoutAt (activated 18) .productivity)
        ((activated 18).tick.generated.projectionOutcome (.component ())) ∧
      HEq (activated 18).tick.generated.wholeLedgerWriteBack
        ((activated 18).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (activated 18).current.visit.current) ∧
      (activated 18).tick.nextCurrent = publicProductivityFacade.process.stateAt
        (publicProductivityFacade.process.successor (activated 18).state) := by
  obtain ⟨tail, found⟩ := Cell.Runtime.generated_tail 17 (by decide)
  have selected : tail.audit = .certified Cell.Audit.actualCertificate :=
    tail.audit_generated.trans Cell.Audit.actual_full_prefix_is_certified
  have factor := publicProductivityFacade.readoutAt_factorizes (activated 18) .productivity
  refine ⟨tail, found, selected, Cell.Audit.actualCertificate.trace_replay,
    Cell.Audit.actualCertificate.native_replay, ?_, Cell.Audit.actualCertificate.every_cut_floor,
    Cell.Audit.actualCertificate.seeded_addresses_survive (by decide),
    Cell.Audit.actualCertificate.seeded_bearers_survive_frames (by decide),
    Cell.Audit.actualCertificate.inventory, Cell.Audit.actualCertificate.finance,
    ⟨Cell.Audit.actualCertificate.financial_run⟩, Cell.Audit.actualCertificate.original_task_rows 17 (by decide),
    Cell.Feedback.next_word_uses_actual_after 17 (by decide), factor.2.2.2.1, factor.2.2.1, factor.2.2.2.2⟩
  intro index
  have paid := Cell.Audit.actual_payment_is_the_original_occurrence 19 (by decide) index
  exact ⟨paid.2.1, paid.2.2, Cell.Audit.actualCertificate.native_terminal index⟩

end SaturationMonoid.Tracks.LivingLawPublicProductivityInstance

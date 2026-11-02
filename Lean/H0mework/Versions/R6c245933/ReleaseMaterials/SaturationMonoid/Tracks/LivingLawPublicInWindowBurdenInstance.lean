import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Registered.Loss.Appraisal.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.Tracks.LivingLawPublicInWindowBurdenInstance
open ProcessGame.Society.PublicFunction Mandate Mandate.Financed Mandate.Financed.Continuing
open Mandate.Financed.Continuing.Closure Objection Objection.Followup Objection.Opening ScopeRevision.Pending.Joint.Handoff
open ScopeRevision ScopeRevision.Pending.Joint
open ProcessGame.Society.Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
noncomputable section
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
  (count : Nat) {unit : Good} (price : Registered.Loss.Appraisal.Original.Prices unit) (actor : Bool) (word : List Action)

abbrev publicInWindowBurdenFacade := Registered.Loss.Appraisal.Runtime.facade authority inventory fresh count price actor word

theorem the_original_root_consumes_its_six_native_families_actual_opportunities_decision_and_next :
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).baseline =
      Registered.Loss.Runtime.fromRoot authority inventory fresh word count ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).responsibilities =
      (fun row => row.state) ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).positions =
      List.finRange (Registered.Loss.Responsibility.census authority inventory fresh word (Registered.Loss.cursorAt authority inventory fresh word count).state).length ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).nativeHistories =
      (fun row => row.complete) ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).opportunities =
      Registered.Loss.Appraisal.agency authority inventory fresh count word ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).decision =
      Registered.Loss.Appraisal.classify authority inventory fresh count price actor word ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).response =
      Registered.Loss.Appraisal.response authority inventory fresh count price actor word ∧
    (Registered.Loss.Appraisal.Runtime.root authority inventory fresh count price actor word).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (Registered.Loss.I authority inventory fresh word count)).toAuthoritativeRoot.toRoot ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).baseline.cursor.before =
      ProgrammeSource.rawCurrent (Registered.Loss.I authority inventory fresh word count)
        (ProgrammeSource.next (Registered.Loss.I authority inventory fresh word count)
          (ProgrammeHistory.visitAt (Registered.Loss.I authority inventory fresh word count)
            (Registered.Loss.ordinal authority inventory fresh word count)).current) ∧
    HEq (publicInWindowBurdenFacade authority inventory fresh count price actor word |>.readoutAt
      (Registered.Loss.Appraisal.Runtime.activated authority inventory fresh count price actor word (Registered.Loss.ordinal authority inventory fresh word count)) .fullAccount)
      ((Registered.Loss.Appraisal.Runtime.activated authority inventory fresh count price actor word (Registered.Loss.ordinal authority inventory fresh word count)).tick.generated.projectionOutcome (.component ())) ∧
    HEq (Registered.Loss.Appraisal.Runtime.activated authority inventory fresh count price actor word (Registered.Loss.ordinal authority inventory fresh word count)).tick.generated.wholeLedgerWriteBack
      ((Registered.Loss.Appraisal.Runtime.activated authority inventory fresh count price actor word (Registered.Loss.ordinal authority inventory fresh word count)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Registered.Loss.Appraisal.Runtime.activated authority inventory fresh count price actor word (Registered.Loss.ordinal authority inventory fresh word count)).current.visit.current) ∧
    (Registered.Loss.Appraisal.Runtime.activated authority inventory fresh count price actor word (Registered.Loss.ordinal authority inventory fresh word count)).tick.nextCurrent =
      (Registered.Loss.Appraisal.Runtime.process authority inventory fresh count price actor word).stateAt
        ((Registered.Loss.Appraisal.Runtime.process authority inventory fresh count price actor word).successor
          (Registered.Loss.Appraisal.Runtime.activated authority inventory fresh count price actor word (Registered.Loss.ordinal authority inventory fresh word count)).state) := by
  have factor := (Registered.Loss.Appraisal.Runtime.facade authority inventory fresh count price actor word).readoutAt_factorizes
    (Registered.Loss.Appraisal.Runtime.activated authority inventory fresh count price actor word (Registered.Loss.ordinal authority inventory fresh word count)) .fullAccount
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    Registered.Loss.Appraisal.Runtime.the_full_account_is_this_original_sources_generated_raw_next _ _ _ _ _ _ _,
    factor.2.2.2.1,factor.2.2.1,factor.2.2.2.2⟩

theorem each_original_native_slot_and_history_enters_the_priced_account
    (row : Registered.Loss.Responsibility.Row authority inventory fresh word (Registered.Loss.cursorAt authority inventory fresh word count).state)
    (slot : Fin row.state.slots.length) (event : Fin row.state.history.length) :
    (⟨row,slot⟩ : Registered.Loss.Responsibility.Slot authority inventory fresh word (Registered.Loss.cursorAt authority inventory fresh word count).state) ∈
      Registered.Loss.Responsibility.slots authority inventory fresh word (Registered.Loss.cursorAt authority inventory fresh word count).state ∧
    (⟨row,event⟩ : Registered.Loss.Responsibility.Event authority inventory fresh word (Registered.Loss.cursorAt authority inventory fresh word count).state) ∈
      Registered.Loss.Responsibility.events authority inventory fresh word (Registered.Loss.cursorAt authority inventory fresh word count).state ∧
    Nonempty (row.native.Run row.origin.initial row.state) :=
  ⟨Registered.Loss.Responsibility.every_current_slot_is_generated _ _ _ _ _ row slot,
    Registered.Loss.Responsibility.every_actual_history_item_is_generated _ _ _ _ _ row event,
    Registered.Loss.Responsibility.all_current_native_states_have_their_original_run _ _ _ _ _ row⟩

theorem the_root_selected_response_keeps_the_original_financial_occurrence (candidate : List Action)
    (selected : (Registered.Loss.Appraisal.classify authority inventory fresh count price actor word).selected = some candidate) :
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).response =
      some ⟨candidate,(Registered.Loss.Runtime.fromRoot authority inventory fresh candidate count,Registered.Loss.Finance.produce authority inventory fresh candidate count)⟩ := by
  change Registered.Loss.Appraisal.response authority inventory fresh count price actor word = _
  simp only [Registered.Loss.Appraisal.response,selected,Option.map_some]

theorem the_selected_actual_alternative_has_its_own_whole_ledger_and_next (candidate : List Action)
    (selected : (Registered.Loss.Appraisal.classify authority inventory fresh count price actor word).selected = some candidate) :
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).response =
      some ⟨candidate,(Registered.Loss.Runtime.fromRoot authority inventory fresh candidate count,
        Registered.Loss.Finance.produce authority inventory fresh candidate count)⟩ ∧
    HEq (Registered.Loss.Runtime.activated authority inventory fresh candidate count
      (Registered.Loss.ordinal authority inventory fresh candidate count)).tick.generated.wholeLedgerWriteBack
      ((Registered.Loss.Runtime.activated authority inventory fresh candidate count
        (Registered.Loss.ordinal authority inventory fresh candidate count)).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (Registered.Loss.Runtime.activated authority inventory fresh candidate count
          (Registered.Loss.ordinal authority inventory fresh candidate count)).current.visit.current) ∧
    (Registered.Loss.Runtime.activated authority inventory fresh candidate count
      (Registered.Loss.ordinal authority inventory fresh candidate count)).tick.nextCurrent =
      (Registered.Loss.Runtime.process authority inventory fresh candidate count).stateAt
        ((Registered.Loss.Runtime.process authority inventory fresh candidate count).successor
          (Registered.Loss.Runtime.activated authority inventory fresh candidate count
            (Registered.Loss.ordinal authority inventory fresh candidate count)).state) := by
  have factor := (Registered.Loss.Runtime.facade authority inventory fresh candidate count).readoutAt_factorizes
    (Registered.Loss.Runtime.activated authority inventory fresh candidate count
      (Registered.Loss.ordinal authority inventory fresh candidate count)) .lossAccount
  exact ⟨the_root_selected_response_keeps_the_original_financial_occurrence _ _ _ _ _ _ _ _ selected,
    factor.2.2.1,factor.2.2.2.2⟩

theorem the_same_root_consumes_the_full_financial_run_and_its_exact_net (party : Bool) (good : Good) :
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).financing =
      Registered.Loss.Finance.produce authority inventory fresh word count ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).actualVisits =
      Registered.Loss.Finance.entries authority inventory fresh word count ∧
    (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).amounts true party good +
      (Registered.Loss.Appraisal.Runtime.fromRoot authority inventory fresh count price actor word).amounts false party good =
        Registered.Loss.Finance.quotedBefore authority inventory fresh word party good -
          Registered.Loss.Finance.quotedAfter authority inventory fresh word count party good := by
  refine ⟨rfl,rfl,?_⟩
  exact Registered.Loss.Finance.the_complete_continuation_net_has_one_original_start_and_actual_end _ _ _ _ _ _ _

theorem the_dynamic_original_loss_and_each_actual_compensation_are_never_a_second_cash_credit :
    Registered.Loss.Appraisal.rawValue price (Registered.Loss.cursorAt authority inventory fresh word count).book actor =
      (Registered.Loss.Appraisal.rawQuantityValues price (Registered.Loss.cursorAt authority inventory fresh word count).book actor).sum :=
  Registered.Loss.Appraisal.all_dynamic_original_cells_keep_their_own_priced_quantity _ _ _

theorem publicSourceDecision :
    (Registered.Loss.Appraisal.paidWindow authority inventory fresh word = false ∧
      (Registered.Loss.Appraisal.classify authority inventory fresh count price actor word).selected = none) ∨
    (∃ candidate, (Registered.Loss.Appraisal.classify authority inventory fresh count price actor word).selected = some candidate ∧
      candidate ∈ Registered.Loss.Appraisal.menu authority inventory fresh ∧ Registered.Loss.Appraisal.sameWindow authority inventory fresh count actor word candidate = true ∧
      Registered.Loss.Appraisal.payoff authority inventory fresh count price word actor < Registered.Loss.Appraisal.payoff authority inventory fresh count price candidate actor) ∨
    ((Registered.Loss.Appraisal.classify authority inventory fresh count price actor word).selected = none ∧
      Registered.Loss.Appraisal.paidWindow authority inventory fresh word = true ∧
      ∀ candidate ∈ Registered.Loss.Appraisal.menu authority inventory fresh, Registered.Loss.Appraisal.sameWindow authority inventory fresh count actor word candidate = true →
        Registered.Loss.Appraisal.financial authority inventory fresh count price word actor true - Registered.Loss.Appraisal.financial authority inventory fresh count price candidate actor true ≤
          Registered.Loss.Appraisal.budget authority inventory fresh count price word actor candidate - Registered.Loss.Appraisal.gains authority inventory fresh count price word actor candidate) :=
  Registered.Loss.Appraisal.the_source_produces_an_unpaid_baseline_or_actual_improvement_or_paid_cost_bound
    authority inventory fresh count price actor word

end
end SaturationMonoid.Tracks.LivingLawPublicInWindowBurdenInstance

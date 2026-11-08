import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Run
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation.Native

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

open Source.Program Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro
open Quantities Actual Handoff.Continuation
open Exchange (nativeAccount nativeAccount_heq_of_eq)

noncomputable section

private theorem the_original_period_items_are_material (raw : RawCurrent Bool Bool Unit Unit)
    (item : ExecutionItem Bool Bool Bool Unit Unit) (actual : item ∈ publicLaw.rawItems raw period) :
    Responsibility.NonFinancialOperation item.request.operation := by
  have request : item.request ∈ (publicLaw.rawItems raw period).map ExecutionItem.request :=
    List.mem_map.mpr ⟨item, actual, rfl⟩
  change item.request ∈ (publicLaw.execute raw 0 period).items.map ExecutionItem.request at request
  rw [publicLaw.inventory_requests_exact] at request
  simp only [period, List.mem_cons, List.not_mem_nil, or_false] at request
  rcases request with selected | selected | selected | selected | selected <;> rw [selected] <;> trivial

theorem the_paid_handoff_keeps_the_original_financial_slots :
    HEq (nativeAccount start) (nativeAccount source) := by
  have begins : HEq (nativeAccount migration) (nativeAccount source) := by
    change HEq (nativeAccount (migrationQuery source proposal)) (nativeAccount source)
    unfold migrationQuery
    rw [no_preparation_is_needed proposal rfl]
    exact heq_of_eq (source.requery_keeps_control_and_complete_account (fun _ _ => .migrate proposal.pair)).2
  have first : HEq (nativeAccount (renewalStart source proposal)) (nativeAccount migration) :=
    a_material_body_and_its_native_drain_keep_the_original_account migration
      (preparation_is_ready source proposal) (fun item listed => the_original_period_items_are_material opening item
        (the_front_physically_pays_the_original_word.2.2 ▸ listed))
  have reuses : HEq (nativeAccount renewal) (nativeAccount (renewalStart source proposal)) :=
    heq_of_eq ((renewalStart source proposal).requery_keeps_control_and_complete_account (fun _ _ => .advance)).2
  have finish : HEq (nativeAccount start) (nativeAccount renewal) := by
    have exactEnd : start = Execution.endAt renewal.advance (Execution.drain renewal.advance) :=
      end_is_the_original_renewal_and_its_accounting source proposal
    exact (nativeAccount_heq_of_eq exactEnd).trans
      (a_material_body_and_its_native_drain_keep_the_original_account renewal (renewal_is_ready source proposal)
        (fun item listed => the_original_period_items_are_material firstRaw item
          (the_renewal_physically_pays_the_same_word.2.2 ▸ listed)))
  exact finish.trans (reuses.trans (first.trans begins))

theorem every_original_renewal_retains_all_financial_slots (n : Nat) :
    HEq (nativeAccount (run n)) (nativeAccount source) := by
  induction n with
  | zero => exact the_paid_handoff_keeps_the_original_financial_slots
  | succ n retained =>
    let cut := run n
    let query := installedQuery cut
    have installed := run_is_installed n
    have body := (installed_query_is_paid cut n installed).2
    have ready : ¬ Public.Inquiry.HasWork query.native.frame query.native.actual.actual := installed.ready
    have consumed := a_material_body_and_its_native_drain_keep_the_original_account query ready
      (fun item listed => the_original_period_items_are_material (materialAt n) item (body.inventory ▸ listed))
    have same := nativeAccount_heq_of_eq (renewalSuffix_ends_at_the_original_native_drain cut)
    have querySame := heq_of_eq (cut.requery_keeps_control_and_complete_account (fun _ _ => .advance)).2
    exact same.trans (consumed.trans (querySame.trans retained))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Continuation

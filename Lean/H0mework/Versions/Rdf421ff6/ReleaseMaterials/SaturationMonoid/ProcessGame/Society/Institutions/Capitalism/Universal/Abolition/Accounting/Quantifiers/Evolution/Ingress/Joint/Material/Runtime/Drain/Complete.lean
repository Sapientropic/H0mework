import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Loop
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

private theorem after_first_is_the_original_body_target :
    Runtime.next seed claim (Runtime.initial seed) =
      Public.Accounting.bodyTarget seed.input seed.depth seed.count (Background.nativeAccount seed) := rfl

theorem the_source_budget_starts_with_one_body_and_then_its_own_inventory :
    completed seed claim = (Runtime.next seed claim)^[(Execution.Selected.items seed claim).length]
      (Public.Accounting.bodyTarget seed.input seed.depth seed.count (Background.nativeAccount seed)) := by
  unfold completed stateAt budget
  rw [Nat.add_comm 1 _,Function.iterate_succ_apply,after_first_is_the_original_body_target]

private theorem the_paid_source_inventory_is_consumed_in_its_original_order :
    let result := (Runtime.next seed claim)^[(Execution.Selected.items seed claim).length]
      (Public.Accounting.bodyTarget seed.input seed.depth seed.count (Background.nativeAccount seed))
    result.account = (Execution.Selected.items seed claim).foldl
      (fun state item => (Epoch.Finance.consume seed.input seed.depth seed.count item state).next seed.input seed.depth seed.count)
        (Background.nativeAccount seed) ∧
      result.position = (Execution.Selected.items seed claim).length ∧ result.bodyPaid = true := by
  have result := Loop.suffix_is_consumed_in_its_original_order seed.input seed.depth seed.count 0 0 []
    (Runtime.cursor seed claim) (anchor := Background.nativeAccount seed)
    (no_original_position_requests_another_loan seed claim)
    (Public.Accounting.items seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim))
    (Public.Accounting.bodyTarget seed.input seed.depth seed.count (Background.nativeAccount seed)) rfl (by
      change (Public.Accounting.items seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim)).drop 0 = _
      exact List.drop_zero)
  rw [the_source_inventory_is_the_same_selected_occurrence] at result
  exact ⟨result.1,result.2.1.trans (Nat.zero_add _),result.2.2⟩

theorem the_finite_source_loop_finishes_at_the_original_native_consumption :
    (completed seed claim).account = Execution.Selected.after seed claim ∧
      (completed seed claim).position = (Execution.Selected.items seed claim).length ∧
      (completed seed claim).bodyPaid = true := by
  rw [the_source_budget_starts_with_one_body_and_then_its_own_inventory]
  have result := the_paid_source_inventory_is_consumed_in_its_original_order seed claim
  refine ⟨result.1.trans ?_,result.2⟩
  exact (the_original_financial_consumption_is_its_same_ordered_fold seed.input seed.depth seed.count
    (Execution.Selected.tag seed claim) (Execution.Selected.visit seed claim) (Background.nativeAccount seed)).symm

theorem the_finite_source_budget_leaves_no_original_head :
    Public.Accounting.item? seed.input seed.depth seed.count 0 0 [] (Runtime.cursor seed claim) (completed seed claim) = none := by
  have result := the_finite_source_loop_finishes_at_the_original_native_consumption seed claim
  simp only [Public.Accounting.item?,result.2.2,if_true,result.2.1,
    the_source_inventory_is_the_same_selected_occurrence,List.getElem?_length]

theorem the_consumed_word_does_not_restart_its_body_or_financial_prefix :
    Runtime.next seed claim (completed seed claim) = completed seed claim := by
  have result := the_finite_source_loop_finishes_at_the_original_native_consumption seed claim
  unfold Runtime.next Public.Accounting.next
  rw [dif_pos result.2.2,the_finite_source_budget_leaves_no_original_head]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Drain

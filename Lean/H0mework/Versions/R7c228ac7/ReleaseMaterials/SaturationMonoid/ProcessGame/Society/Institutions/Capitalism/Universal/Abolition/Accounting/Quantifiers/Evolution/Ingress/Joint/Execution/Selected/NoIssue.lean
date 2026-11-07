import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.Actual
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Menu.Integrity

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

def NotIssue (request : Request Party Good Port Technology Instrument) : Prop :=
  match request.operation with | .issue .. => False | _ => True

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology] in
private theorem material_not_issue (request : Request Party Good Port Technology Instrument)
    (material : Responsibility.NonFinancialOperation request.operation) : NotIssue request := by
  cases operation : request.operation <;> simp_all [NotIssue,Responsibility.NonFinancialOperation]

private theorem material_plan_is_nonfinancial (current : Current seed claim) (operator : Party) (technology : Technology) :
    ∀ request ∈ Planning.Menu.materialPlan seed claim current operator technology,
      Responsibility.NonFinancialOperation request.operation := by
  unfold Planning.Menu.materialPlan
  split
  · exact Planning.Menu.current_need_bills_are_nonfinancial seed claim current
  · apply Planning.Menu.productive_repairs_preserve_the_original_nonfinancial_prefix
    apply Planning.Menu.gross_refunds_preserve_the_original_nonfinancial_prefix
    intro request member
    rcases List.mem_append.mp member with funded | needed
    · exact Planning.Menu.funding_preserves_the_original_nonfinancial_prefix seed claim current operator _ _
        (Planning.Menu.current_production_is_nonfinancial seed claim current operator technology) request funded
    · exact Planning.Menu.current_need_bills_are_nonfinancial seed claim current request needed

omit [DecidableEq Technology] in
private theorem settlements_never_issue : ∀ request ∈ Planning.Menu.settlements seed, NotIssue request := by
  intro request member
  obtain ⟨slot,_,inside⟩ := List.mem_flatMap.mp member
  obtain ⟨holder,_,generated⟩ := List.mem_filterMap.mp inside
  split at generated
  · cases Option.some.inj generated
    trivial
  · cases generated

private theorem source_plan_never_issues (current : Current seed claim)
    (programme : RawEvent Party Good Port Technology Instrument)
    (original : programme ∈ Planning.Menu.plans seed claim current) :
    ∀ request ∈ programme, NotIssue request := by
  rcases Planning.Menu.every_plan_keeps_the_original_actor_technology_and_financial_tail
    seed claim current programme original with ⟨_,_,same⟩ | ⟨operator,_,technology,_,same⟩
  · rw [same]
    intro request member
    rcases List.mem_append.mp member with needed | financial
    · exact material_not_issue request (Planning.Menu.current_need_bills_are_nonfinancial seed claim current request needed)
    · exact settlements_never_issue seed request financial
  · rw [same]
    intro request member
    rcases List.mem_append.mp member with material | financial
    · exact material_not_issue request (material_plan_is_nonfinancial seed claim current operator technology request material)
    · exact settlements_never_issue seed request financial

private theorem chosen_never_issues (current : Current seed claim) :
    ∀ request ∈ Planning.chosen seed claim current, NotIssue request := by
  unfold Planning.chosen
  cases Planning.selection seed claim current with
  | ready programme original _ => exact source_plan_never_issues seed claim current programme original
  | blocked issues =>
      change ∀ request ∈ (Planning.Menu.plans seed claim current).headD
        (Planning.Menu.needsWord seed claim current ++ Planning.Menu.settlements seed), NotIssue request
      cases available : Planning.Menu.plans seed claim current with
      | nil =>
          intro request member
          rcases List.mem_append.mp member with needed | financial
          · exact material_not_issue request (Planning.Menu.current_need_bills_are_nonfinancial seed claim current request needed)
          · exact settlements_never_issue seed request financial
      | cons programme rest =>
          apply source_plan_never_issues seed claim current programme
          rw [available]
          exact List.mem_cons_self

theorem the_selected_repair_never_borrows_again : ∀ request ∈ word seed claim, NotIssue request := by
  intro request member
  exact chosen_never_issues seed claim (Material.shared seed claim) request
    ((Entitlement.Execution.the_source_prefix_is_an_original_prefix _ _ _).subset member)

theorem no_actual_financial_item_can_mint_a_new_loan
    (item : Epoch.Finance.ActualItem seed.input seed.depth seed.count)
    (original : item ∈ items seed claim) : NotIssue (item.instruction seed.input seed.depth seed.count).request := by
  have member : item.instruction seed.input seed.depth seed.count ∈
      (actualLaw seed).rawItems (Material.shared seed claim).raw (word seed claim) := by
    rw [← the_native_items_are_the_literal_original_source_inventory seed claim]
    exact List.mem_map.mpr ⟨item,original,rfl⟩
  apply the_selected_repair_never_borrows_again seed claim
  have requests := (actualLaw seed).inventory_requests_exact (Material.shared seed claim).raw 0 (word seed claim)
  rw [← requests]
  exact List.mem_map.mpr ⟨item.instruction seed.input seed.depth seed.count,member,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected

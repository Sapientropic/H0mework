import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.Account
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected.NoIssue

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

private theorem no_new_claim
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (origin : Epoch.Finance.ActualItem input depth count)
    (notIssue : NotIssue (origin.instruction input depth count).request) :
    Epoch.Finance.readNewClaim input depth count origin = none := by
  cases operation : (origin.instruction input depth count).request.operation <;>
    simp_all [NotIssue,Epoch.Finance.readNewClaim]

private theorem one_item_keeps_all_original_claims
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (origin : Epoch.Finance.ActualItem input depth count)
    (notIssue : NotIssue (origin.instruction input depth count).request)
    (state : (Epoch.Finance.process input depth count).GeneratedState) :
    ((Epoch.Finance.consume input depth count origin state).next input depth count).current.slots.map
      (Epoch.Finance.slotClaim input depth count) = state.current.slots.map (Epoch.Finance.slotClaim input depth count) := by
  unfold Epoch.Finance.consume
  split
  · rfl
  · split
    · rename_i fresh returned
      cases (no_new_claim input depth count origin notIssue).symm.trans returned
    · split
      · exact (Epoch.Finance.allocate input depth count origin _ state).original_claims
      · rfl

private theorem the_complete_inventory_keeps_all_original_claims
    (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)
    (tag : Epoch.Interface.Tag input depth count) (visit : Epoch.Interface.Visit input depth count tag)
    (state : (Epoch.Finance.process input depth count).GeneratedState)
    (noIssue : ∀ item ∈ Epoch.Finance.inventory input depth count tag visit,
      NotIssue (item.instruction input depth count).request) :
    (Epoch.Finance.consumeVisit input depth count tag visit state).current.slots.map (Epoch.Finance.slotClaim input depth count) =
      state.current.slots.map (Epoch.Finance.slotClaim input depth count) := by
  unfold Epoch.Finance.consumeVisit
  generalize Epoch.Finance.inventory input depth count tag visit = origins at noIssue ⊢
  induction origins generalizing state with
  | nil => rfl
  | cons item rest later =>
      exact (later ((Epoch.Finance.consume input depth count item state).next input depth count)
        (fun next member => noIssue next (List.mem_cons_of_mem item member))).trans
          (one_item_keeps_all_original_claims input depth count item (noIssue item List.mem_cons_self) state)

variable [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

theorem the_same_repair_neither_reissues_nor_deletes_any_original_claim :
    (after seed claim).current.slots.map (Epoch.Finance.slotClaim seed.input seed.depth seed.count) =
      (before seed).current.slots.map (Epoch.Finance.slotClaim seed.input seed.depth seed.count) := by
  unfold after
  exact the_complete_inventory_keeps_all_original_claims seed.input seed.depth seed.count
    (tag seed claim) (visit seed claim) (before seed) (no_actual_financial_item_can_mint_a_new_loan seed claim)

theorem all_original_origins_and_generated_actors_are_literal :
    (after seed claim).current.slots.map (fun slot =>
      let original := Epoch.Finance.slotClaim seed.input seed.depth seed.count slot
      (original.origin seed.input seed.depth seed.count,
        original.debtorActor seed.input seed.depth seed.count,original.holderActor seed.input seed.depth seed.count)) =
    (before seed).current.slots.map (fun slot =>
      let original := Epoch.Finance.slotClaim seed.input seed.depth seed.count slot
      (original.origin seed.input seed.depth seed.count,
        original.debtorActor seed.input seed.depth seed.count,original.holderActor seed.input seed.depth seed.count)) := by
  simpa only [List.map_map,Function.comp_def] using congrArg
    (List.map (fun original : Epoch.Finance.Claim seed.input seed.depth seed.count =>
      (original.origin seed.input seed.depth seed.count,
        original.debtorActor seed.input seed.depth seed.count,original.holderActor seed.input seed.depth seed.count)))
    (the_same_repair_neither_reissues_nor_deletes_any_original_claim seed claim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected

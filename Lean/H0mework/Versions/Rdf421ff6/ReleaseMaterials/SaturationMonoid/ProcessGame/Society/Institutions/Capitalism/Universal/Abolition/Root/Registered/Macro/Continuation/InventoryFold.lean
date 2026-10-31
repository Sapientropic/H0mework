import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation.AccountFold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound.Rank

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

private theorem visit_is_the_same_inventory_fold
    (tag : Epoch.Interface.Tag input depth count) (visit : Epoch.Interface.Visit input depth count tag)
    (initial : (Epoch.Finance.process input depth count).GeneratedState) :
    Epoch.Finance.consumeVisit input depth count tag visit initial =
      (Epoch.Finance.inventory input depth count tag visit).foldl
        (fun account item => (Epoch.Finance.consume input depth count item account).next input depth count) initial := by
  unfold Epoch.Finance.consumeVisit
  generalize Epoch.Finance.inventory input depth count tag visit = items
  induction items generalizing initial with
  | nil => rfl
  | cons item rest inherited =>
      exact inherited ((Epoch.Finance.consume input depth count item initial).next input depth count)

variable (prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument)
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "items" => Inventory.items (review := review) input depth count prefixLimit renewalLimit start proposal
local notation "before" => Inventory.before input depth count prefixLimit renewalLimit sourceDepth sourceCount start
local notation "accountAt" => Inventory.accountAt (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal

theorem inventory_position_is_the_same_original_fold (position : Nat) :
    accountAt position = ((items).take position).foldl
      (fun account item => (Epoch.Finance.consume input depth count item account).next input depth count) before := by
  induction position with
  | zero => rfl
  | succ position inherited =>
      rw [List.take_add_one, List.foldl_append, ← inherited]
      cases selected : (items)[position]? <;> simp only [Inventory.accountAt, selected] <;> rfl

theorem complete_inventory_is_the_original_event :
    accountAt (items).length =
      Epoch.Finance.consumeVisit input depth count
        (Inventory.tag (review := review) input depth count prefixLimit renewalLimit start proposal)
        (Inventory.visit (review := review) input depth count prefixLimit renewalLimit start proposal) before := by
  rw [inventory_position_is_the_same_original_fold (review := review), List.take_length]
  exact (visit_is_the_same_inventory_fold input depth count _ _ before).symm

theorem completed_event_is_the_literal_next_input_seed :
    Inventory.before input depth count prefixLimit renewalLimit sourceDepth sourceCount
      (Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal) =
        accountAt (items).length := by
  unfold Inventory.before Inventory.physicalAfter
  rw [Epoch.Finance.ActualPast.cursor_append_is_one_original_update]
  exact (complete_inventory_is_the_original_event (review := review) input depth count prefixLimit renewalLimit
    sourceDepth sourceCount start proposal).symm

variable (sourcePosition : Nat)

theorem completed_root_account_is_the_literal_next_input_seed
    (current : Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (same : AccountIsSourceFold (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition current)
    (complete : Bound.Complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
      start proposal sourcePosition current) :
    current.account = Inventory.before input depth count prefixLimit renewalLimit sourceDepth sourceCount
      (Inventory.physicalAfter (review := review) input depth count prefixLimit renewalLimit start proposal) := by
  have positionBound : (items).length ≤ current.position := by
    rcases current with ⟨phase⟩
    cases phase with
    | none => cases complete.1
    | some account => exact List.getElem?_eq_none_iff.mp complete.2
  rw [same, completed_event_is_the_literal_next_input_seed (review := review),
    inventory_position_is_the_same_original_fold (review := review), inventory_position_is_the_same_original_fold (review := review),
    List.take_of_length_le positionBound, List.take_length]

#print axioms inventory_position_is_the_same_original_fold
#print axioms complete_inventory_is_the_original_event
#print axioms completed_event_is_the_literal_next_input_seed
#print axioms completed_root_account_is_the_literal_next_input_seed

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Continuation

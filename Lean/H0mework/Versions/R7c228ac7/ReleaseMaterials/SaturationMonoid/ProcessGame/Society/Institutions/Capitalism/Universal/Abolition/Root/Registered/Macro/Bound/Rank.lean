import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.State

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "C" => Accounting.Current (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "items" => Inventory.items (review := review) input depth count prefixLimit renewalLimit start proposal
local notation "advance" => Accounting.next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "headAt" => Accounting.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

/-- One unit is reserved for the actual physical body. The remaining units
are exactly its already generated item positions, not money or clock time. -/
def rank (current : C) : Nat :=
  (items).length - current.position + if current.progress.isSome then 0 else 1

def Complete (current : C) : Prop := current.progress.isSome = true ∧ headAt current = none

theorem initial_rank_is_the_original_inventory :
    rank (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
      (Accounting.initial (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition) =
        (items).length - sourcePosition + 1 := rfl

theorem zero_rank_iff_complete (current : C) :
    rank (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = 0 ↔
      Complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current := by
  rcases current with ⟨phase⟩
  cases phase with
  | none =>
      change (items).length - sourcePosition + 1 = 0 ↔ false = true ∧ _
      constructor
      · intro impossible; omega
      · rintro ⟨impossible, _⟩; cases impossible
  | some account =>
      change (items).length - account.position + 0 = 0 ↔ true = true ∧ (items)[account.position]? = none
      simp only [Nat.add_zero, true_and, Nat.sub_eq_zero_iff_le, List.getElem?_eq_none_iff]

theorem each_pending_source_step_consumes_one_unit (current : C)
    (pending : 0 < rank (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) :
    rank (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition (advance current) + 1 =
      rank (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current := by
  rcases current with ⟨phase⟩
  cases phase with
  | none =>
      change (items).length - sourcePosition + 0 + 1 = (items).length - sourcePosition + 1
      omega
  | some account =>
      cases selected : Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account with
      | none =>
          have absent : (items)[account.position]? = none := selected
          have bound := List.getElem?_eq_none_iff.mp absent
          change 0 < (items).length - account.position + 0 at pending
          omega
      | some item =>
          have present : (items)[account.position]? = some item := selected
          have bound := (List.getElem?_eq_some_iff.mp present).choose
          change (items).length -
            (Accounting.Account.nextFrom (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account
              (Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account)).position + 0 + 1 =
              (items).length - account.position + 0
          rw [selected]
          change (items).length - (account.position + 1) + 0 + 1 = (items).length - account.position + 0
          omega

theorem a_complete_source_has_no_financial_head (current : C)
    (finished : Complete (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current) :
    headAt current = none ∧
      Accounting.writes (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition current = false := by
  refine ⟨finished.2, ?_⟩
  rcases current with ⟨phase⟩
  cases phase with
  | none => cases finished.1
  | some account =>
      change (Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account).isSome = false
      rw [show Accounting.Account.item? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition account = none from finished.2]
      rfl

#print axioms each_pending_source_step_consumes_one_unit
#print axioms zero_rank_iff_complete

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Bound

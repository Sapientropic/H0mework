import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

private theorem entry_le_sum {α : Type} (members : List α) (value : α → ℚ)
    (nonnegative : ∀ member ∈ members, 0 ≤ value member)
    (member : α) (listed : member ∈ members) : value member ≤ (members.map value).sum := by
  induction members with
  | nil => cases listed
  | cons first rest ih =>
      have tailPositive : 0 ≤ (rest.map value).sum := by
        apply List.sum_nonneg
        intro amount present
        obtain ⟨entry,inside,rfl⟩ := List.mem_map.mp present
        exact nonnegative entry (List.mem_cons_of_mem _ inside)
      rcases List.mem_cons.mp listed with same | later
      · subst member
        exact le_add_of_nonneg_right tailPositive
      · have lower := ih (fun entry inside => nonnegative entry (List.mem_cons_of_mem _ inside)) later
        exact lower.trans (le_add_of_nonneg_left (nonnegative first List.mem_cons_self))

theorem a_zero_full_matrix_clears_every_original_slot_balance
    (state : (process input depth count).GeneratedState)
    (matrix : ∀ instrument debtor holder, ledgerClaims input depth count state.current instrument debtor holder = 0)
    (slot : ObligationSlot (vocabulary input depth count)) (listed : slot ∈ state.current.slots) :
    slotBalance input depth count slot = 0 := by
  apply Finsupp.ext
  intro holder
  let claim := slotClaim input depth count slot
  have lower := entry_le_sum state.current.slots
    (fun entry => slotClaims input depth count entry (claim.instrument input depth count) (claim.debtor input depth count) holder)
    (fun entry inside => slotClaims_nonnegative input depth count state entry inside _ _ _) slot listed
  have total := matrix (claim.instrument input depth count) (claim.debtor input depth count) holder
  change ledgerClaims input depth count state.current _ _ _ = 0 at total
  have equal : slotClaims input depth count slot (claim.instrument input depth count) (claim.debtor input depth count) holder =
      slotBalance input depth count slot holder := by simp only [slotClaims,claim,and_self,↓reduceIte]
  change slotClaims input depth count slot _ _ _ ≤ ledgerClaims input depth count state.current _ _ _ at lower
  rw [equal,total] at lower
  exact le_antisymm lower ((generated_sound input depth count state slot listed).2 holder)

theorem every_original_row_has_an_exact_zero_or_archive_disposition
    (state : (process input depth count).GeneratedState)
    (matrix : ∀ instrument debtor holder, ledgerClaims input depth count state.current instrument debtor holder = 0)
    (slot : ObligationSlot (vocabulary input depth count)) (listed : slot ∈ state.current.slots) :
    (∃ archive, slot = .terminal archive) ∨
      ∃ obligation, slot = .live obligation ∧ obligation.residual = 0 := by
  cases slot with
  | terminal archive => exact Or.inl ⟨archive,rfl⟩
  | live obligation => exact Or.inr ⟨obligation,rfl,
      a_zero_full_matrix_clears_every_original_slot_balance input depth count state matrix _ listed⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Accounting
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Cuts

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Finance

open Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

abbrev account (shared : Bool) (ordinal : Nat) := Financial.accountAt (programme shared).input ordinal

theorem matrix (shared : Bool) (ordinal : Nat) :
    Financial.BalanceConservation.ledgerClaims (programme shared).input (account shared ordinal).current =
      ((programme shared).currentAt ordinal).claims := by
  apply Financial.BalanceConservation.generated_prefix_claims
  cases shared <;> rfl

private def archived (shared : Bool) (slot : ObligationSlot (Financial.vocabulary (programme shared).input)) : Prop :=
  match slot with | .terminal _ => True | .live _ => False

private instance (shared : Bool) (slot : ObligationSlot (Financial.vocabulary (programme shared).input)) :
    Decidable (archived shared slot) := by cases slot <;> unfold archived <;> infer_instance

theorem every_original_debt_is_archived (shared : Bool) :
    ∀ slot ∈ (account shared 11).current.slots, archived shared slot := by
  cases shared <;> decide +kernel

theorem all_claims_are_zero (shared : Bool) (instrument : Unit) (debtor holder : Party) :
    ((programme shared).currentAt 11).claims instrument debtor holder = 0 := by
  rw [← matrix]
  unfold Financial.BalanceConservation.ledgerClaims
  apply List.sum_eq_zero
  intro value member
  obtain ⟨slot, inside, rfl⟩ := List.mem_map.mp member
  have terminal := every_original_debt_is_archived shared slot inside
  cases slot with
  | terminal archive => exact Financial.BalanceConservation.slotClaims_terminal _ _ _ _ _
  | live obligation => exact terminal.elim

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Finance

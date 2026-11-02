import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Cuts

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Finance

open Institutions.Capitalism.Universal.Root

abbrev account (ordinal : Nat) := Financial.accountAt source.input ordinal

def continuation (start later : Nat) :=
  Financial.BalanceConservation.fromActualCut source.input start later

theorem all_native_positions_are_the_actual_claims (ordinal : Nat) :
    Financial.BalanceConservation.ledgerClaims source.input (account ordinal).current =
      (source.currentAt ordinal).claims :=
  Financial.BalanceConservation.generated_prefix_claims source.input zero_financial_genesis ordinal

theorem original_issues_and_native_history_survive (start later : Nat) :
    (account start).current.slots.map (Financial.slotClaim source.input) <+:
      (account (start + later)).current.slots.map (Financial.slotClaim source.input) ∧
    (account start).current.history <+: (account (start + later)).current.history :=
  ⟨Financial.BalanceConservation.cut_preserves_all_original_claims _ start later,
    Financial.BalanceConservation.cut_keeps_history _ start later⟩

def principals (ordinal : Nat) : List ℚ :=
  (account ordinal).current.slots.map fun slot =>
    Financial.total source.input (Financial.slotBalance source.input slot)

def archived (ordinal : Nat) : List Bool :=
  (account ordinal).current.slots.map fun slot => match slot with
    | .live _ => false
    | .terminal _ => true

def originalIssueCoordinates (ordinal : Nat) : List (Nat × Party × Party × ℚ) :=
  (account ordinal).current.slots.map fun slot =>
    let claim := Financial.slotClaim source.input slot
    (claim.instruction.index, claim.debtor, claim.holder, claim.quantity)

theorem actual_issue_is_admitted_and_actual_settlement_discharges_it :
    (account 0).current.slots.length = 0 ∧
    principals 2 = [1] ∧ principals 4 = [0] ∧
    Financial.BalanceConservation.ledgerClaims source.input (account 2).current () 0 2 = 1 ∧
    Financial.BalanceConservation.ledgerClaims source.input (account 4).current () 0 2 = 0 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  all_goals rw [all_native_positions_are_the_actual_claims, raw_current_frame]; decide +kernel

theorem settlement_archives_the_original_issue :
    archived 2 = [false] ∧ archived 4 = [true] ∧
    originalIssueCoordinates 2 = [(0, 0, 2, 1)] ∧
    originalIssueCoordinates 4 = [(0, 0, 2, 1)] := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Finance

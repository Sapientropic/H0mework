import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Settlement.Posted
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Posting

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt)
open Reparation Reparation.Actual

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (past : Script Party Good Port Technology Instrument)
  (visit : Installation.Core.Landed seed community (endAt seed past)
    (PostedMaterial Party Good Port Technology Instrument))
  (ordered : past.length ≤ visit.read.ordinal)
  (accepted : visit.read.effect.isAccepted = true)
  (position : Fin visit.read.effect.execution.items.length)

local notation "Site" => Settlement.postedPosition past visit ordered accepted position
local notation "Offer" => Settlement.postedOffer Site
local notation "Limit" => Settlement.deliveryLimit visit.read.programme.law (PostedPosition.item Site)
local notation "Plan" => Settlement.allocatePosted past visit ordered accepted position
local notation "Landed" => Settlement.consumePosted past visit ordered accepted position

variable (key : Key Party Good) {receipt : JointReceipt seed key}
  (issued : Settlement.postedOffer (Settlement.postedPosition past visit ordered accepted position) key = some receipt)
  (only : ∀ other : Key Party Good, other ≠ key →
    Settlement.postedOffer (Settlement.postedPosition past visit ordered accepted position) other = none)

include issued only in
/-- The original FIFO writer consumes the exact legal delivery at its
one key. Other addresses keep their prior balances and paid dispositions. -/
theorem posted_key_exact
    (origins : visit.state.stack.balances.map Prod.fst = originalLosses seed community past) :
    ∀ other, dueFor other (Landed).stack.balances = dueFor other visit.state.stack.balances -
      (if other = key then min (Limit key.2.2) (dueFor key visit.state.stack.balances) else 0) := by
  intro other
  rw [Settlement.consumePosted, StateAt.consumeMotion_balances]
  by_cases selected : other = key
  · subst other
    rw [if_pos rfl]
    have demands : Settlement.demand Offer key.2.2 visit.state.stack.balances =
        dueFor key visit.state.stack.balances := by
      apply demand_eq_key_due _ key _
      · intro row listed same
        have existsReceipt : ∃ received : JointReceipt seed row.1.key, Offer row.1.key = some received := by
          rw [same]
          exact ⟨receipt, issued⟩
        obtain ⟨received, actual⟩ := existsReceipt
        refine ⟨received, actual, ?_⟩
        obtain ⟨_, _, _, rfl⟩ := Settlement.posted_offer_is_at_its_actual_position Site _ _ actual
        have present := List.mem_map_of_mem (f := Prod.fst) listed
        rw [origins] at present
        exact every_actual_origin_birth_is_a_prefix past _ present
      · exact fun other _ different => only other different
    have tight := (Plan).tight key.2.2
    change Limit key.2.2 - ((Plan).left.balance key.2.2).remaining =
      min (Limit key.2.2) (Settlement.demand Offer key.2.2 visit.state.stack.balances) at tight
    have booked := the_unique_key_of_a_good_consumes_its_entire_booked_debit Offer Limit
      (fun k r sel => (Settlement.posted_limit_eq_quantity Site k r sel).le)
      visit.state.stack (Settlement.Available.full (Settlement.deliveryLimit_nonnegative _ _))
      key (fun other _ different => only other different)
    change dueFor key (Plan).after.balances +
      (Limit key.2.2 - ((Plan).left.balance key.2.2).remaining) =
        dueFor key visit.state.stack.balances at booked
    rw [tight, demands] at booked
    linarith only [booked]
  · rw [if_neg selected, sub_zero]
    have unchanged := allocation_keeps_every_unfunded_row Offer Limit
      (fun k r sel => (Settlement.posted_limit_eq_quantity Site k r sel).le)
      visit.state.stack (Settlement.Available.full (Settlement.deliveryLimit_nonnegative _ _))
      (· = other) (fun found same => Or.inl (only found (same.symm ▸ selected)))
    change ((Plan).after.balances.filter (fun row => decide (row.1.key = other))) = _ at unchanged
    rw [dueFor_is_the_sum_of_the_original_rows_of_the_key, dueFor_is_the_sum_of_the_original_rows_of_the_key,
      unchanged]

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.Reinterpreted

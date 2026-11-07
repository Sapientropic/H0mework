import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring.Envelope
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Consumers.Life

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring.Consumers

open Abolition.Root Abolition.Root.Registered
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers
  (lifeSource)

noncomputable section

local notation "C" => Evolving.Epoch.Current (Party := Bool) (Good := Bool) (Port := Bool)
  (Technology := Unit) (Instrument := Unit)
local notation "Script" => List (Option (Compile.RawInput Bool Bool Bool Unit Unit))

def exposures (_stage : Nat) (_current : C) (wholePeriod : Bool) : Script :=
  Robust.Consumers.exposure wholePeriod

def signal (_stage : Nat) (_current : C) : Unit := ()

theorem every_committed_policy_retains_the_actual_zero_hour_branch
    (policy : Nat → Unit → Script) :
    Failure lifeSource exposures signal policy ∧
      ¬ PolicyPaid lifeSource exposures signal policy := by
  let events : Nat → Bool := fun _ => false
  have actual := (Robust.Consumers.every_policy_has_the_original_zero_clock_obstruction (policy 0)).2.2.1
  have issue : Failure lifeSource exposures signal policy :=
    .repair events 0 actual (record lifeSource _)
  exact ⟨issue, (policy_fails_iff_an_actual_history_has_an_original_obstruction _ _ _ _).mpr issue⟩

theorem later_event_choices_leave_the_first_actual_current_and_repair_unchanged
    (policy : Nat → Unit → Script) (first second : Nat → Bool) (same : first 0 = second 0) :
    currentAt lifeSource exposures signal policy first 1 = currentAt lifeSource exposures signal policy second 1 ∧
      repairAt signal policy 0 lifeSource (exposures 0 lifeSource (first 0)) =
        repairAt signal policy 0 lifeSource (exposures 0 lifeSource (second 0)) := by
  refine ⟨equal_past_events_generate_the_same_actual_current _ _ _ _ _ _ _ ?_,
    the_committed_policy_cannot_use_an_unobserved_exposure _ _ _ _ _ _ _ rfl⟩
  intro stage earlier
  have zero : stage = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ earlier)
  simpa only [zero] using same

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Recurring.Consumers

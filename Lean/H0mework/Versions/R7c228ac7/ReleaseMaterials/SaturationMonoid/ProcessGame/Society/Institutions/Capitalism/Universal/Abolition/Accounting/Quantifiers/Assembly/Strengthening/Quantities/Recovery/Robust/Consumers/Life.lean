import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Information
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers.LifePeriod
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime.Complete

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Consumers

open Abolition.Root.Registered
open Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Primitive
  (a_whole_instruction_word_preserves_the_clock_until_the_period_boundary)
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Consumers (lifeSource lifePeriod lifeScript lifeTrace
  life_target_is_the_actual_script_successor the_two_actual_life_payments_write_the_original_ledger
  the_original_period_advances_one_actual_hour)

noncomputable section

def exposure (wholePeriod : Bool) :=
  if wholePeriod then lifePeriod else lifeScript

private theorem paid_microsteps_do_not_supply_a_work_hour : elapsed lifeSource lifeScript = 0 := by
  have clock : (Execution.endAt lifeSource lifeScript).raw.clock = lifeSource.raw.clock := by
    rw [life_target_is_the_actual_script_successor,
      Innovation.Contribution.Pricing.Root.Runtime.Trace.raw_is_the_complete_original_execution lifeTrace 0]
    exact (a_whole_instruction_word_preserves_the_clock_until_the_period_boundary
      (Physical.Public.interpreter lifeSource.native.input) lifeSource.raw 0 _).1
  unfold elapsed
  rw [clock, sub_self]

theorem every_policy_has_the_original_zero_clock_obstruction
    (policy : Unit → List (Option (Compile.RawInput Bool Bool Bool Unit Unit))) :
    Settled lifeSource (exposure false) ∧
      0 < elapsed lifeSource (exposure true) ∧
      Nonempty (BranchIssue lifeSource (exposure false) (response lifeSource (fun _ => ()) policy (exposure false))) ∧
      ¬ ValidPolicy lifeSource exposure (fun _ => ()) policy := by
  have issue : BranchIssue lifeSource (exposure false) (response lifeSource (fun _ => ()) policy (exposure false)) :=
    .clock paid_microsteps_do_not_supply_a_work_hour
  exact ⟨the_two_actual_life_payments_write_the_original_ledger,
    the_original_period_advances_one_actual_hour.symm ▸ zero_lt_one, ⟨issue⟩,
    fun valid => issue.refutes (valid false)⟩

theorem the_original_two_event_cut_consumes_the_precommitted_work_solver :
    Resolution lifeSource exposure (fun _ => ()) :=
  the_original_root_resolves_precommitted_work_conversion _ _ _

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.Robust.Consumers

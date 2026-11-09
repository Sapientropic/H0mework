import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.ExitCounterexample
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers.Life

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Actual (life lifeWord)
open Quantities.Consumers

noncomputable section

def visible (_ : C) : Unit := ()
def firstOnly (seen : History Unit) : Move := if seen.length = 1 then lifePeriod else []
def twoQuietRounds : List Move := [[], []]

theorem the_actual_first_service_is_a_fresh_exit :
    AtRound lifeSource visible firstOnly (RequiresExit lifeSource [] id) twoQuietRounds 0 :=
  ⟨real_life_service_is_a_safe_paid_round, real_life_service_is_a_safe_paid_round⟩

private theorem the_next_intervention_has_no_actual_clock :
    ¬ AtRound lifeSource visible firstOnly (RequiresExit lifeSource [] id) twoQuietRounds 1 := by
  intro positive
  have impossible := positive.1.renewal
  change (initial.run lifePeriod).current.raw.clock < (initial.run lifePeriod).current.raw.clock at impossible
  exact (lt_irrefl _) impossible

theorem a_paid_safe_round_then_stall_returns_the_first_original_failure :
    ∃ first : FirstFailureWithExit lifeSource [] id visible firstOnly twoQuietRounds,
      first.round = 1 ∧ first.originalScript = lifePeriod ∧
      Quantities.Recorded lifeSource first.originalScript := by
  cases inspectThroughWithExit lifeSource [] id visible firstOnly twoQuietRounds 2 (by decide) with
  | inr passed => exact (the_next_intervention_has_no_actual_clock (passed.down 1 (by decide))).elim
  | inl found =>
    let first : FirstFailureWithExit lifeSource [] id visible firstOnly twoQuietRounds := found.val
    have nonzero : first.round ≠ 0 := by
      intro zero
      have denied : ¬ AtRound lifeSource visible firstOnly (RequiresExit lifeSource [] id) twoQuietRounds first.round :=
        first.failure.refutes
      rw [zero] at denied
      exact denied the_actual_first_service_is_a_fresh_exit
    have bound : first.round < 2 := found.property
    have one : first.round = 1 := by omega
    refine ⟨first, one, ?_, first.original_prefix_and_next.2.1⟩
    have nothing : first.failure.consumed = [] := by
      obtain ⟨tail, source⟩ := first.failure.consumed_is_original_prefix
      have noBody : firstOnly (play lifeSource visible firstOnly (submitted twoQuietRounds) first.round).position.seen ++
          submitted twoQuietRounds first.round = [] := by
        rw [one]
        rfl
      have empty : ([] : Move) = first.failure.consumed ++ tail := noBody.symm.trans source
      exact (List.append_eq_nil_iff.mp empty.symm).1
    have earlier : (play lifeSource visible firstOnly (submitted twoQuietRounds) first.round).script = lifePeriod := by
      rw [one]
      rfl
    simp only [FirstFailureWithExit.originalScript, earlier, nothing, List.append_nil]

/-- The same physically paid period loses its claimed civilian authority
when a payer is an original command member. Actual payment remains in history. -/
def a_command_signature_is_not_a_civilian_exit :
    FirstFailureWithExit lifeSource [true] id visible firstOnly [[]] :=
  ⟨0, by decide, fun _ impossible => (Nat.not_lt_zero _ impossible).elim,
    .actual (.intervention
      ⟨[], service, [], rfl, trivial, .signature rfl (life true)
        (by decide +kernel : life true ∈ lifeWord)
        (fun owned => owned.2.1 (by decide +kernel))⟩)⟩

theorem the_paid_period_does_not_authorize_a_command_signature_for_civilians :
    ¬ AtRound lifeSource visible firstOnly (RequiresExit lifeSource [true] id) [[]] 0 ∧
      Quantities.Recorded lifeSource a_command_signature_is_not_a_civilian_exit.originalScript :=
  ⟨a_command_signature_is_not_a_civilian_exit.failure.refutes,
    a_command_signature_is_not_a_civilian_exit.original_prefix_and_next.2.1⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers

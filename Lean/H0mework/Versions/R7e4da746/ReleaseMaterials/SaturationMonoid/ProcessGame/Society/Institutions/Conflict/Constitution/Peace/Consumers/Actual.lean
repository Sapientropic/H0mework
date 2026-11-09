import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Contract
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Consumers.Obstruction

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Consumers

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Consumers (lifeSource lifePeriod)
open Civil.Persistence
open Civil.Persistence.Consumers

noncomputable section

theorem the_actual_life_payment_generates_a_protected_whole_ledger :
    ProtectedRound (seed := lifeSource) (community := id) (past := []) (observe := visible)
      (strategy := firstOnly) [] (submitted twoQuietRounds) 0 :=
  round_on_the_original_ledger (submitted twoQuietRounds) 0 the_actual_first_service_is_a_fresh_exit

theorem the_next_stall_writes_the_first_failed_original_prefix :
    ∃ first : FirstFailureWithExit lifeSource [] id visible firstOnly twoQuietRounds,
      first.round = 1 ∧ first.originalScript = lifePeriod ∧
      AccountedFailure (seed := lifeSource) (past := []) first := by
  obtain ⟨first, round, exactPrefix, _⟩ := a_paid_safe_round_then_stall_returns_the_first_original_failure
  exact ⟨first, round, exactPrefix, first_failure_consumes_the_original_prefix_and_keeps_the_complete_ledger _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Peace.Consumers

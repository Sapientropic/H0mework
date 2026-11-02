import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Runtime

/-! Every finite continuation is consumed from its own actual source root.
Both obstruction branches supply the next complete inventory. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Iteration
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section

def run (packet : Packet) : Nat → Packet
  | 0 => packet
  | count + 1 => run ((Runtime.continuationFromRoot packet.2).packet packet.2) count

theorem run_is_the_actual_source_evolution (packet : Packet) (count : Nat) : run packet count = evolve packet count := by
  induction count generalizing packet with
  | zero => rfl
  | succ count ih =>
      change run ((Runtime.continuationFromRoot packet.2).packet packet.2) count = evolve (next packet.2) count
      rw [ContinuationDisposition.next_exact,ih]

abbrev Step := Sigma fun packet : Packet => ContinuationDisposition packet.2

def trace (packet : Packet) : Nat → List Step
  | 0 => []
  | count + 1 => ⟨packet,Runtime.continuationFromRoot packet.2⟩ ::
      trace ((Runtime.continuationFromRoot packet.2).packet packet.2) count

theorem trace_has_every_actual_decision (packet : Packet) (count : Nat) : (trace packet count).length = count := by
  induction count generalizing packet with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ (ih _)

def financialRun (packet : Packet) : (count : Nat) →
    (Financial.Family.process sources).Run packet.2.finance.current (run packet count).2.finance.current
  | 0 => .nil
  | count + 1 => (Runtime.continuationFromRoot packet.2).financialRun packet.2 |>.concatRuns _
      (financialRun ((Runtime.continuationFromRoot packet.2).packet packet.2) count)

theorem all_past_cohorts_are_consumed (packet : Packet) (count : Nat) :
    packet.2.pastGrants.map GrantCohort.origin <+: (run packet count).2.pastGrants.map GrantCohort.origin ∧
    packet.2.pastChallenges.map ChallengeCohort.origin <+: (run packet count).2.pastChallenges.map ChallengeCohort.origin ∧
    packet.2.pastServices.map ServiceCohort.origin <+: (run packet count).2.pastServices.map ServiceCohort.origin := by
  rw [run_is_the_actual_source_evolution]
  exact finite_epoch_chains_preserve_every_original_cohort packet count

theorem full_matrix_at_every_generated_cut (packet : Packet) (count : Nat) :
    Financial.Family.ledgerClaims sources (run packet count).2.finance.current =
      (current (run packet count).1 (run packet count).2.inputs).claims := (run packet count).2.matrix

def nextDisposition (packet : Packet) (count : Nat) := Runtime.continuationFromRoot (run packet count).2

theorem every_finite_cut_has_its_own_actual_disposition (packet : Packet) (count : Nat) :
    (nextDisposition packet count).decision = continuationDecision (run packet count).2 ∧
    (nextDisposition packet count).packet (run packet count).2 = next (run packet count).2 :=
  ⟨(nextDisposition packet count).decision_exact,(nextDisposition packet count).next_exact _⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Iteration

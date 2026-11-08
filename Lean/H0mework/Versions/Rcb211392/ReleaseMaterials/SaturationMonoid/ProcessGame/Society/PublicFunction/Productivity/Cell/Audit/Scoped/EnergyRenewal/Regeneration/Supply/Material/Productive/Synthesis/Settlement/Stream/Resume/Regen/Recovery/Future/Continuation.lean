import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle

private theorem continue_visits_append (input : Finance.Input) (start first later : Nat)
    (before : Finance.Account) :
    Financial.Family.continueVisits Finance.sources input (start + first) later
      (Financial.Family.continueVisits Finance.sources input start first before) =
      Financial.Family.continueVisits Finance.sources input start (first + later) before := by
  induction later with
  | zero => simp only [Financial.Family.continueVisits, Nat.add_zero]
  | succ later previous =>
    change Financial.Family.consumeVisit Finance.sources input (start + first + later) _ = _
    rw [previous]
    simp only [Financial.Family.continueVisits, Nat.add_assoc]
    rfl

variable {seed : Seed} {oldRequests : Requests.Source} {oldPermission : Material.Mode} {baseCut : Nat}
  {source : Inherited seed oldRequests oldPermission baseCut}
  {requests : Requests.Source} {authority : Authority} {index : Nat}
  {cut : Cut source requests authority index} {count : Nat}
  (original : Snapshot cut count)
  (futureRequests : Requests.Source) (futureAuthority : Authority) (futurePermission : Material.Mode)

theorem every_intermediate_window_survives_its_remaining_future (first later : Nat)
    (window : Requests.Window seed.basis)
    (tracked : Tracked (run original futureRequests futureAuthority futurePermission first).protocol window) :
    Tracked (run original futureRequests futureAuthority futurePermission (first + later)).protocol window := by
  induction later with
  | zero => simpa only [Nat.add_zero] using tracked
  | succ later previous =>
    rw [Nat.add_succ, run_succ]
    exact step_preserves_every_tracked_window original futureRequests futureAuthority futurePermission
      (first + later) _ window previous

namespace Runtime

local notation "prog" => input original futureRequests futureAuthority futurePermission
local notation "start" => startAt (baseCut := baseCut) (index := index) (count := count)

theorem every_actual_account_generates_the_remaining_account (first later : Nat) :
    Financial.Family.continueVisits Finance.sources prog (start + first) later
      (account original futureRequests futureAuthority futurePermission first) =
      account original futureRequests futureAuthority futurePermission (first + later) :=
  continue_visits_append prog start first later original.account

def remainingRun (first later : Nat) :
    (Financial.Family.process Finance.sources).Run
      (account original futureRequests futureAuthority futurePermission first).current
      (account original futureRequests futureAuthority futurePermission (first + later)).current := by
  rw [← every_actual_account_generates_the_remaining_account original futureRequests futureAuthority futurePermission first later]
  exact Financial.Family.continueVisits_run Finance.sources prog (start + first) later
    (account original futureRequests futureAuthority futurePermission first)

theorem every_intermediate_native_archive_is_preserved (first later position : Nat)
    (archive : TerminalArchive (Financial.Family.vocabulary Finance.sources))
    (present : (account original futureRequests futureAuthority futurePermission first).current.slots[position]? = some (.terminal archive)) :
    (account original futureRequests futureAuthority futurePermission (first + later)).current.slots[position]? = some (.terminal archive) := by
  let carried := Financial.Family.Migration.follow Finance.sources
    (remainingRun original futureRequests futureAuthority futurePermission first later) position (.terminal archive) present
  exact carried.present.trans (congrArg some (carried.path.terminal_is_unchanged Finance.sources))

theorem full_carrier_continues_from_its_own_actual_after (first later : Nat) :
    evolve original futureRequests futureAuthority futurePermission first
      (run original futureRequests futureAuthority futurePermission first) later =
        run original futureRequests futureAuthority futurePermission (first + later) ∧
    Financial.Family.continueVisits Finance.sources prog (start + first) later
      (account original futureRequests futureAuthority futurePermission first) =
        account original futureRequests futureAuthority futurePermission (first + later) :=
  ⟨every_actual_after_generates_the_remaining_future original futureRequests futureAuthority futurePermission first later,
    every_actual_account_generates_the_remaining_account original futureRequests futureAuthority futurePermission first later⟩

end Runtime
end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future

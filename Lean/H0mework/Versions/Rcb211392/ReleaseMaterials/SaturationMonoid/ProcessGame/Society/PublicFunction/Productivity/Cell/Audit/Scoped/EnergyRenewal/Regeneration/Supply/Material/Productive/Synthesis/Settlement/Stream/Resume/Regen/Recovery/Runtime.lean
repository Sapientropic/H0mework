import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Runtime

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {seed : Seed} {oldRequests : Requests.Source} {permission : Material.Mode} {baseCut : Nat}
  {source : Inherited seed oldRequests permission baseCut}
  {requests : Requests.Source} {authority : Authority} {index : Nat}
  (cut : Cut source requests authority index)

local notation "startAt" => handoff (baseCut := baseCut) index
local notation "prog" => input cut

def activated (offset : Nat) := ProgrammeHistory.activated prog (startAt + offset)

private theorem activation_index (offset : Nat) :
    (show Nat from (activated cut offset).state) = startAt + offset :=
  ProgrammeHistory.activated_state prog (startAt + offset)

def execution (offset : Nat) :=
  match (ProgrammeHistory.facade prog).readoutAt (activated cut offset) .execution with
  | .inl ⟨_, payload⟩ => payload
  | .inr impossible => nomatch impossible

def after (offset : Nat) := run cut (offset + 1)

def account (offset : Nat) : Finance.Account :=
  Financial.Family.continueVisits Finance.sources prog startAt (offset + 1) cut.after.account

def actualRun (offset : Nat) :
    (Financial.Family.process Finance.sources).Run cut.after.account.current (account cut offset).current :=
  Financial.Family.continueVisits_run Finance.sources prog startAt (offset + 1) cut.after.account

theorem original_actual_before (offset : Nat) :
    (execution cut offset).before = (run cut offset).raw := by
  exact (congrArg (fun n : Nat => ProgrammeSource.rawCurrent prog (ProgrammeHistory.visitAt prog n).current)
    (activation_index cut offset)).trans (own_current cut offset)

theorem actual_submitted (offset : Nat) :
    (execution cut offset).submitted =
      admittedWord cut offset (run cut offset) := by
  exact (congrArg (fun n : Nat => ProgrammeSource.rawEvent prog (ProgrammeHistory.visitAt prog n).current)
    (activation_index cut offset)).trans (selected_word cut offset)

theorem actual_after (offset : Nat) : (execution cut offset).after = (after cut offset).raw := by
  let material (n : Nat) := (ProgrammeLiving.executionFace prog
    (ProgrammeSource.emitted prog (ProgrammeHistory.visitAt prog n).current)).after
  exact (congrArg material (activation_index cut offset)).trans
    ((ProgrammeLiving.projected_execution_uses_actual_root_next prog
      (ProgrammeHistory.visitAt prog (startAt + offset)).current).trans (own_current cut (offset + 1)))

theorem first_is_the_original_activated_next :
    HEq (activated cut 0).current.visit.current
      (Regen.Runtime.activated source requests authority index).tick.nextCurrent.visit.current := by
  have next := (Regen.Runtime.same_occurrence_whole_ledger_and_own_next source requests authority index).2.2.trans
    (congrArg (fun n : Nat => (Regen.Runtime.process source requests authority).stateAt (n + 1))
      (Regen.Runtime.activated_state source requests authority index))
  rw [next]
  exact heq_of_eq ((congrArg (fun n : Nat => (ProgrammeHistory.visitAt prog n).current)
    (activation_index cut 0)).trans (original_current_prefix cut _ (le_refl _)))

theorem the_original_frame_computes_this_exact_after (ready : OpeningAt cut) (offset : Nat) :
    after cut offset =
      runFrom seed requests authority permission (index + 1)
        (Regen.run source requests authority (index + 1)) (offset + 1) := by
  rw [after, run_uses_original_frame_when_ready cut ready, cut.after.frameExact]

theorem whole_ledger_and_own_next (offset : Nat) :
    HEq (activated cut offset).tick.generated.wholeLedgerWriteBack
      ((activated cut offset).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated cut offset).current.visit.current) ∧
    (activated cut offset).tick.nextCurrent = (activated cut (offset + 1)).current := by
  have factorization := ProgrammeHistory.execution_face_shares_whole_ledger_and_next prog (startAt + offset)
  refine ⟨factorization.2.2.1, ?_⟩
  exact factorization.2.2.2.2.trans
    ((congrArg (fun n : Nat => (ProgrammeHistory.process prog).stateAt (n + 1))
      (activation_index cut offset)).trans
      (congrArg (fun n : Nat => (ProgrammeHistory.process prog).stateAt n)
        (activation_index cut (offset + 1))).symm)

theorem original_history_is_kept (offset : Nat) :
    cut.after.account.current.history <+: (account cut offset).current.history := by
  rw [(actualRun cut offset).history_eq]
  exact List.prefix_append _ _

theorem original_archives_are_kept (offset position : Nat)
    (archive : TerminalArchive (Financial.Family.vocabulary Finance.sources))
    (present : cut.after.account.current.slots[position]? = some (.terminal archive)) :
    (account cut offset).current.slots[position]? = some (.terminal archive) := by
  let carried := Financial.Family.Migration.follow Finance.sources (actualRun cut offset)
    position (.terminal archive) present
  exact carried.present.trans (congrArg some (carried.path.terminal_is_unchanged Finance.sources))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Runtime

import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.Pressure
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Stop

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction (PublicTaskSpec)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Task" => PublicTaskSpec Party Good

structure ProtectedStop (source : C) (community : Party → Community) (command : List Party)
    (task : Task) (front calm exit : Word) (submitted : List Word) : Prop where
  civilian : Civil.CivilAction source command front
  stopped : ∀ word ∈ submitted, ¬ Nonempty (Boundary.AggressionAt source (front ++ word) community)
  independent : Civil.ExitAt source command task (front ++ calm) exit
  peacefulExit : ¬ Nonempty (Boundary.AggressionAt source ((front ++ calm) ++ exit) community)

inductive StopResult (source : C) (community : Party → Community) (command : List Party)
    (task : Task) (front calm exit : Word) (submitted : List Word)
  | blockedAction (failure : ¬ Civil.CivilAction source command front)
  | bypass (word : Word) (listed : word ∈ submitted) (attack : Boundary.AggressionAt source (front ++ word) community)
  | blockedExit (failure : Civil.ExitFailure source command task (front ++ calm) exit)
  | captureInExit (attack : Boundary.AggressionAt source ((front ++ calm) ++ exit) community)
  | stopped (actual : ProtectedStop source community command task front calm exit submitted)

/-- Reclassify all originally submitted plans after the actual civil prefix.
An executable but no longer aggressive plan no longer counts as a bypass. -/
def inspectStop (source : C) (community : Party → Community) (command : List Party) (task : Task)
    (front calm exit : Word) (submitted : List Word) :
    StopResult source community command task front calm exit submitted :=
  if civic : Civil.CivilAction source command front then
    match scanned : aggressors source community (submitted.map (front ++ ·)) with
    | [] =>
      have stopped : ∀ word ∈ submitted, ¬ Nonempty (Boundary.AggressionAt source (front ++ word) community) :=
        fun word listed => (aggressors_empty_iff source community _).mp scanned _ (List.mem_map_of_mem listed)
      match Civil.inspectExit source command task (front ++ calm) exit with
      | .inl issue => .blockedExit issue
      | .inr ⟨actual⟩ =>
        match measured : Boundary.aggressions source ((front ++ calm) ++ exit) community actual.actual with
        | first :: _ => .captureInExit first
        | [] =>
          .stopped ⟨civic, stopped, actual, by
            rintro ⟨capture⟩
            have member := capture.listed_in_generated_aggressions
            rw [measured] at member
            exact List.not_mem_nil member⟩
    | first :: _ =>
      have found : first ∈ aggressors source community (submitted.map (front ++ ·)) := scanned ▸ List.mem_cons_self
      have actual := List.mem_filter.mp found
      have shape := List.mem_map.mp (Root.mem_admitted.mp actual.1)
      have classified := (isAggressive_exact first).mp actual.2
      Classical.choice (show Nonempty (StopResult source community command task front calm exit submitted) from by
        obtain ⟨word, listed, same⟩ := shape
        exact ⟨.bypass word listed (same.symm ▸ Classical.choice classified)⟩)
  else .blockedAction civic

set_option maxHeartbeats 600000 in
theorem inspectStop_returns_each_protected_stop
    {source : C} {community : Party → Community} {command : List Party}
    {task : Task} {front calm exit : Word} {submitted : List Word}
    (stop : ProtectedStop source community command task front calm exit submitted) :
    inspectStop source community command task front calm exit submitted = .stopped stop := by
  have all := (aggressors_empty_iff source community (submitted.map (front ++ ·))).mpr (by
    intro word listed
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp listed
    exact stop.stopped original member)
  unfold inspectStop
  rw [dif_pos stop.civilian]
  split
  · cases chosen : Civil.inspectExit source command task (front ++ calm) exit with
    | inl failure =>
        obtain ⟨_, paid⟩ := Civil.inspectExit_selects_every_paid_independent_exit stop.independent
        rw [chosen] at paid
        cases paid
    | inr certificate =>
        cases certificate
        dsimp only
        split
        · rename_i capture rest found
          exact (stop.peacefulExit ⟨capture⟩).elim
        · rfl
  · rename_i first tail found
    rw [all] at found
    cases found

theorem a_protected_stop_rejects_all_m11_bypasses_on_its_covered_source
    {source : C} {community : Party → Community} {command : List Party}
    {task : Task} {front calm exit : Word} {submitted : List Word}
    (stop : ProtectedStop source community command task front calm exit submitted)
    (covered : ∀ word, Nonempty (Boundary.AggressionAt source (front ++ word) community) → word ∈ submitted) :
    (∀ word, ¬ Nonempty (Boundary.AggressionAt source (front ++ word) community)) ∧
      Quantities.Settled source (Quantities.Execution.primitiveScript ((front ++ calm) ++ exit)) :=
  ⟨fun word attempt => stop.stopped word (covered word attempt) attempt, stop.independent.actual.whole⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution

import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Agenda
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Exit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root
open PublicFunction (PublicTaskSpec)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Task" => PublicTaskSpec Party Good

def CivilAction (source : C) (command : List Party) (front : Word) : Prop :=
  front ≠ [] ∧ ∀ item ∈ (Physical.Public.interpreter source.native.input).rawItems source.raw front,
    Quantities.Exit.Grant.Independent source command item

instance (source : C) (command : List Party) (front : Word) : Decidable (CivilAction source command front) := by
  unfold CivilAction
  infer_instance

structure Stopped (source : C) (command : List Party) (task : Task)
    (front calm exit : Word) (war : List Word) where
  civilian : CivilAction source command front
  refusals : ∀ word ∈ war, Refused source (front ++ word)
  independentExit : ExitAt source command task (front ++ calm) exit

inductive StopDecision (source : C) (command : List Party) (task : Task)
    (front calm exit : Word) (war : List Word)
  | noCivilAction (missing : ¬ CivilAction source command front)
  | bypass (word : Word) (listed : word ∈ war) (actual : Root.Paid source (front ++ word))
  | noExit (reason : ExitFailure source command task (front ++ calm) exit)
  | stopped (actual : Stopped source command task front calm exit war)

/-- A refusal is chosen before any offensive alternative. The successful
outcome spends only the chosen original word, including the independent exit. -/
def tryStop (source : C) (command : List Party) (task : Task)
    (front calm exit : Word) (war : List Word) : StopDecision source command task front calm exit war :=
  if civic : CivilAction source command front then
    match inspectAgenda source front war with
    | .bypass word listed actual => .bypass word listed actual
    | .blocked refusals =>
        match inspectExit source command task (front ++ calm) exit with
        | .inl issue => .noExit issue
        | .inr actual => .stopped ⟨civic, refusals, actual.down⟩
  else .noCivilAction civic

theorem Stopped.no_attack {source : C} {command : List Party} {task : Task}
    {front calm exit : Word} {war : List Word}
    (stopped : Stopped source command task front calm exit war) : noAttack source front war :=
  fun word listed => refused_word_is_not_paid (stopped.refusals word listed)

theorem Stopped.actual_civil_prefix {source : C} {command : List Party} {task : Task}
    {front calm exit : Word} {war : List Word}
    (stopped : Stopped source command task front calm exit war) :
    Runtime.Trace source front (Root.terminal source front) := by
  apply Root.trace_before_prefix source (Root.terminal source ((front ++ calm) ++ exit)) front (calm ++ exit)
  simpa only [List.append_assoc] using stopped.independentExit.actual.trace

theorem Stopped.prevents_a_profitable_attack_and_pays_the_original_exit
    {source : C} {command : List Party} {task : Task} {front calm exit : Word} {war peace : List Word}
    (stopped : Stopped source command task front calm exit war) (read : C → ℚ) (margin : ℚ)
    (old : Root.pressure source read war peace = some margin) (profitable : 0 < margin) :
    (∃ offensive ∈ war, ∃ baseline ∈ peace, Root.Paid source offensive ∧ Root.Paid source baseline ∧
      read (Root.terminal source baseline) < read (Root.terminal source offensive)) ∧
    afterPressure source read front war peace = none ∧
    Quantities.Recorded source (Quantities.Execution.primitiveScript ((front ++ calm) ++ exit)) ∧
    Evolving.Epoch.Current.ClosedAt (Root.terminal source ((front ++ calm) ++ exit)) := by
  obtain ⟨offensive, own, baseline, chosen, warPaid, peacePaid, gap, _, _⟩ :=
    Root.pressure_is_the_gap_between_the_best_paid_alternatives _ _ _ _ _ old
  refine ⟨⟨offensive, own, baseline, chosen, warPaid, peacePaid, sub_pos.mp (gap ▸ profitable)⟩,
    a_hard_stop_leaves_no_comparable_attack _ _ _ _ _ stopped.no_attack, ?_⟩
  exact an_independent_exit_has_the_original_prefix_and_whole_successor stopped.independentExit

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil

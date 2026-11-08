import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Restitution
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.ExitFloor
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Plan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction (PublicTaskSpec)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Task" => PublicTaskSpec Party Good
local notation "script" => Quantities.Execution.primitiveScript

def protectedMembers (origin : C) (command : List Party) : List Party :=
  origin.members.filter (fun person => decide (person ∉ command))

def PositiveSlot (task : Task) (person : Party) : Prop :=
  ∃ slot ∈ task.slots, slot.bearer = person ∧ ∃ lot ∈ slot.goods, 0 < lot.2

instance (task : Task) (person : Party) : Decidable (PositiveSlot task person) := by
  unfold PositiveSlot
  infer_instance

def Covered (cut : C) (task : Task) (person : Party) : Prop :=
  person ∈ cut.members ∧ PositiveSlot task person

instance (cut : C) (task : Task) (person : Party) : Decidable (Covered cut task person) := by
  unfold Covered
  infer_instance

/-- The prefix may pay general obligations. The independent exit suffix is
checked only against its own real inventory and original due window. -/
structure ExitAt (origin : C) (command : List Party) (task : Task) (front exit : Word) : Prop where
  actual : Root.Paid origin (front ++ exit)
  nonempty : protectedMembers origin command ≠ []
  preserves : ∀ person ∈ protectedMembers origin command, Covered (Root.terminal origin front) task person
  independent : ∀ item ∈ Quantities.Execution.inventory (Root.terminal origin front) (script exit),
    Quantities.Exit.Grant.Independent (Root.terminal origin front) command item
  serves : Quantities.Clock.Window.FullyServed (Root.terminal origin front) task (script exit)
  originalFloor : Boundary.floorPaid origin (Root.terminal origin front) (protectedMembers origin command) exit

inductive ExitFailure (origin : C) (command : List Party) (task : Task) (front exit : Word)
  | original (issue : Root.Failure origin (front ++ exit))
  | noCivilian (missing : protectedMembers origin command = [])
  | uncovered (person : Party) (original : person ∈ protectedMembers origin command)
      (missing : ¬ Covered (Root.terminal origin front) task person)
  | dependence (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ Quantities.Execution.inventory (Root.terminal origin front) (script exit))
      (controlled : ¬ Quantities.Exit.Grant.Independent (Root.terminal origin front) command item)
  | shortage (issue : Quantities.Clock.Window.Shortage (Root.terminal origin front) task (script exit))
  | floor (cell : Party × Use × Good × ℚ) (original : cell ∈ Boundary.floorCells origin (protectedMembers origin command))
      (short : Boundary.deliveredAt (Root.terminal origin front) exit cell < cell.2.2.2)

def inspectExit (origin : C) (command : List Party) (task : Task) (front exit : Word) :
    ExitFailure origin command task front exit ⊕ PLift (ExitAt origin command task front exit) :=
  match Root.inspect origin (front ++ exit) with
  | .rejected issue => .inl (.original issue)
  | .paid actual =>
      let cut := Root.terminal origin front
      if empty : protectedMembers origin command = [] then .inl (.noCivilian empty)
      else match Material.inspectList (Covered cut task) (protectedMembers origin command) with
      | .failure person member missing => .inl (.uncovered person member missing)
      | .clear members =>
        match Material.inspectList (Quantities.Exit.Grant.Independent cut command)
            (Quantities.Execution.inventory cut (script exit)) with
        | .failure item member controlled => .inl (.dependence item member controlled)
        | .clear independent =>
          match found : Quantities.Clock.Window.inspect cut task (script exit) with
          | some issue => .inl (.shortage issue)
          | none =>
            match Material.inspectList (fun cell : Party × Use × Good × ℚ =>
                cell.2.2.2 ≤ Boundary.deliveredAt cut exit cell)
                (Boundary.floorCells origin (protectedMembers origin command)) with
            | .failure cell member denied => .inl (.floor cell member (lt_of_not_ge denied))
            | .clear floor => .inr ⟨⟨actual, empty, members, independent,
                (Quantities.Clock.Window.passes_iff_every_original_service_commits_in_time _ _ _).mp found, floor⟩⟩

theorem an_independent_exit_has_the_original_prefix_and_whole_successor
    {origin : C} {command : List Party} {task : Task} {front exit : Word}
    (paid : ExitAt origin command task front exit) :
    Quantities.Recorded origin (script (front ++ exit)) ∧
      Evolving.Epoch.Current.ClosedAt (Root.terminal origin (front ++ exit)) :=
  ⟨paid.actual.whole.toRecorded, paid.actual.whole.next⟩

theorem inspectExit_selects_every_paid_independent_exit
    {origin : C} {command : List Party} {task : Task} {front exit : Word}
    (paid : ExitAt origin command task front exit) :
    ∃ receipt, inspectExit origin command task front exit = .inr ⟨receipt⟩ := by
  let cut := Root.terminal origin front
  have admitted := (Root.inspect_accepts_iff origin (front ++ exit)).mpr paid.actual
  unfold inspectExit
  cases found : Root.inspect origin (front ++ exit) with
  | rejected issue => rw [found] at admitted; cases admitted
  | paid execution =>
    simp only [dif_neg paid.nonempty]
    cases Material.inspectList (Covered cut task) (protectedMembers origin command) with
    | failure person original missed => exact (missed (paid.preserves person original)).elim
    | clear members =>
      cases Material.inspectList (Quantities.Exit.Grant.Independent cut command)
          (Quantities.Execution.inventory cut (script exit)) with
      | failure item original controlled => exact (controlled (paid.independent item original)).elim
      | clear independent =>
        have service := (Quantities.Clock.Window.passes_iff_every_original_service_commits_in_time
          cut task (script exit)).mpr paid.serves
        simp only [cut] at service
        dsimp only
        split
        · rename_i issue selected
          rw [service] at selected
          cases selected
        · cases Material.inspectList (fun cell : Party × Use × Good × ℚ =>
              cell.2.2.2 ≤ Boundary.deliveredAt cut exit cell)
              (Boundary.floorCells origin (protectedMembers origin command)) with
          | failure cell member denied => exact (denied (paid.originalFloor cell member)).elim
          | clear checked => exact ⟨paid, rfl⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil

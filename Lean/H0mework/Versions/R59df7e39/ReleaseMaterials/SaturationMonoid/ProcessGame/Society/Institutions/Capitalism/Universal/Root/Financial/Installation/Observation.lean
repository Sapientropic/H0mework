import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.ExecutedHistory
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Material.Bearers
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Structural.Law

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

open Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

structure Observation where
  current : Cursor.State input
  following : Cursor.State input
  following_exact : following = Cursor.next input current
  pending : Cursor.PendingInventory input current
  pendingAfter : Cursor.PendingInventory input following
  completed : ActualBirth.Visit input
  completed_exact : completed = Cursor.lastExecutedVisit input current
  completedNext_exact : input.law.next (ProgrammeSource.rawCurrent input completed.current)
      (ProgrammeSource.rawEvent input completed.current) = Material.rawAt input following
  members : List Party
  members_exact : members = ActualBirth.participants input completed
  memberBirth : ∀ person ∈ members, ActualBirth.At input completed person
  completedControls : List (Source.ProgrammeControl.ControlUse input.law
    (ProgrammeSource.rawCurrent input completed.current) (ProgrammeSource.rawEvent input completed.current)
    (Structural.familyAtVisit input completed))
  completedControls_exact : completedControls = Source.ProgrammeControl.controlInventory input.law
    (ProgrammeSource.rawCurrent input completed.current) (ProgrammeSource.rawEvent input completed.current)
    (Structural.familyAtVisit input completed)
  completeStructure : Structural.Total input
  materialBalance : ∀ location : Party × Good,
    (Material.rawAt input following).stock location.1 location.2 +
        Material.use input .necessity current location + Material.use input .maintenance current location +
        Material.other input current location =
      (Material.rawAt input current).stock location.1 location.2 + Material.dependent input current location +
        Material.independent input current location + Material.unresolved input current location
  unresolvedReceiver : ∀ location : Party × Good, 0 < Material.unresolved input current location →
    ActualBirth.At input (Cursor.physicalVisit input current) location.1

def observe (current : Cursor.State input) : Observation input where
  current := current
  following := Cursor.next input current
  following_exact := rfl
  pending := Cursor.pendingInventory input current
  pendingAfter := Cursor.pendingInventory input (Cursor.next input current)
  completed := Cursor.lastExecutedVisit input current
  completed_exact := rfl
  completedNext_exact := Cursor.last_execution_returns_actual_physical_current input current
  members := ActualBirth.participants input (Cursor.lastExecutedVisit input current)
  members_exact := rfl
  memberBirth := fun person present =>
    ActualBirth.fromHistory input (Cursor.lastExecutedVisit input current) person present
  completedControls := Source.ProgrammeControl.controlInventory input.law
    (ProgrammeSource.rawCurrent input (Cursor.lastExecutedVisit input current).current)
    (ProgrammeSource.rawEvent input (Cursor.lastExecutedVisit input current).current)
    (Structural.familyAtVisit input (Cursor.lastExecutedVisit input current))
  completedControls_exact := rfl
  completeStructure := Structural.all_source_forms_total input
  materialBalance := Material.actual_balance input current
  unresolvedReceiver := Material.unresolvedReceiverBirth input current

/-- This finite read retains original access ordinals.  Reading it again
on bookkeeping ticks never counts an old access as a new renewal. -/
def Observation.completedCyclesSince (observation : Observation input) (cutoff : Nat) :=
  Source.ProgrammeControl.History.completedSince input
    (Source.ProgrammeControl.History.actual input observation.completed) cutoff

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation

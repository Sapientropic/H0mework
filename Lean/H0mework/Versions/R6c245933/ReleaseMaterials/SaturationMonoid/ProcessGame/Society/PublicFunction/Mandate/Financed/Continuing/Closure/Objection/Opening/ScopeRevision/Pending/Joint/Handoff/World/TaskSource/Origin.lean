import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction
open Institutions.Capitalism.Universal.Source.Program
open Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World
open Computation.Search.Segmented.Publication.Learning.Paid

namespace Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {law : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}

def TaskInput.withOrigin (input : TaskInput law scope) (origin : FutureOrigin input.packet) :
    TaskInput law scope := by
  cases input with
  | actual inventory => exact .received inventory origin
  | received inventory _previous => exact .received inventory origin

theorem TaskInput.withOrigin_packet (input : TaskInput law scope) (origin : FutureOrigin input.packet) :
    (input.withOrigin origin).packet = input.packet := by cases input <;> rfl

theorem TaskInput.withOrigin_origin (input : TaskInput law scope) (origin : FutureOrigin input.packet) :
    (TaskInput.withOrigin_packet input origin) ▸ (input.withOrigin origin).futureOrigin = some origin := by
  cases input <;> rfl

theorem TaskInput.withOrigin_worldAt (input : TaskInput law scope) (origin : FutureOrigin input.packet)
    (source : Distributed.Reaction.Machine Party Good Port (Mandate.State Party Technology) Instrument)
    (cut : Nat) :
    Owned.WorldAt (input.withOrigin origin) source cut ↔ Owned.WorldAt input source cut := by
  cases input <;> rfl


def TaskInput.bindAt (stored : Option (TaskInput law scope)) (packet : Packet)
    (same : stored.map TaskInput.packet = some packet) (basis : FutureOrigin packet) : TaskInput law scope :=
  match stored with
  | none => False.elim (by cases same)
  | some input =>
      have packets : input.packet = packet := Option.some.inj same
      input.withOrigin (packets.symm ▸ basis)

def TaskInput.originAt (stored : Option (TaskInput law scope)) (packet : Packet)
    (same : stored.map TaskInput.packet = some packet) : Option (FutureOrigin packet) :=
  match stored with
  | none => none
  | some input =>
      have packets : input.packet = packet := Option.some.inj same
      packets ▸ input.futureOrigin

theorem TaskInput.bindAt_packet (stored : Option (TaskInput law scope)) (packet : Packet)
    (same : stored.map TaskInput.packet = some packet) (basis : FutureOrigin packet) :
    (bindAt stored packet same basis).packet = packet := by
  cases stored with
  | none => cases same
  | some input =>
      change (input.withOrigin _).packet = packet
      rw [TaskInput.withOrigin_packet]
      exact Option.some.inj same

theorem TaskInput.bindAt_origin (stored : Option (TaskInput law scope)) (packet : Packet)
    (same : stored.map TaskInput.packet = some packet) (basis : FutureOrigin packet) :
    originAt (some (bindAt stored packet same basis)) packet
      (congrArg some (bindAt_packet stored packet same basis)) = some basis := by
  cases stored with
  | none => cases same
  | some input =>
      have packets : input.packet = packet := Option.some.inj same
      cases packets
      exact TaskInput.withOrigin_origin input basis

theorem TaskInput.bindAt_worldAt (stored : Option (TaskInput law scope)) (packet : Packet)
    (same : stored.map TaskInput.packet = some packet) (basis : FutureOrigin packet)
    (source : Distributed.Reaction.Machine Party Good Port (Mandate.State Party Technology) Instrument)
    (cut : Nat) (old : ∀ input,stored = some input → Owned.WorldAt input source cut) :
    Owned.WorldAt (bindAt stored packet same basis) source cut := by
  cases stored with
  | none => cases same
  | some input =>
      change Owned.WorldAt (input.withOrigin _) source cut
      exact (TaskInput.withOrigin_worldAt input _ source cut).mpr (old input rfl)

end Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

namespace Computation.Search.Segmented.Publication.Learning.Paid.Owned
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

variable (packet : Packet) (same : task.worldInput.map TaskInput.packet = some packet)

def Task.originAt : Option (FutureOrigin packet) := TaskInput.originAt task.worldInput packet same

/-- Only provenance and its dependent occurrence proof change. -/
def Task.withOriginAt (basis : FutureOrigin packet) : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) :=
  { task with
    worldInput := some (TaskInput.bindAt task.worldInput packet same basis)
    worldCurrent := task.worldCurrent.map fun witness => ⟨by
      intro next supplied
      cases (Option.some.inj supplied).symm
      exact TaskInput.bindAt_worldAt task.worldInput packet same basis _ _ witness.down⟩ }

theorem Task.withOriginAt_packet (basis : FutureOrigin packet) :
    (task.withOriginAt packet same basis).worldInput.map TaskInput.packet = some packet :=
  congrArg some (TaskInput.bindAt_packet task.worldInput packet same basis)

theorem Task.withOriginAt_origin (basis : FutureOrigin packet) :
    (task.withOriginAt packet same basis).originAt packet
      (task.withOriginAt_packet packet same basis) = some basis :=
  TaskInput.bindAt_origin task.worldInput packet same basis

def Task.withOptionalOriginAt (basis : Option (FutureOrigin packet)) :
    Task (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument) :=
  { task with
    worldInput := match basis with
      | none => task.worldInput
      | some origin => (task.withOriginAt packet same origin).worldInput
    worldCurrent := by
      cases basis with
      | none => exact task.worldCurrent
      | some origin => exact (task.withOriginAt packet same origin).worldCurrent }

theorem Task.withOptionalOriginAt_packet (basis : Option (FutureOrigin packet)) :
    (task.withOptionalOriginAt packet same basis).worldInput.map TaskInput.packet = some packet := by
  cases basis with
  | none => exact same
  | some origin => exact task.withOriginAt_packet packet same origin

end Computation.Search.Segmented.Publication.Learning.Paid.Owned
end SaturationMonoid.ProcessGame.Society.PublicFunction

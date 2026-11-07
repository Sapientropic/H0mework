import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Release
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Geometry
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeThread
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term

open Source.Program PublicFunction PublicFunction.Mandate ResponsibilityLifecycle
open OutstandingSource.History.NativeService

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "Inputs" => List (RawEvent Party Good Port (State Party Technology) Instrument)

def target (bound : BoundSource base scope) (past suffix : Inputs) :=
  OutstandingSource.History.currentAt bound.source (past ++ suffix) ((past ++ suffix).length + 2)

def serviceThread (bound : BoundSource base scope) (past suffix : Inputs) (slot : bound.source.Slot) :=
  (Thread.initial bound.source (originInputs := past) slot).extend bound.source suffix

def originalInventory (bound : BoundSource base scope) (past suffix : Inputs) :=
  (List.range ((past ++ suffix).length + 1)).flatMap fun ordinal =>
    let actual := OutstandingSource.History.actualExecution bound.source (past ++ suffix) ordinal
    if actual.after.clock ≤ bound.source.seed.task.deadline then actual.interpreted.items else []

def serviceGeometry (bound : BoundSource base scope) (past suffix : Inputs) :=
  geometryOf bound.source.seed.law bound.source.seed.task (originalInventory bound past suffix)

structure PaidAt (bound : BoundSource base scope) (past suffix : Inputs) : Prop where
  slots : ∀ slot, (serviceThread bound past suffix slot).state.current.TerminalAt 0
  distinctDebits :
    (serviceGeometry bound past suffix).maximumMatchingCapacity = (serviceGeometry bound past suffix).leftCarrier.card
  closed : (target bound past suffix).technology.holder = none ∧ (target bound past suffix).technology.offered = none
  next : (OutstandingSource.History.actualExecution bound.source (past ++ suffix)
    (past ++ suffix).length).after = target bound past suffix

inductive Issue (bound : BoundSource base scope) (past suffix : Inputs)
  | service (slot : bound.source.Slot) (live : (serviceThread bound past suffix slot).state.current.LiveAt 0)
  | overlap
      (short : (serviceGeometry bound past suffix).maximumMatchingCapacity < (serviceGeometry bound past suffix).leftCarrier.card)
  | authority (active : ¬ ((target bound past suffix).technology.holder = none ∧
      (target bound past suffix).technology.offered = none))

inductive Decision (bound : BoundSource base scope) (past suffix : Inputs)
  | paid (complete : PaidAt bound past suffix)
  | blocked (issue : Issue bound past suffix)

/-- Check the same admitted service threads and original physical suffix.
A still-live mandate or a shared-service shortfall remains on that cut. -/
def decide (bound : BoundSource base scope) (past suffix : Inputs) : Decision bound past suffix :=
  let combined := past ++ suffix
  let archive := (frameAt bound.source combined (combined.length + 2)).payments
  match Material.inspectList (fun slot : bound.source.Slot => (archive slot).isSome = true)
      (List.finRange bound.source.seed.task.slots.length) with
  | .failure slot _ failed =>
      .blocked (.service slot (((serviceThread bound past suffix slot).native_live_iff_unpaid bound.source).mpr
        (by cases actual : archive slot with
            | none => exact actual
            | some _ => exact (failed (by rw [actual]; rfl)).elim)))
  | .clear paid =>
      let geometry := serviceGeometry bound past suffix
      if overlap : geometry.maximumMatchingCapacity < geometry.leftCarrier.card then
        .blocked (.overlap overlap)
      else if inactive : (target bound past suffix).technology.holder = none ∧
          (target bound past suffix).technology.offered = none then
        .paid {
          slots := fun slot => ((serviceThread bound past suffix slot).native_terminal_iff_recorded bound.source).mpr
            (by cases actual : archive slot with
                | none => have found := paid slot (List.mem_finRange slot); rw [actual] at found; cases found
                | some ordinal => exact ⟨ordinal, actual⟩)
          distinctDebits := le_antisymm geometry.maximumMatchingCapacity_le_left (le_of_not_gt overlap)
          closed := inactive
          next := OutstandingSource.History.actual_next bound.source combined _ }
      else .blocked (.authority inactive)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Term

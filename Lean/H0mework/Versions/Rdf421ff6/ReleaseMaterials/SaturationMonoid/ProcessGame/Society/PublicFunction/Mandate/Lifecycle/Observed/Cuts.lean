import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {currentAt : Nat → RawCurrent Party Good (State Party Technology) Instrument}
  {wordAt : Nat → RawEvent Party Good Port (State Party Technology) Instrument}
  {birth : Nat} {grant : Grant base scope (currentAt birth) (wordAt birth)}

def History.consumeRun (history : History base scope currentAt wordAt birth grant)
    (visit : Nat) (item : {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)}) :
    (process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant)).Run
      history.state (history.consume visit item).state := by
  unfold History.consume
  cases readEvent history.obligation history.origin visit item with
  | none => exact .nil
  | some event => exact .step .nil (history.edge event)

private def consumeManyRun (history : History base scope currentAt wordAt birth grant)
    (visit : Nat) (items : List {item // item ∈ (law base scope).rawItems (currentAt visit) (wordAt visit)}) :
    (process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant)).Run
      history.state (items.foldl (fun prior item => prior.consume visit item) history).state := by
  induction items generalizing history with
  | nil => exact .nil
  | cons item rest ih =>
      exact (history.consumeRun visit item).concatRuns _ (ih (history.consume visit item))

def History.visitRun (history : History base scope currentAt wordAt birth grant) (visit : Nat) :
    (process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant)).Run
      history.state (history.visit visit).state :=
  consumeManyRun history visit _

def fromActualCut (start later : Nat) :
    (process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant)).Run
      (through (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
        (birth := birth) (grant := grant) start).state
      (through (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
        (birth := birth) (grant := grant) (start + later)).state := by
  induction later with
  | zero => exact .nil
  | succ later ih =>
      have next := (through (base := base) (scope := scope) (currentAt := currentAt)
        (wordAt := wordAt) (birth := birth) (grant := grant) (start + later)).visitRun (start + later + 1)
      rw [through_succ] at next
      exact ih.concatRuns _ next

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed

import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Transport

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Release

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {currentAt : Nat → RawCurrent Party Good (State Party Technology) Instrument}
  {wordAt : Nat → RawEvent Party Good Port (State Party Technology) Instrument}
  {birth : Nat} {grant : Grant base scope (currentAt birth) (wordAt birth)}

abbrev items (visit : Nat) := ((law base scope).rawItems (currentAt visit) (wordAt visit)).attach

def isRelease {obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))}
    (event : Event base scope currentAt wordAt birth grant obligation) : Bool :=
  match event.disposition with
  | .bearerRelease _ => true
  | .carry _ | .terminal _ => false

abbrev before (history : History base scope currentAt wordAt birth grant) (visit : Nat)
    (index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length) :=
  history.visitPrefix visit index.val

structure Receipt (history : History base scope currentAt wordAt birth grant) (visit : Nat)
    (index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length) where
  private mk ::
  event : Event base scope currentAt wordAt birth grant (before history visit index).obligation
  actual : readEvent (before history visit index).obligation (before history visit index).origin visit
    ((items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index) = some event
  released : isRelease event = true

def read (history : History base scope currentAt wordAt birth grant) (visit : Nat)
    (index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length) :
    Option (Receipt history visit index) :=
  match actual : readEvent (before history visit index).obligation (before history visit index).origin visit
      ((items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index) with
  | none => none
  | some event => if released : isRelease event = true then some ⟨event, actual, released⟩ else none

def Receipt.crossing {history : History base scope currentAt wordAt birth grant} {visit : Nat}
    {index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length}
    (receipt : Receipt history visit index) :
    (process (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) (birth := birth) (grant := grant)).Run
      (before history visit index).state ((before history visit index).cross receipt.event).state :=
  .step .nil ((before history visit index).edge receipt.event)

theorem Receipt.is_the_actual_consumption {history : History base scope currentAt wordAt birth grant} {visit : Nat}
    {index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length}
    (receipt : Receipt history visit index) :
    (before history visit index).consume visit
      ((items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).get index) =
      (before history visit index).cross receipt.event := by
  simp only [History.consume, receipt.actual]

theorem Receipt.accepted_command_source {history : History base scope currentAt wordAt birth grant} {visit : Nat}
    {index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length}
    (receipt : Receipt history visit index) :
    (match receipt.event.evidence with
      | .command .. => True
      | .handoff .. | .refused .. => False) := by
  rcases receipt with ⟨event, actual, released⟩
  rcases event with ⟨accepted⟩ | ⟨refusal⟩
  · rcases accepted with ⟨visit, actual, later, kind, origin⟩ | ⟨visit, next, later, origin⟩
    · trivial
    · cases released
  · cases released

theorem Receipt.native_kind {history : History base scope currentAt wordAt birth grant} {visit : Nat}
    {index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length}
    (receipt : Receipt history visit index) :
    (((before history visit index).edge receipt.event).lifecycleEvent).kind = .bearerRelease := by
  have released := receipt.released
  unfold isRelease at released
  cases disposition : receipt.event.disposition with
  | carry carry => rw [disposition] at released; cases released
  | terminal terminal => rw [disposition] at released; cases released
  | bearerRelease release =>
      simp only [History.edge, NativeResponsibilityProcess.Edge.lifecycleEvent, process]
      rw [disposition]
      rfl

theorem Receipt.keeps_the_original_live_responsibility {history : History base scope currentAt wordAt birth grant} {visit : Nat}
    {index : Fin (items (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt) visit).length}
    (receipt : Receipt history visit index) :
    ((before history visit index).cross receipt.event).state.LiveAt 0 ∧
    HEq ((before history visit index).cross receipt.event).obligation.admission
      (original base scope currentAt wordAt birth grant).admission :=
  ⟨History.responsibility_remains_live _, History.original_admission _⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Release

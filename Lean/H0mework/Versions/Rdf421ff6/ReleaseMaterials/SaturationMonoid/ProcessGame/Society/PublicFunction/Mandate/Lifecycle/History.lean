import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle

open Institutions.Capitalism.Universal.Source.Program ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : RawLaw Party Good Port Technology Instrument)
  (scope : Scope (Party := Party) (Good := Good) (Port := Port))
  (currentAt : Nat → RawCurrent Party Good (State Party Technology) Instrument)
  (wordAt : Nat → RawEvent Party Good Port (State Party Technology) Instrument)
  (birth : Nat) (grant : Grant base scope (currentAt birth) (wordAt birth))

abbrev initialState := (admitGrant base scope _ _ grant).native.target

/-- The full dependent Run retains each actual command or two-signature
handoff. Its history alone is deliberately not the installed payload. -/
structure History where
  private mk ::
  obligation : AdmittedObligation (vocabulary (Party := Party) (Port := Port))
  origin : obligation = {original base scope currentAt wordAt birth grant with bearer := obligation.bearer}
  state : ResponsibilityState (vocabulary (Party := Party) (Port := Port))
  slots : state.slots = [.live obligation]
  generated : (process (base := base) (scope := scope) (currentAt := currentAt)
    (wordAt := wordAt) (birth := birth) (grant := grant)).Run
    (initialState base scope currentAt wordAt birth grant) state

variable {base scope currentAt wordAt birth grant}

def initial : History base scope currentAt wordAt birth grant :=
  ⟨original base scope currentAt wordAt birth grant, rfl,
    initialState base scope currentAt wordAt birth grant, rfl, .nil⟩

def History.slot (history : History base scope currentAt wordAt birth grant) :
    Fin history.state.slots.length :=
  ⟨0, by rw [history.slots]; exact Nat.zero_lt_succ 0⟩

theorem History.present (history : History base scope currentAt wordAt birth grant) :
    history.state.slots.get history.slot = .live history.obligation := by
  simp [History.slot, history.slots]

def History.edge (history : History base scope currentAt wordAt birth grant)
    (event : Event base scope currentAt wordAt birth grant history.obligation) :=
  NativeResponsibilityProcess.Edge.cross
    (P := process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant))
    history.slot history.obligation history.present event

def History.cross (history : History base scope currentAt wordAt birth grant)
    (event : Event base scope currentAt wordAt birth grant history.obligation) :
    History base scope currentAt wordAt birth grant where
  obligation := event.next
  origin := event.next_origin
  state := (history.edge event).target
  slots := by
    change history.state.slots.set history.slot event.disposition.targetSlot = _
    rw [event.target_is_live]
    simp [History.slot, history.slots]
  generated := .step history.generated (history.edge event)

def History.consume (history : History base scope currentAt wordAt birth grant)
    (visit : Nat) (actual : ActualCommand base scope (currentAt visit) (wordAt visit)) :
    History base scope currentAt wordAt birth grant :=
  match readEvent history.obligation history.origin visit actual with
  | none => history
  | some event => history.cross event

def History.visit (history : History base scope currentAt wordAt birth grant) (visit : Nat) :
    History base scope currentAt wordAt birth grant :=
  (commandsAt base scope (currentAt visit) (wordAt visit)).foldl
    (fun prior actual => prior.consume visit actual) history

/-- Only the observed finite prefix is consumed, in source order. Later
visits are not evaluated or stored as a successful future. -/
def through (last : Nat) : History base scope currentAt wordAt birth grant :=
  (List.range (last + 1)).foldl (fun history visit => history.visit visit) initial

theorem through_succ (last : Nat) :
    (through (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
      (birth := birth) (grant := grant) last).visit (last + 1) = through (last + 1) := by
  simp only [through, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem History.original_admission (history : History base scope currentAt wordAt birth grant) :
    HEq history.obligation.admission (original base scope currentAt wordAt birth grant).admission := by
  rw [history.origin]

theorem History.original_scope_lineage_incidence (history : History base scope currentAt wordAt birth grant) :
    history.obligation.scope = scope.service ∧
    history.obligation.lineage = (original base scope currentAt wordAt birth grant).lineage ∧
    history.obligation.sourceIncidence = (original base scope currentAt wordAt birth grant).sourceIncidence := by
  rw [history.origin]
  exact ⟨rfl, rfl, rfl⟩

theorem History.responsibility_remains_live (history : History base scope currentAt wordAt birth grant) :
    history.state.LiveAt 0 := by
  refine ⟨history.obligation, ?_⟩
  rw [history.slots]
  rfl

theorem through_keeps_original_responsibility (last : Nat) :
    (through (base := base) (scope := scope) (currentAt := currentAt) (wordAt := wordAt)
      (birth := birth) (grant := grant) last).state.LiveAt 0 :=
  History.responsibility_remains_live _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle

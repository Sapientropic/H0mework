import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.Quorum
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RootConsumer
import Mathlib.Data.Finset.Union

/-! Source-generated exposure budgets for the paid local-observation protocol.
Every counted key has an actual change of control, admission, communication
resources or observed signal. This is a budget for this source interpreter;
arbitrary application payload signing is a separate protocol responsibility. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceExposure

open Distributed Institutions.Capitalism.Universal.Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

structure CapabilityData (Actor Signal : Type) where
  controller : Actor
  directPermission : Bool
  affordable : List Bool
  observed : Signal
  deriving DecidableEq

abbrev Capability := CapabilityData Party (Fin code.signals)

variable (ports : Fin code.sites → Port)

def capability (current : RawCurrent Party Good Technology Instrument) (key : Fin code.sites) : Capability code :=
  ⟨code.law.controller current.technology (ports key),
    code.law.allowed current.technology (ports key) (code.siteParty key),
    (List.finRange code.sites).map fun recipient => decide
      (∀ item ∈ code.law.rawItems current (code.sendCost key recipient),
        code.law.Valid item.before item.request),
    code.readLocal key (code.snapshot key current)⟩

variable (policy : code.Policy) (initial : RawCurrent Party Good Technology Instrument)

def currentAt (events : List (Event Party Good Port Technology Instrument code.sites)) (n : Nat) :=
  code.rawAt initial (frameAt code policy initial events n)

def viewAt (events : List (Event Party Good Port Technology Instrument code.sites))
    (n : Nat) (key : Fin code.sites) := capability code ports (currentAt code policy initial events n) key

def impactAt (events : List (Event Party Good Port Technology Instrument code.sites))
    (n : Nat) : Finset (Fin code.sites) :=
  Finset.univ.filter fun key => viewAt code ports policy initial events n key ≠
    viewAt code ports policy initial events (n + 1) key

def affectedThrough (events : List (Event Party Good Port Technology Instrument code.sites))
    (count : Nat) : Finset (Fin code.sites) :=
  (Finset.range count).biUnion (impactAt code ports policy initial events)

def budget (events : List (Event Party Good Port Technology Instrument code.sites)) (count : Nat) : Nat :=
  (affectedThrough code ports policy initial events count).card

theorem affected_iff_actual_change
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (count : Nat) (key : Fin code.sites) :
    key ∈ affectedThrough code ports policy initial events count ↔
      ∃ n < count, viewAt code ports policy initial events n key ≠
        viewAt code ports policy initial events (n + 1) key := by
  simp [affectedThrough, impactAt]

theorem unaffected_view_is_constant
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (count : Nat) (key : Fin code.sites)
    (unaffected : key ∉ affectedThrough code ports policy initial events count)
    (n : Nat) (bounded : n ≤ count) :
    viewAt code ports policy initial events n key = viewAt code ports policy initial events 0 key := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have unchanged : viewAt code ports policy initial events n key =
        viewAt code ports policy initial events (n + 1) key := by
      by_contra different
      exact unaffected ((affected_iff_actual_change code ports policy initial events count key).mpr
        ⟨n, by omega, different⟩)
    exact unchanged.symm.trans (ih (by omega))

theorem frameAt_successor
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (n : Nat) (event : Event Party Good Port Technology Instrument code.sites)
    (actual : events[n]? = some event) :
    frameAt code policy initial events (n + 1) = code.step policy initial
      (frameAt code policy initial events n) event := by
  unfold frameAt Code.replay
  rw [List.take_add_one, actual]
  simp only [Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

structure AttemptData (Current Request : Type) where
  before : Current
  request : Request
  admitted : Bool
  after : Current

abbrev Attempt := AttemptData (RawCurrent Party Good Technology Instrument)
  (Request Party Good Port Technology Instrument)

def attemptAt (events : List (Event Party Good Port Technology Instrument code.sites))
    (n : Nat) : Option (Attempt (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :=
  match events[n]? with
  | some (.adversary request) =>
      let before := currentAt code policy initial events n
      some ⟨before, request, decide (code.law.Valid before request), code.law.step before request⟩
  | _ => none

theorem actual_attempt_has_exact_effect
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (n : Nat) (request : Request Party Good Port Technology Instrument)
    (actual : events[n]? = some (.adversary request)) :
    attemptAt code policy initial events n = some
      ⟨currentAt code policy initial events n, request,
        decide (code.law.Valid (currentAt code policy initial events n) request),
        currentAt code policy initial events (n + 1)⟩ := by
  have effect : currentAt code policy initial events (n + 1) =
      code.law.step (currentAt code policy initial events n) request := by
    unfold currentAt
    rw [frameAt_successor code policy initial events n (.adversary request) actual]
    exact code.adversary_attempt_has_exact_raw_effect policy initial _ request
  simp only [attemptAt, actual, effect]

theorem refused_attempt_is_retained_without_capability_change
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (n : Nat) (request : Request Party Good Port Technology Instrument)
    (actual : events[n]? = some (.adversary request))
    (refused : ¬ code.law.Valid (currentAt code policy initial events n) request) :
    (frameAt code policy initial events (n + 1)).word =
        (frameAt code policy initial events n).word ++ [request] ∧
      currentAt code policy initial events (n + 1) = currentAt code policy initial events n ∧
      impactAt code ports policy initial events n = ∅ := by
  have effects := code.invalid_adversary_attempt_is_retained_but_has_no_material_effect
    policy initial (frameAt code policy initial events n) request refused
  have next := frameAt_successor code policy initial events n (.adversary request) actual
  have current : currentAt code policy initial events (n + 1) = currentAt code policy initial events n := by
    simpa only [currentAt, next] using effects.2
  refine ⟨by simpa only [next] using effects.1, current, ?_⟩
  simp only [impactAt, viewAt, current, ne_eq, not_true_eq_false, Finset.filter_false]

theorem authenticated_conflict_is_source_affected
    (interface : Interface code)
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (count : Nat) (one two : Envelope code)
    (auth₁ : verify code interface policy initial events one = true)
    (auth₂ : verify code interface policy initial events two = true)
    (bound₁ : one.occurrence ≤ count) (bound₂ : two.occurrence ≤ count)
    (conflict : Conflicts code one two) :
    one.key ∈ affectedThrough code ports policy initial events count := by
  by_contra unaffected
  have first := (authenticated_origin code interface policy initial events one auth₁).2.1
  have second := (authenticated_origin code interface policy initial events two auth₂).2.1
  have payload₁ : one.payload = (viewAt code ports policy initial events one.occurrence one.key).observed :=
    congrArg EnvelopeData.payload first
  have payload₂ : two.payload = (viewAt code ports policy initial events two.occurrence two.key).observed :=
    congrArg EnvelopeData.payload second
  have same₁ := unaffected_view_is_constant code ports policy initial events count one.key unaffected
    one.occurrence bound₁
  have same₂ := unaffected_view_is_constant code ports policy initial events count one.key unaffected
    two.occurrence bound₂
  have same : one.payload = two.payload := by
    rw [payload₁, payload₂, ← conflict.1, same₁, same₂]
  exact conflict.2.2 same

theorem received_exposure_is_bounded_by_source
    (interface : Interface code)
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (leftSite rightSite : Fin code.sites) (leftInput rightInput : Nat → Option (Envelope code))
    (leftCount rightCount count : Nat) (leftBound : leftCount ≤ count) (rightBound : rightCount ≤ count) :
    Quorum.affected code
      (run code interface policy initial events leftSite leftInput leftCount)
      (run code interface policy initial events rightSite rightInput rightCount) ⊆
      affectedThrough code ports policy initial events count := by
  intro key exposed
  obtain ⟨pair, witness, sameKey⟩ := List.mem_map.mp (List.mem_toFinset.mp exposed)
  obtain ⟨one, two, conflict⟩ := (evidence_iff code _ pair.1 pair.2).mp witness
  have sourceOf : ∀ receipt ∈ (Quorum.merged code
      (run code interface policy initial events leftSite leftInput leftCount)
      (run code interface policy initial events rightSite rightInput rightCount)).receipts,
      verify code interface policy initial events receipt.wire = true ∧ receipt.wire.occurrence ≤ count := by
    intro receipt member
    rcases List.mem_append.mp member with left | right
    · obtain ⟨auth, _, before, bounded, _⟩ :=
        receipts_authenticated code interface policy initial events leftSite leftInput leftCount receipt left
      exact ⟨auth, by omega⟩
    · obtain ⟨auth, _, before, bounded, _⟩ :=
        receipts_authenticated code interface policy initial events rightSite rightInput rightCount receipt right
      exact ⟨auth, by omega⟩
  rw [← sameKey]
  exact authenticated_conflict_is_source_affected code ports policy initial interface events count pair.1.wire pair.2.wire
    (sourceOf pair.1 one).1 (sourceOf pair.2 two).1 (sourceOf pair.1 one).2 (sourceOf pair.2 two).2 conflict

theorem agreement_of_source_generated_budget
    (interface : Interface code)
    (events : List (Event Party Good Port Technology Instrument code.sites))
    (leftSite rightSite : Fin code.sites) (leftInput rightInput : Nat → Option (Envelope code))
    (count threshold : Nat) (scope : Scope) (a b : Fin code.signals)
    (one : Quorum.readout code (run code interface policy initial events leftSite leftInput count)
      scope threshold = .decided a)
    (two : Quorum.readout code (run code interface policy initial events rightSite rightInput count)
      scope threshold = .decided b)
    (enough : code.sites + budget code ports policy initial events count < threshold + threshold) : a = b := by
  have covered := Finset.card_le_card (received_exposure_is_bounded_by_source code ports policy initial
    interface events leftSite rightSite leftInput rightInput count count count (Nat.le_refl _) (Nat.le_refl _))
  apply Quorum.agreement_of_generated_exposure_bound code _ _ scope threshold a b one two
  exact lt_of_le_of_lt (Nat.add_le_add_left covered code.sites) enough

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceExposure

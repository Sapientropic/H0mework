import H0mework.Foundation.Agency.Lineage
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.ThreeAgentH1Face

/-!
# Source-generated ProcessGame reuse across domains

Economic coalition members, biological ancestry individuals and multi-agent
interaction actors are all downstream images of seeds witnessed in one exact
source occurrence trace.  None of these domain identities is a field of the
source-only `ProcessGame` core.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace DomainReuse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u

/-! ## Shared finite event-occurrence helper -/

def eventBranches {Event : Type u} :
    List Event → AccountedBranches Event
  | [] => .nil
  | event :: events =>
      .cons (RootedAccountedUnfolding.zero event) (eventBranches events)

def eventOccurrence {Event : Type u} (origin : Event)
    (events : List Event) : RootedAccountedUnfolding Event :=
  .occur origin (eventBranches events)

@[simp] theorem traceBranches_eventBranches {Event : Type u}
    (events : List Event) :
    RootedAccountedUnfolding.traceBranches (eventBranches events) = events := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      change event ::
        RootedAccountedUnfolding.traceBranches (eventBranches events) =
          event :: events
      rw [ih]

@[simp] theorem eventOccurrence_trace {Event : Type u}
    (origin : Event) (events : List Event) :
    (eventOccurrence origin events).trace = origin :: events := by
  change origin ::
    RootedAccountedUnfolding.traceBranches (eventBranches events) =
      origin :: events
  rw [traceBranches_eventBranches]

/-! ## Economic coalition admission -/

namespace Economic

structure AdmissionEvent where
  candidate : Nat
  deriving DecidableEq, Repr

structure Source where
  admissions : List AdmissionEvent

inductive State where
  | opened
  | admitted (event : AdmissionEvent)
  deriving DecidableEq, Repr

def occurrenceOf (source : Source) : RootedAccountedUnfolding State :=
  eventOccurrence .opened (source.admissions.map State.admitted)

def processGame (source : Source) :
    _root_.SaturationMonoid.ProcessGame occurrenceOf :=
  ⟨source⟩

def seedAt (_source : Source) (state : State)
    (seed : AdmissionEvent) : Prop :=
  state = .admitted seed

def sourceSeed (source : Source) (event : AdmissionEvent)
    (admitted : event ∈ source.admissions) :
    SourceSeed occurrenceOf AdmissionEvent seedAt source :=
  ⟨event, ⟨.admitted event, by
    simp [occurrenceOf, admitted], rfl⟩⟩

theorem sourceSeed_has_exact_admission_witness
    (source : Source) (event : AdmissionEvent)
    (admitted : event ∈ source.admissions) :
    ∃ state ∈ (occurrenceOf source).trace, seedAt source state event :=
  (sourceSeed source event admitted).2

/-- Coalition identity exists only downstream of an admitted source seed. -/
inductive CoalitionLineage (source : Source) where
  | admitted
      (seed : SourceSeed occurrenceOf AdmissionEvent seedAt source)

def lineageOf (source : Source)
    (seed : SourceSeed occurrenceOf AdmissionEvent seedAt source) :
    CoalitionLineage source :=
  .admitted seed

def CoalitionLineage.admission {source : Source} :
    CoalitionLineage source → AdmissionEvent
  | .admitted seed => seed.1

abbrev GeneratedCoalitionMember (source : Source) :=
  GeneratedActor (processGame source) AdmissionEvent seedAt CoalitionLineage
    lineageOf

def GeneratedCoalitionMember.admission {source : Source}
    (member : GeneratedCoalitionMember source) : AdmissionEvent :=
  member.1.admission

def admissionFoldAlgebra (state : State)
    (children : List (List AdmissionEvent)) : List AdmissionEvent :=
  match state with
  | .opened => children.flatten
  | .admitted event => [event]

def admissionFoldReadout (source : Source) :
    FoldReadout (processGame source) admissionFoldAlgebra :=
  foldReadout (processGame source) admissionFoldAlgebra

theorem candidate_eq_admissionFold (source : Source)
    (candidate : RootedAccountedUnfolding State → List AdmissionEvent)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        admissionFoldAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate (processGame source).occurrence =
      (admissionFoldReadout source).value :=
  (admissionFoldReadout source).candidate_eq_value candidate commutes

end Economic

/-! ## Biological division and ancestry -/

namespace Biological

structure DivisionEvent where
  parent : Nat
  child : Nat
  deriving DecidableEq, Repr

structure Source where
  divisions : List DivisionEvent

inductive State where
  | organism
  | divided (event : DivisionEvent)
  deriving DecidableEq, Repr

def occurrenceOf (source : Source) : RootedAccountedUnfolding State :=
  eventOccurrence .organism (source.divisions.map State.divided)

def processGame (source : Source) :
    _root_.SaturationMonoid.ProcessGame occurrenceOf :=
  ⟨source⟩

def seedAt (_source : Source) (state : State)
    (seed : DivisionEvent) : Prop :=
  state = .divided seed

def sourceSeed (source : Source) (event : DivisionEvent)
    (divided : event ∈ source.divisions) :
    SourceSeed occurrenceOf DivisionEvent seedAt source :=
  ⟨event, ⟨.divided event, by
    simp [occurrenceOf, divided], rfl⟩⟩

theorem sourceSeed_has_exact_division_witness
    (source : Source) (event : DivisionEvent)
    (divided : event ∈ source.divisions) :
    ∃ state ∈ (occurrenceOf source).trace, seedAt source state event :=
  (sourceSeed source event divided).2

/-- An ancestry individual is generated from one witnessed division event. -/
inductive AncestryLineage (source : Source) where
  | divided (seed : SourceSeed occurrenceOf DivisionEvent seedAt source)

def lineageOf (source : Source)
    (seed : SourceSeed occurrenceOf DivisionEvent seedAt source) :
    AncestryLineage source :=
  .divided seed

def AncestryLineage.division {source : Source} :
    AncestryLineage source → DivisionEvent
  | .divided seed => seed.1

abbrev GeneratedAncestryIndividual (source : Source) :=
  GeneratedActor (processGame source) DivisionEvent seedAt AncestryLineage
    lineageOf

def GeneratedAncestryIndividual.division {source : Source}
    (individual : GeneratedAncestryIndividual source) : DivisionEvent :=
  individual.1.division

def divisionFoldAlgebra (state : State)
    (children : List (List DivisionEvent)) : List DivisionEvent :=
  match state with
  | .organism => children.flatten
  | .divided event => [event]

def divisionFoldReadout (source : Source) :
    FoldReadout (processGame source) divisionFoldAlgebra :=
  foldReadout (processGame source) divisionFoldAlgebra

theorem candidate_eq_divisionFold (source : Source)
    (candidate : RootedAccountedUnfolding State → List DivisionEvent)
    (commutes : ∀ origin branches,
      candidate (.occur origin branches) =
        divisionFoldAlgebra origin
          (RootedAccountedUnfolding.candidateValues candidate branches)) :
    candidate (processGame source).occurrence =
      (divisionFoldReadout source).value :=
  (divisionFoldReadout source).candidate_eq_value candidate commutes

end Biological

/-! ## Multi-agent reuse of the existing three-agent source -/

namespace MultiAgent

def seedPoint : ThreeCycleTime → ThreeAgentFoldPoint
  | .t0 => .edge01
  | .t1 => .edge12
  | .t2 => .edge20

def seedAt (_source : Unit) (state : ThreeAgentFoldPoint)
    (seed : ThreeCycleTime) : Prop :=
  state = seedPoint seed

def sourceSeed (agent : ThreeCycleTime) :
    SourceSeed threeAgentOccurrenceOf ThreeCycleTime seedAt () := by
  refine ⟨agent, seedPoint agent, ?_, rfl⟩
  cases agent <;>
    simp [threeAgentOccurrenceOf, threeAgentExposure, seedPoint,
      RootedAccountedUnfolding.trace,
      RootedAccountedUnfolding.zero, AccountedBranches.singleton]

theorem sourceSeed_has_exact_exposure_witness (agent : ThreeCycleTime) :
    ∃ state ∈ threeAgentExposure.trace, seedAt () state agent :=
  (sourceSeed agent).2

inductive InteractionLineage (source : Unit) where
  | exposed
      (seed : SourceSeed threeAgentOccurrenceOf ThreeCycleTime seedAt source)

def lineageOf (source : Unit)
    (seed : SourceSeed threeAgentOccurrenceOf ThreeCycleTime seedAt source) :
    InteractionLineage source :=
  .exposed seed

def InteractionLineage.agent {source : Unit} :
    InteractionLineage source → ThreeCycleTime
  | .exposed seed => seed.1

abbrev GeneratedInteractionActor :=
  GeneratedActor threeAgentProcessGame ThreeCycleTime seedAt InteractionLineage
    lineageOf

def GeneratedInteractionActor.agent
    (actor : GeneratedInteractionActor) : ThreeCycleTime :=
  actor.1.agent

end MultiAgent

end DomainReuse
end ProcessGame
end SaturationMonoid

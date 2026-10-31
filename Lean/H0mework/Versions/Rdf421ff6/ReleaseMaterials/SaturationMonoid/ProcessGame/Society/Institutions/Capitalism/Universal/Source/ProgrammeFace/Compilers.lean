import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Trace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Incidence

/-! The original raw instructions generate the existing M0, actual-action
and relation-role compilers.  Permission roles read the actual pre/post rule
state.  Future codes are finite original request ordinals, with source-law
execution witnesses rather than a completed future table. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle.Universal Relations Power Program

universe u

variable {Party Good Port Technology Instrument Index : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (read : Index → Origin Party Good Port Technology Instrument)

def occurrenceOf (index : Index) := trace law (read index)

def SeedAt (index : Index) (point : Point Party Good Port Technology Instrument)
    (party : Party) : Prop :=
  point = .source (read index) ∧ party ∈ parties law (read index)

def actorFace : M0BoundaryFace (occurrenceOf law read) where
  Seed := Party
  Lineage := fun _ => List Party
  SeedAt := SeedAt law read
  lineageOf := fun index seed => actorLineage law (read index) seed.val
  state := fun index => .source (read index)
  seedAt_state := fun _ _ _ active => active.1

def game (index : Index) : SaturationMonoid.ProcessGame (occurrenceOf law read) := ⟨index⟩

abbrev Actor (index : Index) :=
  GeneratedActor (game law read index) (actorFace law read).Seed
    (actorFace law read).SeedAt (actorFace law read).Lineage (actorFace law read).lineageOf

def exactParty (index : Index) (party : Party) (present : party ∈ parties law (read index)) :
    SourceSeed (occurrenceOf law read) Party (SeedAt law read) index :=
  ⟨party, .source (read index), source_mem_trace law (read index), rfl, present⟩

def actor (index : Index) (party : Party) (present : party ∈ parties law (read index)) :
    Actor law read index :=
  generatedActorOf (game law read index) (actorFace law read).Seed
    (actorFace law read).SeedAt (actorFace law read).Lineage (actorFace law read).lineageOf
    (exactParty law read index party present)

theorem actor_distinguishes_original_seeds (index : Index) (first second : Party)
    (firstPresent : first ∈ parties law (read index))
    (secondPresent : second ∈ parties law (read index))
    (same : actor law read index first firstPresent = actor law read index second secondPresent) :
    first = second :=
  actorLineage_distinguishes law (read index) first second firstPresent (congrArg Subtype.val same)

def controllers (index : Index) :
    SourceOwnedActionControllerCompiler (game law read index) (actorFace law read) where
  ActionSeed := ActionSeed Party
  actionAdmittedAt := fun action => action ∈ actions law (read index)
  actionState := fun location => .source (read location)
  actionState_mem := source_mem_trace law (read index)
  actorState_mem := source_mem_trace law (read index)
  actorSeed := ActionSeed.party
  actorSeed_active := fun action admitted =>
    ⟨rfl, action_party_present law (read index) action admitted⟩

def exactAction (index : Index) (action : ActionSeed Party)
    (admitted : action ∈ actions law (read index)) : (controllers law read index).ExactActionSeed :=
  ⟨action, .source (read index), source_mem_trace law (read index), rfl, admitted⟩

def relationSeedAt (index : Index) (point : Point Party Good Port Technology Instrument)
    (seed : Port × Party) : Prop :=
  point = .source (read index) ∧ seed ∈ relationIncidences law (read index)

def boundaryRaw (origin : Origin Party Good Port Technology Instrument) : EdgeSide →
    RawCurrent Party Good Technology Instrument
  | .source => origin.1
  | .target => law.next origin.1 origin.2

def boundaryPoint (origin : Origin Party Good Port Technology Instrument) : EdgeSide →
    Point Party Good Port Technology Instrument
  | .source => .source origin
  | .target => .target (law.next origin.1 origin.2)

def permissionRole (current : RawCurrent Party Good Technology Instrument)
    (port : Option Port) : Party → Bool :=
  match port with
  | some port => law.allowed current.technology port
  | none => fun _ => false

abbrev FutureCode := ULift.{u} (Option Nat)

def continuationPredicate (origin : Origin Party Good Port Technology Instrument)
    (lineage : List Port) (side : EdgeSide) (code : FutureCode)
    (item : ExecutionItem Party Good Port Technology Instrument) : Prop :=
  item ∈ law.rawItems origin.1 origin.2 ∧ code.down = some item.index ∧
  (∃ port, lineage.head? = some port ∧
    port ∈ law.requiredPorts (boundaryRaw law origin side) item.request) ∧
  law.Valid (boundaryRaw law origin side) item.request

def ContinuationAt (origin : Origin Party Good Port Technology Instrument)
    (lineage : List Port) (side : EdgeSide) (code : FutureCode) : Type u :=
  Σ item : ExecutionItem Party Good Port Technology Instrument,
    ULift.{u} (PLift (continuationPredicate law origin lineage side code item))

def relations (index : Index) :
    SourceOwnedRelationRoleCompiler (occurrenceOf law read) (game law read index)
      (actorFace law read) where
  RelationSeed := Port × Party
  RelationLineage := fun _ => List Port
  relationSeedAt := relationSeedAt law read
  relationLineageOf := fun location seed => relationLineage law (read location) seed.val.1
  beneficiaryActorSeed := Prod.snd
  beneficiaryActor_active := fun location _ seed active =>
    ⟨active.1, relation_party_present law (read location) seed active.2⟩
  Role := fun _ => Party → Bool
  Phase := fun _ => Option Port × RawCurrent Party Good Technology Instrument
  sourceRoleOf := fun location lineage => permissionRole law (read location).1 lineage.head?
  phaseStepOf := fun location lineage => (lineage.head?, law.next (read location).1 (read location).2)
  advanceRole := fun _ phase _ => permissionRole law phase.2 phase.1
  FutureCode := FutureCode
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier :=
    ((none :: (law.rawItems (read index).1 (read index).2).map (fun item => some item.index)).map
      (fun code => (ULift.up code : FutureCode))).toFinset
  futureIdle := fun code => code.down = none
  FutureContinuationAt := ContinuationAt law (read index)
  futureBoundaryState := fun _ side => boundaryPoint law (read index) side
  futureBoundaryState_mem := fun _ side => by
    cases side
    · exact source_mem_trace law (read index)
    · exact target_mem_trace law (read index)
  FutureContinuationWitnessAt := fun lineage side code continuation =>
    continuationPredicate law (read index) lineage side code continuation.1
  futureContinuation_witnessed := fun _ _ _ continuation => continuation.2.down.down

def exactRelation (index : Index) (seed : Port × Party)
    (admitted : seed ∈ relationIncidences law (read index)) :
    (relations law read index).ExactRelationSeed :=
  ⟨seed, .source (read index), source_mem_trace law (read index), rfl, admitted⟩

/-- Local participation readout.  This face does not supply identity across
occurrences; the authoritative reader uses the original genesis anchors. -/
def localParticipationFace
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V)
    (raw : OriginalOccurrence source → Origin Party Good Port Technology Instrument) :
    ExistingSocietyFace source where
  State := Point Party Good Port Technology Instrument
  traceOf := occurrenceOf law raw
  actorFace := actorFace law raw
  controllersAt := controllers law raw
  relationsAt := relations law raw
  actionEquality := fun _ => inferInstanceAs (DecidableEq (ActionSeed Party))
  lineageEquality := fun _ => inferInstanceAs (DecidableEq (List Party))
  relationEquality := fun _ => inferInstanceAs (DecidableEq (List Port))

#print axioms actor_distinguishes_original_seeds
#print axioms localParticipationFace

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace

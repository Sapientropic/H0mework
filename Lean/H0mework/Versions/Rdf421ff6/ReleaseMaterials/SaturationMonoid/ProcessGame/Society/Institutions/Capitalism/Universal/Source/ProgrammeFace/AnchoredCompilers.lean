import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Compilers

/-!
The registered programme's keys resolve to seeds of its original genesis
occurrence.  Later participation is an image of those exact seeds, not a
fresh image of equal display names.  A previously unregistered key has no
actor or relation in this face and must enter through native admission.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Anchored

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle.Universal Relations Power Program

universe u

variable {Party Good Port Technology Instrument Index : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (read : Index → Origin Party Good Port Technology Instrument) (birth : Index)

abbrev BirthSeed := SourceSeed (occurrenceOf law read) Party (SeedAt law read) birth
abbrev BirthActor := ProgrammeFace.Actor law read birth

def bornActor (seed : BirthSeed law read birth) : BirthActor law read birth :=
  generatedActorOf (game law read birth) (ProgrammeFace.actorFace law read).Seed
    (ProgrammeFace.actorFace law read).SeedAt (ProgrammeFace.actorFace law read).Lineage
    (ProgrammeFace.actorFace law read).lineageOf seed

def actorActive (index : Index) (point : Point Party Good Port Technology Instrument)
    (seed : BirthSeed law read birth) : Prop :=
  point = .source (read index) ∧ seed.val ∈ parties law (read index)

def actorFace : M0BoundaryFace (occurrenceOf law read) where
  Seed := BirthSeed law read birth
  Lineage := fun _ => BirthActor law read birth
  SeedAt := actorActive law read birth
  lineageOf := fun _ seed => bornActor law read birth seed.val
  state := fun index => .source (read index)
  seedAt_state := fun _ _ _ active => active.1

abbrev Actor (index : Index) :=
  GeneratedActor (game law read index) (actorFace law read birth).Seed
    (actorFace law read birth).SeedAt (actorFace law read birth).Lineage
    (actorFace law read birth).lineageOf

def exactParty (index : Index) (seed : BirthSeed law read birth)
    (present : seed.val ∈ parties law (read index)) :
    SourceSeed (occurrenceOf law read) (BirthSeed law read birth)
      (actorActive law read birth) index :=
  ⟨seed, .source (read index), source_mem_trace law (read index), rfl, present⟩

def actor (index : Index) (seed : BirthSeed law read birth)
    (present : seed.val ∈ parties law (read index)) : Actor law read birth index :=
  generatedActorOf (game law read index) (actorFace law read birth).Seed
    (actorFace law read birth).SeedAt (actorFace law read birth).Lineage
    (actorFace law read birth).lineageOf (exactParty law read birth index seed present)

theorem actor_has_original_birth (index : Index) (actor : Actor law read birth index) :
    ∃ seed : BirthSeed law read birth, actor.val = bornActor law read birth seed := by
  obtain ⟨seed, generated⟩ := actor.property
  exact ⟨seed.val, generated⟩

theorem same_original_birth_at_two_occurrences
    (first second : Index) (seed : BirthSeed law read birth)
    (firstPresent : seed.val ∈ parties law (read first))
    (secondPresent : seed.val ∈ parties law (read second)) :
    (actor law read birth first seed firstPresent).val =
      (actor law read birth second seed secondPresent).val := rfl

abbrev RegisteredAction :=
  { action : ActionSeed Party // action.party ∈ parties law (read birth) }

def controllers (index : Index) :
    SourceOwnedActionControllerCompiler (game law read index) (actorFace law read birth) where
  ActionSeed := RegisteredAction law read birth
  actionAdmittedAt := fun action => action.val ∈ actions law (read index)
  actionState := fun location => .source (read location)
  actionState_mem := source_mem_trace law (read index)
  actorState_mem := source_mem_trace law (read index)
  actorSeed := fun action => ProgrammeFace.exactParty law read birth action.val.party action.property
  actorSeed_active := fun action admitted =>
    ⟨rfl, action_party_present law (read index) action.val admitted⟩

def exactAction (index : Index) (action : ActionSeed Party)
    (born : action.party ∈ parties law (read birth))
    (admitted : action ∈ actions law (read index)) :
    (controllers law read birth index).ExactActionSeed :=
  ⟨⟨action, born⟩, .source (read index), source_mem_trace law (read index), rfl, admitted⟩

abbrev RegisteredRelation :=
  { seed : Port × Party // seed ∈ relationIncidences law (read birth) }

def relationActive (index : Index) (point : Point Party Good Port Technology Instrument)
    (seed : RegisteredRelation law read birth) : Prop :=
  point = .source (read index) ∧ seed.val ∈ relationIncidences law (read index)

abbrev BirthRelation := (ProgrammeFace.relations law read birth).GeneratedRelation

def bornRelation (seed : RegisteredRelation law read birth) : BirthRelation law read birth :=
  (ProgrammeFace.relations law read birth).relationOf
    (ProgrammeFace.exactRelation law read birth seed.val seed.property)

def relations (index : Index) :
    SourceOwnedRelationRoleCompiler (occurrenceOf law read) (game law read index)
      (actorFace law read birth) where
  RelationSeed := RegisteredRelation law read birth
  RelationLineage := fun _ => BirthRelation law read birth
  relationSeedAt := relationActive law read birth
  relationLineageOf := fun _ seed => bornRelation law read birth seed.val
  beneficiaryActorSeed := fun seed => ProgrammeFace.exactParty law read birth seed.val.2
    (relation_party_present law (read birth) seed.val seed.property)
  beneficiaryActor_active := fun location _ seed active =>
    ⟨active.1, relation_party_present law (read location) seed.val active.2⟩
  Role := fun _ => Party → Bool
  Phase := fun _ => Option Port × RawCurrent Party Good Technology Instrument
  sourceRoleOf := fun location lineage => permissionRole law (read location).1 lineage.val.head?
  phaseStepOf := fun location lineage =>
    (lineage.val.head?, law.next (read location).1 (read location).2)
  advanceRole := fun _ phase _ => permissionRole law phase.2 phase.1
  FutureCode := FutureCode
  futureCodeDecidableEq := inferInstance
  futureCodeCarrier :=
    ((none :: (law.rawItems (read index).1 (read index).2).map (fun item => some item.index)).map
      (fun code => (ULift.up code : FutureCode))).toFinset
  futureIdle := fun code => code.down = none
  FutureContinuationAt := fun lineage => ContinuationAt law (read index) lineage.val
  futureBoundaryState := fun _ side => boundaryPoint law (read index) side
  futureBoundaryState_mem := fun _ side => by
    cases side
    · exact source_mem_trace law (read index)
    · exact target_mem_trace law (read index)
  FutureContinuationWitnessAt := fun lineage side code continuation =>
    continuationPredicate law (read index) lineage.val side code continuation.1
  futureContinuation_witnessed := fun _ _ _ continuation => continuation.2.down.down

def exactRelation (index : Index) (seed : Port × Party)
    (born : seed ∈ relationIncidences law (read birth))
    (admitted : seed ∈ relationIncidences law (read index)) :
    (relations law read birth index).ExactRelationSeed :=
  ⟨⟨seed, born⟩, .source (read index), source_mem_trace law (read index), rfl, admitted⟩

def society
    {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V)
    (raw : OriginalOccurrence source → Origin Party Good Port Technology Instrument)
    (genesis : OriginalOccurrence source) : ExistingSocietyFace source where
  State := Point Party Good Port Technology Instrument
  traceOf := occurrenceOf law raw
  actorFace := actorFace law raw genesis
  controllersAt := controllers law raw genesis
  relationsAt := relations law raw genesis
  actionEquality := fun _ => inferInstanceAs (DecidableEq (RegisteredAction law raw genesis))
  lineageEquality := fun _ left right =>
    match (inferInstance : DecidableEq (List Party)) left.val right.val with
    | isTrue same => isTrue (Subtype.ext same)
    | isFalse different => isFalse (fun equal => different (congrArg Subtype.val equal))
  relationEquality := fun _ left right =>
    match (inferInstance : DecidableEq (List Port)) left.val right.val with
    | isTrue same => isTrue (Subtype.ext same)
    | isFalse different => isFalse (fun equal => different (congrArg Subtype.val equal))

#print axioms actor_has_original_birth
#print axioms society

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Anchored

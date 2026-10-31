import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.AnchoredCompilers
import H0mework.Foundation.Agency.LifecycleSeeds

/-! The two boundary states are a restriction of the same raw programme
event.  Its grammar can alter material, claims and permissions, but does not
erase the origin token of a participant.  Identity is therefore transported
from the actual genesis seed by the existing lifecycle core. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Anchored

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle.Universal Relations Power Program

universe u

variable {Party Good Port Technology Instrument Index : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (read : Index → Origin Party Good Port Technology Instrument) (birth : Index)

def boundaryOccurrence (index : Index) :
    RootedAccountedUnfolding (Point Party Good Port Technology Instrument) :=
  .occur (boundaryPoint law (read index) .source)
    (.cons (.zero (boundaryPoint law (read index) .target)) .nil)

def boundaryGame (index : Index) : SaturationMonoid.ProcessGame (boundaryOccurrence law read) :=
  ⟨index⟩

theorem boundary_is_original_trace_restriction (index : Index) :
    List.Sublist (boundaryOccurrence law read index).trace (occurrenceOf law read index).trace := by
  change List.Sublist [Point.source (read index), Point.target (law.next (read index).1 (read index).2)]
    (trace law (read index)).trace
  rw [trace_exact]
  apply List.cons_sublist_cons.mpr
  apply List.singleton_sublist.mpr
  exact List.mem_append_right _ List.mem_cons_self

def boundaryActive (side : EdgeSide) (index : Index)
    (point : Point Party Good Port Technology Instrument) (seed : BirthSeed law read birth) : Prop :=
  point = boundaryPoint law (read index) side ∧ seed.val ∈ parties law (read index)

def boundaryFace (side : EdgeSide) : M0BoundaryFace (boundaryOccurrence law read) where
  Seed := BirthSeed law read birth
  Lineage := fun _ => BirthActor law read birth
  SeedAt := boundaryActive law read birth side
  lineageOf := fun _ seed => bornActor law read birth seed.val
  state := fun index => boundaryPoint law (read index) side
  seedAt_state := fun _ _ _ active => active.1

def lifecycle (index : Index) :
    SourceOwnedLifecycleCore (boundaryOccurrence law read) (boundaryGame law read index) where
  sourceFace := boundaryFace law read birth .source
  targetFace := boundaryFace law read birth .target
  HistorySeed := PEmpty
  HistoryLineage := fun _ => PEmpty
  historySeedAt := fun _ _ seed => seed.elim
  historyLineageOf := fun _ seed => seed.val.elim
  LinkSeed := BirthSeed law read birth
  linkAdmittedAt := fun seed => seed.val ∈ parties law (read index)
  linkSource := id
  linkTarget := id
  linkSource_active := fun _ admitted => ⟨rfl, admitted⟩
  linkTarget_active := fun _ admitted => ⟨rfl, admitted⟩
  IdentitySeed := BirthSeed law read birth
  identityAdmittedAt := fun seed => seed.val ∈ parties law (read index)
  identitySource := id
  identityTarget := id
  identitySource_active := fun _ admitted => ⟨rfl, admitted⟩
  identityTarget_active := fun _ admitted => ⟨rfl, admitted⟩
  ExitSeed := PEmpty
  exitAdmittedAt := fun impossible => impossible.elim
  exitSource := PEmpty.elim
  exitSource_active := fun impossible => impossible.elim
  FreshSeed := PEmpty
  freshAdmittedAt := fun impossible => impossible.elim
  freshTarget := PEmpty.elim
  freshTarget_active := fun impossible => impossible.elim
  ReappearanceSeed := PEmpty
  reappearanceAdmittedAt := fun impossible => impossible.elim
  reappearanceHistory := PEmpty.elim
  reappearanceHistoryState := PEmpty.elim
  reappearanceHistory_active := fun impossible => impossible.elim
  reappearanceTarget := PEmpty.elim
  reappearanceTarget_active := fun impossible => impossible.elim
  sourceIndex := 0
  source_state_mem := List.mem_cons_self
  target_state_mem := by exact List.mem_cons_of_mem _ List.mem_cons_self
  source_at_index := rfl
  target_follows_source := rfl
  history_before_event := fun _ impossible => impossible.elim

def identitySeed (index : Index) (seed : BirthSeed law read birth)
    (present : seed.val ∈ parties law (read index)) :
    (lifecycle law read birth index).ExactIdentitySeed :=
  ⟨seed, _, (lifecycle law read birth index).target_state_mem, rfl, present⟩

def identityTransport (index : Index) (seed : BirthSeed law read birth)
    (present : seed.val ∈ parties law (read index)) :
    (lifecycle law read birth index).DomainIdentityTransportAt
      ((identitySeed law read birth index seed present).sourceActor
        (lifecycle law read birth index))
      ((identitySeed law read birth index seed present).targetActor
        (lifecycle law read birth index)) :=
  ⟨identitySeed law read birth index seed present, rfl, rfl⟩

def sourceRestrictionSeed (index : Index)
    (seed : SourceSeed (boundaryOccurrence law read) (BirthSeed law read birth)
      (boundaryActive law read birth .source) index) :
    SourceSeed (occurrenceOf law read) (BirthSeed law read birth)
      (actorActive law read birth) index := by
  refine ⟨seed.val, ?_⟩
  rcases seed.property with ⟨point, member, active⟩
  exact ⟨point, (boundary_is_original_trace_restriction law read index).subset member, active⟩

theorem identity_seed_is_original_source_seed (index : Index) (seed : BirthSeed law read birth)
    (present : seed.val ∈ parties law (read index)) :
    sourceRestrictionSeed law read birth index
      ((identitySeed law read birth index seed present).sourceSeed (lifecycle law read birth index)) =
      exactParty law read birth index seed present := Subtype.ext rfl

theorem identity_carries_original_birth (index : Index) (seed : BirthSeed law read birth)
    (present : seed.val ∈ parties law (read index)) :
    ((identitySeed law read birth index seed present).sourceActor
        (lifecycle law read birth index)).val = bornActor law read birth seed ∧
    ((identitySeed law read birth index seed present).targetActor
        (lifecycle law read birth index)).val = bornActor law read birth seed := ⟨rfl, rfl⟩

theorem identity_agrees_with_actual_actor (index : Index) (seed : BirthSeed law read birth)
    (present : seed.val ∈ parties law (read index)) :
    ((identitySeed law read birth index seed present).sourceActor
        (lifecycle law read birth index)).val = (actor law read birth index seed present).val := rfl

#print axioms identityTransport

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Anchored

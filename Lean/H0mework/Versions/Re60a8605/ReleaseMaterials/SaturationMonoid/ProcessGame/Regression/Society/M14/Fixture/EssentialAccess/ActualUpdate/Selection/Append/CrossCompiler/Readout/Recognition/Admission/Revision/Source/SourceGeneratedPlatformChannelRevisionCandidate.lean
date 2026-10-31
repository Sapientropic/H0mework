import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Source.SourceGeneratedCycleMemoryPlatformGateObstruction

/-!
# Source-generated platform-channel revision candidate

The exact platform cycle-memory obstruction generates one right-summand gate
over the existing paid essential-access carrier.  This file creates only the
candidate channel vocabulary and its preservation/non-reconstruction laws.
It is not a root, ledger, occurrence, U8 core or installed authority; the next
layer must install it through the existing first-row revision.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedPlatformChannelRevisionCandidate

noncomputable section

open M14EssentialAccessRelationFixture
open M14SourceGeneratedActualRelationThreeCycle
open M14SourceGeneratedCycleMemoryPlatformGateObstruction
open M14SourceGeneratedContributionCapacityEssentialAccessChannel

/-- Exact lineage restriction selecting the obstruction's generated platform
seed.  This is not a new gate identity carrier. -/
abbrev SourceGeneratedPlatformChannelGateAt
    {boundary : Nat}
    (obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt
      boundary) :=
  { source : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary //
      source = obstruction } ×
    { seed : essentialAccessRelationCompiler.ExactRelationSeed //
      seed = actualRelationSeedAt (platformCycleBaseAfter boundary) }

def sourceGeneratedPlatformChannelGateAt
    {boundary : Nat}
    (obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt
      boundary) :
    SourceGeneratedPlatformChannelGateAt obstruction :=
  ⟨⟨obstruction, rfl⟩,
    ⟨actualRelationSeedAt (platformCycleBaseAfter boundary), rfl⟩⟩

namespace SourceGeneratedPlatformChannelGateAt

variable {boundary : Nat}
  {obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary}
  (gate : SourceGeneratedPlatformChannelGateAt obstruction)

/-- Exact source seed carried by the witness, not a caller label. -/
def seed : essentialAccessRelationCompiler.ExactRelationSeed := by
  exact gate.2.1

@[simp] theorem source_eq_obstruction : gate.1.1 = obstruction :=
  gate.1.2

def actor := (seed gate).actor essentialAccessRelationCompiler

def relation := essentialAccessRelationCompiler.relationOf (seed gate)

def phase := essentialAccessRelationCompiler.phaseStep (relation gate)

def targetRole := essentialAccessRelationCompiler.roleAt
  (relation gate) .target

@[simp] theorem seed_eq_platform :
    seed gate = exactEssentialAccessSeed .platform := by
  exact gate.2.2.trans obstruction.platformSeedExact

@[simp] theorem actor_eq_platformActor : actor gate = platformActor := by
  rw [actor, seed_eq_platform]
  rfl

@[simp] theorem relation_eq_platformRelation :
    relation gate = platformRelation := by
  rw [relation, seed_eq_platform]
  rfl

@[simp] theorem phase_eq_platform : phase gate = .platform := by
  rw [phase, relation_eq_platformRelation]
  exact platform_phase_is_generated

@[simp] theorem targetRole_eq_platformProvider :
    targetRole gate = .platformProvider := by
  rw [targetRole, relation_eq_platformRelation]
  exact platform_target_role_is_generated

end SourceGeneratedPlatformChannelGateAt

/-- Existing channels plus exactly the source-generated platform gate. -/
abbrev RevisedPaidEssentialAccessChannelAt
    {boundary : Nat}
    (obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt
      boundary) :=
  EssentialAccessChannel ⊕ SourceGeneratedPlatformChannelGateAt obstruction

def revisedChannelSeed
    {boundary : Nat}
    {obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary} :
    RevisedPaidEssentialAccessChannelAt obstruction →
      essentialAccessRelationCompiler.ExactRelationSeed
  | .inl channel => channelSeed channel
  | .inr gate => gate.seed

theorem revisedChannelSeed_old_exact
    {boundary : Nat}
    {obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary}
    (channel : EssentialAccessChannel) :
    revisedChannelSeed (obstruction := obstruction) (.inl channel) =
      channelSeed channel :=
  rfl

theorem revisedChannelSeed_new_platform
    {boundary : Nat}
    {obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary}
    (gate : SourceGeneratedPlatformChannelGateAt obstruction) :
    revisedChannelSeed (obstruction := obstruction) (.inr gate) =
      exactEssentialAccessSeed .platform :=
  gate.seed_eq_platform

theorem revisedChannel_oldEmbedding_injective
    {boundary : Nat}
    {obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary} :
    Function.Injective
      (Sum.inl : EssentialAccessChannel →
        RevisedPaidEssentialAccessChannelAt obstruction) :=
  Sum.inl_injective

theorem revisedChannel_newGate_hasNoOldPreimage
    {boundary : Nat}
    {obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary}
    (gate : SourceGeneratedPlatformChannelGateAt obstruction) :
    IsEmpty { channel : EssentialAccessChannel //
      (Sum.inl channel : RevisedPaidEssentialAccessChannelAt obstruction) =
        .inr gate } :=
  ⟨fun represented => by
    cases represented.2⟩

theorem revisedChannel_newSeed_hasNoOldRepresentation
    {boundary : Nat}
    {obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary}
    (gate : SourceGeneratedPlatformChannelGateAt obstruction) :
    IsEmpty { channel : EssentialAccessChannel //
      channelSeed channel =
        revisedChannelSeed (obstruction := obstruction) (.inr gate) } := by
  rw [revisedChannelSeed_new_platform]
  exact existingPaidChannel_platformRepresentation_isEmpty

/-- Zero-choice revision candidate at every finite boundary. -/
structure SourceGeneratedPlatformChannelRevisionCandidateAt
    (boundary : Nat) : Type where
  private mk ::
  obstruction : SourceGeneratedCycleMemoryPlatformGateObstructionAt boundary
  gate : SourceGeneratedPlatformChannelGateAt obstruction
  oldEmbeddingInjective : Function.Injective
    (Sum.inl : EssentialAccessChannel →
      RevisedPaidEssentialAccessChannelAt obstruction)
  newSeedPlatform : revisedChannelSeed (obstruction := obstruction)
    (.inr gate) = exactEssentialAccessSeed .platform
  newSeedNoOldRepresentation : IsEmpty
    { channel : EssentialAccessChannel //
      channelSeed channel = revisedChannelSeed
        (obstruction := obstruction) (.inr gate) }

def sourceGeneratedPlatformChannelRevisionCandidateAt (boundary : Nat) :
    SourceGeneratedPlatformChannelRevisionCandidateAt boundary :=
  let obstruction :=
    sourceGeneratedCycleMemoryPlatformGateObstructionAt boundary
  let gate := sourceGeneratedPlatformChannelGateAt obstruction
  { obstruction := obstruction
    gate := gate
    oldEmbeddingInjective := revisedChannel_oldEmbedding_injective
    newSeedPlatform := revisedChannelSeed_new_platform gate
    newSeedNoOldRepresentation :=
      revisedChannel_newSeed_hasNoOldRepresentation gate }

theorem platformChannelRevisionCandidate_directConsumer (boundary : Nat) :
    let candidate := sourceGeneratedPlatformChannelRevisionCandidateAt boundary
    type_of% (cycleMemoryPlatformGateObstruction_directConsumer boundary) ∧
      Function.Injective
        (Sum.inl : EssentialAccessChannel →
          RevisedPaidEssentialAccessChannelAt candidate.obstruction) ∧
      revisedChannelSeed (obstruction := candidate.obstruction)
          (.inr candidate.gate) = exactEssentialAccessSeed .platform ∧
      IsEmpty { channel : EssentialAccessChannel //
        channelSeed channel = revisedChannelSeed
          (obstruction := candidate.obstruction) (.inr candidate.gate) } := by
  dsimp
  let candidate := sourceGeneratedPlatformChannelRevisionCandidateAt boundary
  exact ⟨cycleMemoryPlatformGateObstruction_directConsumer boundary,
    candidate.oldEmbeddingInjective,
    candidate.newSeedPlatform,
    candidate.newSeedNoOldRepresentation⟩

end
end M14SourceGeneratedPlatformChannelRevisionCandidate
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformChannelRevisionCandidate.sourceGeneratedPlatformChannelRevisionCandidateAt
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformChannelRevisionCandidate.revisedChannel_newSeed_hasNoOldRepresentation
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedPlatformChannelRevisionCandidate.platformChannelRevisionCandidate_directConsumer

import H0mework.Foundation.Agency.MaximalActor

/-!
# One source-owned actor lifecycle event

This file fixes one actual occurrence with a before-state, one transfer event,
and an after-state.  Source actors, target actors, and transfers are three
seed faces of that same occurrence.  In particular, the transfer relation is
not a caller-supplied edge list and neither actor carrier is preinstalled in
the `ProcessGame` core.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace Lifecycle

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

/-! ## The unique actual event occurrence -/

inductive EventState where
  | before
  | after
  deriving DecidableEq, Repr

/-- One root, one actual transfer event, and one target state. -/
def actualEventOccurrence : RootedAccountedUnfolding EventState :=
  .occur .before <| .singleton <| .zero .after

def actualEventOccurrenceOf : Unit → RootedAccountedUnfolding EventState :=
  fun _ => actualEventOccurrence

def actualEventGame : SaturationMonoid.ProcessGame actualEventOccurrenceOf :=
  ⟨()⟩

@[simp] theorem actualEventOccurrence_trace :
    actualEventOccurrence.trace =
      [.before, .after] := by
  rfl

/-- The unique actual edge has a fixed generated target state. -/
theorem after_is_exact_generated_next :
    actualEventGame.occurrence.trace.drop 1 = [.after] := by
  rfl

/-! ## Source- and target-generated actors -/

inductive SourceToken where
  | s0
  | s1
  | s2
  | s3
  | s4
  | s5
  deriving DecidableEq, Repr

inductive TargetToken where
  | t0
  | t1
  | t2
  | t3
  | t4
  | t5
  deriving DecidableEq, Repr

def sourceSeedAt (_source : Unit) (state : EventState)
    (_seed : SourceToken) : Prop :=
  state = .before

def targetSeedAt (_source : Unit) (state : EventState)
    (_seed : TargetToken) : Prop :=
  state = .after

def sourceSeed (token : SourceToken) :
    SourceSeed actualEventOccurrenceOf SourceToken sourceSeedAt () :=
  ⟨token, .before, by simp [actualEventOccurrenceOf], rfl⟩

def targetSeed (token : TargetToken) :
    SourceSeed actualEventOccurrenceOf TargetToken targetSeedAt () :=
  ⟨token, .after, by simp [actualEventOccurrenceOf], rfl⟩

def SourceLineage (_source : Unit) := SourceToken

def TargetLineage (_source : Unit) := TargetToken

def sourceLineageOf (_source : Unit)
    (seed : SourceSeed actualEventOccurrenceOf SourceToken sourceSeedAt ()) :
    SourceLineage () :=
  seed.1

def targetLineageOf (_source : Unit)
    (seed : SourceSeed actualEventOccurrenceOf TargetToken targetSeedAt ()) :
    TargetLineage () :=
  seed.1

abbrev SourceActor :=
  GeneratedActor actualEventGame SourceToken sourceSeedAt SourceLineage
    sourceLineageOf

abbrev TargetActor :=
  GeneratedActor actualEventGame TargetToken targetSeedAt TargetLineage
    targetLineageOf

def sourceActorOf (token : SourceToken) : SourceActor :=
  generatedActorOf actualEventGame SourceToken sourceSeedAt SourceLineage
    sourceLineageOf (sourceSeed token)

def targetActorOf (token : TargetToken) : TargetActor :=
  generatedActorOf actualEventGame TargetToken targetSeedAt TargetLineage
    targetLineageOf (targetSeed token)

@[simp] theorem sourceActorOf_value (token : SourceToken) :
    (sourceActorOf token).1 = token :=
  rfl

@[simp] theorem targetActorOf_value (token : TargetToken) :
    (targetActorOf token).1 = token :=
  rfl

theorem sourceActor_eq_canonical (actor : SourceActor) :
    actor = sourceActorOf actor.1 := by
  apply Subtype.ext
  rfl

theorem targetActor_eq_canonical (actor : TargetActor) :
    actor = targetActorOf actor.1 := by
  apply Subtype.ext
  rfl

theorem sourceActors_have_exact_before_seeds (actor : SourceActor) :
    ∃ seed : SourceSeed actualEventOccurrenceOf SourceToken sourceSeedAt (),
      (∃ state ∈ actualEventGame.occurrence.trace,
        sourceSeedAt () state seed.1) ∧
      generatedActorOf actualEventGame SourceToken sourceSeedAt SourceLineage
        sourceLineageOf seed = actor :=
  generatedActor_has_exact_sourceSeed actualEventGame SourceToken sourceSeedAt
    SourceLineage sourceLineageOf actor

theorem targetActors_have_exact_after_seeds (actor : TargetActor) :
    ∃ seed : SourceSeed actualEventOccurrenceOf TargetToken targetSeedAt (),
      (∃ state ∈ actualEventGame.occurrence.trace,
        targetSeedAt () state seed.1) ∧
      generatedActorOf actualEventGame TargetToken targetSeedAt TargetLineage
        targetLineageOf seed = actor :=
  generatedActor_has_exact_sourceSeed actualEventGame TargetToken targetSeedAt
    TargetLineage targetLineageOf actor

/-! ## Exact transfer provenance generated at the middle event -/

/-- The closed event law.  This is source-owned production data, not a
classifier verdict: all lifecycle classes below are recovered from its
fibres. -/
def eventTransfers : SourceToken → TargetToken → Prop
  | .s0, .t0 => True
  | .s1, .t1 => True
  | .s1, .t2 => True
  | .s1, .t3 => True
  | .s2, .t1 => True
  | .s2, .t2 => True
  | .s2, .t3 => True
  | .s3, .t1 => True
  | .s3, .t2 => True
  | .s3, .t3 => True
  | .s5, .t4 => True
  | _, _ => False

abbrev TransferToken := SourceToken × TargetToken

def transferSeedAt (_source : Unit) (state : EventState)
    (transfer : TransferToken) : Prop :=
  state = .after ∧ eventTransfers transfer.1 transfer.2

def transferSeed (source : SourceToken) (target : TargetToken)
    (transfers : eventTransfers source target) :
    SourceSeed actualEventOccurrenceOf TransferToken transferSeedAt () :=
  ⟨(source, target), .after,
    by simp [actualEventOccurrenceOf], rfl, transfers⟩

/-- Exact seed-to-seed transfer provenance.  Both endpoint seeds and the
transfer witness live in the same source occurrence. -/
def ActorRelated (source : SourceActor) (target : TargetActor) : Prop :=
  ∃ sourceWitness :
      SourceSeed actualEventOccurrenceOf SourceToken sourceSeedAt (),
    generatedActorOf actualEventGame SourceToken sourceSeedAt SourceLineage
        sourceLineageOf sourceWitness = source ∧
    ∃ targetWitness :
        SourceSeed actualEventOccurrenceOf TargetToken targetSeedAt (),
      generatedActorOf actualEventGame TargetToken targetSeedAt TargetLineage
          targetLineageOf targetWitness = target ∧
      ∃ transferWitness :
          SourceSeed actualEventOccurrenceOf TransferToken transferSeedAt (),
        transferWitness.1 = (sourceWitness.1, targetWitness.1)

@[simp] theorem actorRelated_iff_eventTransfers
    (source : SourceActor) (target : TargetActor) :
    ActorRelated source target ↔ eventTransfers source.1 target.1 := by
  constructor
  · rintro ⟨sourceWitness, sourceGenerated, targetWitness, targetGenerated,
      transferWitness, endpoints⟩
    have sourceValue : sourceWitness.1 = source.1 := by
      have generatedValue := congrArg Subtype.val sourceGenerated
      change sourceWitness.1 = source.1 at generatedValue
      exact generatedValue
    have targetValue : targetWitness.1 = target.1 := by
      have generatedValue := congrArg Subtype.val targetGenerated
      change targetWitness.1 = target.1 at generatedValue
      exact generatedValue
    rcases transferWitness.2 with
      ⟨state, _inTrace, atEvent, transfers⟩
    have transferValues :
        eventTransfers transferWitness.1.1 transferWitness.1.2 := by
      simpa [transferSeedAt] using transfers
    rw [endpoints] at transferValues
    simpa [sourceValue, targetValue] using transferValues
  · intro transfers
    refine ⟨sourceSeed source.1, ?_, targetSeed target.1, ?_,
      transferSeed source.1 target.1 transfers, rfl⟩
    · exact (sourceActor_eq_canonical source).symm
    · exact (targetActor_eq_canonical target).symm

/-- Targets related to one source actor, generated from exact event transfer
provenance. -/
def DescendantFiber (source : SourceActor) :=
  { target : TargetActor // ActorRelated source target }

/-- Sources related to one target actor, generated from the same exact event
transfer provenance. -/
def PredecessorFiber (target : TargetActor) :=
  { source : SourceActor // ActorRelated source target }

/-! ## Lower provenance for the two singleton-fibre cases -/

/-- A neutral identity seed.  Continuity is witnessed by the very same seed
at the before and after states; it is not inferred from a lifecycle label. -/
inductive IdentitySeed where
  | i0
  deriving DecidableEq, Repr

abbrev SourceIdentityEndpoint := SourceToken × IdentitySeed
abbrev TargetIdentityEndpoint := TargetToken × IdentitySeed

def sourceIdentitySeedAt (_source : Unit) (state : EventState)
    (endpoint : SourceIdentityEndpoint) : Prop :=
  state = .before ∧ endpoint = (.s0, .i0)

def targetIdentitySeedAt (_source : Unit) (state : EventState)
    (endpoint : TargetIdentityEndpoint) : Prop :=
  state = .after ∧ endpoint = (.t0, .i0)

def sourceIdentitySeed :
    SourceSeed actualEventOccurrenceOf SourceIdentityEndpoint
      sourceIdentitySeedAt () :=
  ⟨(.s0, .i0), .before,
    by simp [actualEventOccurrenceOf], rfl, rfl⟩

def targetIdentitySeed :
    SourceSeed actualEventOccurrenceOf TargetIdentityEndpoint
      targetIdentitySeedAt () :=
  ⟨(.t0, .i0), .after,
    by simp [actualEventOccurrenceOf], rfl, rfl⟩

/-- Exact same-seed continuity across the event. -/
def SharedIdentityProvenance (source : SourceActor)
    (target : TargetActor) : Prop :=
  ∃ sourceWitness :
      SourceSeed actualEventOccurrenceOf SourceIdentityEndpoint
        sourceIdentitySeedAt (),
    sourceWitness.1.1 = source.1 ∧
    ∃ targetWitness :
        SourceSeed actualEventOccurrenceOf TargetIdentityEndpoint
          targetIdentitySeedAt (),
      targetWitness.1.1 = target.1 ∧
      sourceWitness.1.2 = targetWitness.1.2

@[simp] theorem sharedIdentityProvenance_iff
    (source : SourceActor) (target : TargetActor) :
    SharedIdentityProvenance source target ↔
      source.1 = .s0 ∧ target.1 = .t0 := by
  constructor
  · rintro ⟨sourceWitness, sourceEndpoint, targetWitness, targetEndpoint,
      _sameSeed⟩
    rcases sourceWitness.2 with
      ⟨state, _inTrace, atBefore, endpoint⟩
    rcases targetWitness.2 with
      ⟨targetState, _targetInTrace, atAfter, targetEndpointValue⟩
    have sourceFixed : sourceWitness.1 = (.s0, .i0) := by
      simpa [sourceIdentitySeedAt] using endpoint
    have targetFixed : targetWitness.1 = (.t0, .i0) := by
      simpa [targetIdentitySeedAt] using targetEndpointValue
    constructor
    · change source.1 = SourceToken.s0
      exact sourceEndpoint.symm.trans (congrArg Prod.fst sourceFixed)
    · change target.1 = TargetToken.t0
      exact targetEndpoint.symm.trans (congrArg Prod.fst targetFixed)
  · rintro ⟨sourceValue, targetValue⟩
    refine ⟨sourceIdentitySeed, ?_, targetIdentitySeed, ?_, rfl⟩
    · change SourceToken.s0 = source.1
      change source.1 = SourceToken.s0 at sourceValue
      exact sourceValue.symm
    · change TargetToken.t0 = target.1
      change target.1 = TargetToken.t0 at targetValue
      exact targetValue.symm

end Lifecycle
end Society
end ProcessGame
end SaturationMonoid

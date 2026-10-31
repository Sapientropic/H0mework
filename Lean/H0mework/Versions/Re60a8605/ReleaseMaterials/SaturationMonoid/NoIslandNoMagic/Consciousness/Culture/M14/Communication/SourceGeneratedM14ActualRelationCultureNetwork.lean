import H0mework.Foundation.Runtime.OperationalSeparation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Memory.Source.SourceGeneratedActualRelationRoleReflexiveRing

/-!
# Source-generated M14 actual-relation culture network

The existing M14 cross runtime first generates three actual relation macro
edges.  This file indexes those generated edges by `ThreeCycleTime` and exposes
them as an `ActualCommunicationNetwork`.  It does not reinterpret the relation
family as communication by name: every public contact event retains its exact
`SourceGeneratedActualRelationMacroEdgeAt` receipt.

The transported carrier at a support is the singleton practice-medium role
received from its actual incoming edge.  An actual edge presents that carrier
as the next support's incoming medium.  The three presentations compose to a
closed, three-event path with a canonical whole-carrier write-back.

No culture quotient, gluing theorem, root, ledger installation, institutional
revision, or generated next is introduced here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Communication

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution
open Lifecycle Universal Relations
open M14EssentialAccessRelationFixture
open M14SourceGeneratedEssentialAccessRelationRenewal
open M14SourceGeneratedActualRelationThreeCycle
open M14ProofCarryingActualRelationThreeCycleResidual
open M14SourceGeneratedActualRelationRoleReflexiveRing

noncomputable section

abbrev ExactRelationSeed :=
  essentialAccessRelationCompiler.ExactRelationSeed

/-! ## Exact support-local practice medium -/

/-- The practice medium present at one support is exactly the target role
written by that support's actual incoming relation edge. -/
abbrev CulturePracticeMediumAt
    (base : Nat) (support : ThreeCycleTime) :=
  { role : EssentialAccessRole //
    role = actualRelationCycleTargetRoleAt base
      (actualRelationIncomingIndex support) }

def culturePracticeMediumAt
    (base : Nat) (support : ThreeCycleTime) :
    CulturePracticeMediumAt base support :=
  ⟨actualRelationCycleTargetRoleAt base
      (actualRelationIncomingIndex support), rfl⟩

/-! ## Actual contact events and source-native transports -/

/-- A culture contact is one already generated M14 relation macro edge.
The constructor is private; callers can only request the canonical event at
one support of the generated cycle. -/
structure SourceGeneratedM14CultureContactEventAt
    (base : Nat) : Type where
  private mk ::
  support : ThreeCycleTime
  macroEdge : SourceGeneratedActualRelationMacroEdgeAt
    (actualRelationCycleDepthAt base support)

def sourceGeneratedM14CultureContactEventAt
    (base : Nat) (support : ThreeCycleTime) :
    SourceGeneratedM14CultureContactEventAt base :=
  ⟨support, sourceGeneratedActualRelationMacroEdgeAt _⟩

/-- Exact anchor-level contact evidence retained by the communication
network. -/
structure SourceGeneratedM14CultureContactAt
    (base : Nat)
    (source target : essentialAccessRelationCompiler.Actor) : Type where
  actualEvent : SourceGeneratedM14CultureContactEventAt base
  sourceExact : source =
    actualRelationCycleActorAt base actualEvent.support
  targetExact : target =
    actualRelationCycleActorAt base
      (threeCycleNext actualEvent.support)

/-- Exact incidence transport of one generated contact. -/
structure SourceGeneratedM14CultureIncidenceTransportAt
    (base : Nat) (source target : Int) : Type where
  actualEvent : SourceGeneratedM14CultureContactEventAt base
  sourceExact : source =
    actualRelationCycleIncidenceOf base actualEvent.support
  targetExact : target =
    actualRelationCycleIncidenceOf base
      (threeCycleNext actualEvent.support)

/-- Exact relation lineage transport of one generated contact. -/
structure SourceGeneratedM14CultureLineageTransportAt
    (base : Nat) (source target : ExactRelationSeed) : Type where
  actualEvent : SourceGeneratedM14CultureContactEventAt base
  sourceExact : source = actualRelationSeedAt
    (actualRelationCycleDepthAt base actualEvent.support)
  targetExact : target = actualRelationSeedAt
    (actualRelationCycleDepthAt base
      (threeCycleNext actualEvent.support))
  targetGenerated : target =
    sourceGeneratedEssentialAccessRenewalSeed source

/-- The lineage attached to the next support is exactly the source-generated
renewal of the current support's lineage.  At the third edge this consumes
period-three seed closure rather than identifying the two action
occurrences. -/
theorem actualRelationCycleLineage_targetGenerated
    (base : Nat) (support : ThreeCycleTime) :
    actualRelationSeedAt
        (actualRelationCycleDepthAt base (threeCycleNext support)) =
      sourceGeneratedEssentialAccessRenewalSeed
        (actualRelationSeedAt
          (actualRelationCycleDepthAt base support)) := by
  cases support with
  | t0 =>
      change actualRelationSeedAt (base + 1) =
        sourceGeneratedEssentialAccessRenewalSeed
          (actualRelationSeedAt base)
      exact (sourceGeneratedActualRelationMacroEdgeAt base).targetSeedRenewal
  | t1 =>
      change actualRelationSeedAt (base + 2) =
        sourceGeneratedEssentialAccessRenewalSeed
          (actualRelationSeedAt (base + 1))
      convert
        (sourceGeneratedActualRelationMacroEdgeAt
          (base + 1)).targetSeedRenewal using 1
  | t2 =>
      change actualRelationSeedAt base =
        sourceGeneratedEssentialAccessRenewalSeed
          (actualRelationSeedAt (base + 2))
      calc
        actualRelationSeedAt base =
            actualRelationSeedAt (base + 3) :=
          (sourceGeneratedActualRelationThreeCycleAt base).seedClosure.symm
        _ = sourceGeneratedEssentialAccessRenewalSeed
              (actualRelationSeedAt (base + 2)) := by
          convert
            (sourceGeneratedActualRelationMacroEdgeAt
              (base + 2)).targetSeedRenewal using 1

/-- Whole practice-medium presentation generated by one exact contact.  Both
fibres are source-fixed singletons, so forward and backward programs have no
caller-selectable payload. -/
def culturePracticeMediumPresentationAt
    {base : Nat}
    (event : SourceGeneratedM14CultureContactEventAt base) :
    ConstructivePresentation
      (CulturePracticeMediumAt base event.support)
      (CulturePracticeMediumAt base (threeCycleNext event.support)) where
  forward := fun _ =>
    culturePracticeMediumAt base (threeCycleNext event.support)
  backward := fun _ => culturePracticeMediumAt base event.support
  backward_forward := by
    intro medium
    apply Subtype.ext
    exact medium.property.symm
  forward_backward := by
    intro medium
    apply Subtype.ext
    exact medium.property.symm

/-! ## Three-support world and communication network -/

/-- The finite communication world is a source-derived chart of the actual
M14 cycle.  It is not the M14 institutional root network. -/
def m14CultureWorldAt (base : Nat) : WorldRelationNetwork where
  Support := ThreeCycleTime
  Anchor := essentialAccessRelationCompiler.Actor
  Incidence := Int
  Lineage := ExactRelationSeed
  Responsibility := ThreeCycleTime
  Claim := ExactRelationSeed
  anchorAt := actualRelationCycleActorAt base
  incidenceAt := actualRelationCycleIncidenceOf base
  lineageAt := fun support => actualRelationSeedAt
    (actualRelationCycleDepthAt base support)
  OpenAt := fun support responsibility => PLift (responsibility = support)
  openClaimAt := fun {support} {_responsibility} _open =>
    actualRelationSeedAt (actualRelationCycleDepthAt base support)
  HoldsAt := fun support claim => PLift
    (claim = actualRelationSeedAt
      (actualRelationCycleDepthAt base support))
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := fun obstruction => nomatch obstruction
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun _ _ => PEmpty

abbrev M14CultureWorldAt (base : Nat) := m14CultureWorldAt base

def m14CultureCommunicationAt (base : Nat) :
    ActualCommunicationNetwork (M14CultureWorldAt base) where
  Carrier := CulturePracticeMediumAt base
  Observation := fun _ => EssentialAccessRole
  observe := fun _ medium => medium.1
  ContactAt := SourceGeneratedM14CultureContactAt base
  IncidenceTransportAt :=
    SourceGeneratedM14CultureIncidenceTransportAt base
  LineageTransportAt :=
    SourceGeneratedM14CultureLineageTransportAt base
  Event := SourceGeneratedM14CultureContactEventAt base
  sourceSupport := SourceGeneratedM14CultureContactEventAt.support
  targetSupport := fun event => threeCycleNext event.support
  contact := fun event => ⟨event, rfl, rfl⟩
  incidenceTransport := fun event => ⟨event, rfl, rfl⟩
  lineageTransport := fun event =>
    ⟨event, rfl, rfl,
      actualRelationCycleLineage_targetGenerated base event.support⟩
  carrierTransport := culturePracticeMediumPresentationAt

abbrev M14CultureCommunicationAt (base : Nat) :=
  m14CultureCommunicationAt base

/-! ## Fixed payload and target-practice consumer -/

def m14CulturePayloadSourceAt (base : Nat) :
    ActualPayloadSource (M14CultureCommunicationAt base) where
  EventAt := fun _ => PUnit
  emit := fun _ => PUnit.unit
  payload := fun {support} _ => culturePracticeMediumAt base support

def m14CultureTargetConsumerSourceAt (base : Nat) :
    ActualTargetConsumerSource (M14CultureCommunicationAt base) where
  EventAt := fun _ _ => PUnit
  emit := fun _ _ => PUnit.unit
  EffectAt := fun _ => Int
  effectFromObservation := fun support role =>
    actualRelationIncomingRoleReadAt base support role
  openEntryAt := fun {support} {_observation} _ =>
    ⟨support, ⟨rfl⟩⟩

def m14CultureOperationalSourcesAt (base : Nat) :
    ActualOperationalSeparationSources
      (M14CultureCommunicationAt base) where
  payloadSource := m14CulturePayloadSourceAt base
  consumerSource := m14CultureTargetConsumerSourceAt base
  CutEventAt := fun _ _ => PEmpty
  cutSide := fun event => nomatch event
  cut_source_side := fun event => nomatch event
  cut_target_side := fun event => nomatch event
  cut_blocks := fun event => nomatch event
  cutObstruction := fun event => nomatch event

/-! ## Three exact edges and generated deliveries -/

def m14CultureContactEdgeAt
    (base : Nat) (support : ThreeCycleTime) :
    ActualContactEdgeAt (M14CultureCommunicationAt base)
      support (threeCycleNext support) :=
  { actualEvent := sourceGeneratedM14CultureContactEventAt base support
    source_eq := rfl
    target_eq := rfl }

def m14CultureEdgePathAt
    (base : Nat) (support : ThreeCycleTime) :
    SourceOwnedTransportPath (M14CultureCommunicationAt base)
      support (threeCycleNext support) :=
  .cons (m14CultureContactEdgeAt base support)
    (@SourceOwnedTransportPath.nil (M14CultureWorldAt base)
      (M14CultureCommunicationAt base) (threeCycleNext support))

def m14CultureEdgeDeliveryAt
    (base : Nat) (support : ThreeCycleTime) :
    GeneratedDeliveryAt (M14CultureCommunicationAt base)
      (m14CultureOperationalSourcesAt base)
      support (threeCycleNext support) where
  path := m14CultureEdgePathAt base support

/-- The ordered actual cycle `t0 → t1 → t2 → t0`. -/
def m14CultureCyclePathAt (base : Nat) :
    SourceOwnedTransportPath (M14CultureCommunicationAt base)
      .t0 .t0 :=
  .cons (m14CultureContactEdgeAt base .t0)
    (.cons (m14CultureContactEdgeAt base .t1)
      (.cons (m14CultureContactEdgeAt base .t2)
        (@SourceOwnedTransportPath.nil (M14CultureWorldAt base)
          (M14CultureCommunicationAt base) ThreeCycleTime.t0)))

def m14CultureCycleDeliveryAt (base : Nat) :
    GeneratedDeliveryAt (M14CultureCommunicationAt base)
      (m14CultureOperationalSourcesAt base) .t0 .t0 where
  path := m14CultureCyclePathAt base

@[simp] theorem m14CultureContactEdge_actualEvent_exact
    (base : Nat) (support : ThreeCycleTime) :
    (m14CultureContactEdgeAt base support).actualEvent =
      sourceGeneratedM14CultureContactEventAt base support :=
  by
    change sourceGeneratedM14CultureContactEventAt base support =
      sourceGeneratedM14CultureContactEventAt base support
    rfl

theorem m14CultureContactEvent_macroEdge_exact
    (base : Nat) (support : ThreeCycleTime) :
    type_of%
      (sourceGeneratedM14CultureContactEventAt base support).macroEdge :=
  (sourceGeneratedM14CultureContactEventAt base support).macroEdge

@[simp] theorem m14CultureCyclePath_length (base : Nat) :
    (m14CultureCyclePathAt base).length = 3 :=
  by simp [m14CultureCyclePathAt, SourceOwnedTransportPath.length]

@[simp] theorem m14CultureCyclePath_events_exact (base : Nat) :
    (m14CultureCyclePathAt base).events =
      [sourceGeneratedM14CultureContactEventAt base .t0,
        sourceGeneratedM14CultureContactEventAt base .t1,
        sourceGeneratedM14CultureContactEventAt base .t2] :=
  by
    change
      [sourceGeneratedM14CultureContactEventAt base .t0,
        sourceGeneratedM14CultureContactEventAt base .t1,
        sourceGeneratedM14CultureContactEventAt base .t2] =
      [sourceGeneratedM14CultureContactEventAt base .t0,
        sourceGeneratedM14CultureContactEventAt base .t1,
        sourceGeneratedM14CultureContactEventAt base .t2]
    rfl

theorem m14CultureEdgeDelivery_effect_eq_one
    (base : Nat) (support : ThreeCycleTime) :
    (show Int from (m14CultureEdgeDeliveryAt base support).effect) = 1 := by
  change actualRelationIncomingRoleReadAt base (threeCycleNext support)
    (m14CultureEdgeDeliveryAt base support).targetValue.1 = 1
  rw [(m14CultureEdgeDeliveryAt base support).targetValue.property]
  simpa [actualRelationIncomingIndex] using
    (actualRelationIncomingRoleReadAt_target_eq_one_iff
      base support (threeCycleNext support)).2 rfl

theorem m14CultureEdgeDelivery_consumerSafe
    (base : Nat) (support : ThreeCycleTime) :
    ConsumerSafe
      ((M14CultureCommunicationAt base).observe (threeCycleNext support))
      ((m14CultureOperationalSourcesAt base).consumerSource.consumerAt
        (threeCycleNext support)) :=
  (m14CultureEdgeDeliveryAt base support).observer_safe

/-- The closed actual path returns to the same exact practice-medium fibre.
This equality does not erase its nonempty ordered event trace. -/
theorem m14CultureCycleDelivery_targetValue_eq_sourceValue
    (base : Nat) :
    (m14CultureCycleDeliveryAt base).targetValue =
      (m14CultureCycleDeliveryAt base).sourceValue := by
  apply Subtype.ext
  exact (m14CultureCycleDeliveryAt base).targetValue.property.trans
    (m14CultureCycleDeliveryAt base).sourceValue.property.symm

theorem m14CultureCycleDelivery_effect_eq_one (base : Nat) :
    (show Int from (m14CultureCycleDeliveryAt base).effect) = 1 := by
  change actualRelationIncomingRoleReadAt base .t0
    (m14CultureCycleDeliveryAt base).targetValue.1 = 1
  rw [(m14CultureCycleDeliveryAt base).targetValue.property]
  exact
    (actualRelationIncomingRoleReadAt_target_eq_one_iff
      base .t2 .t0).2 rfl

theorem m14CultureCycleDelivery_consumerSafe (base : Nat) :
    ConsumerSafe
      ((M14CultureCommunicationAt base).observe .t0)
      ((m14CultureOperationalSourcesAt base).consumerSource.consumerAt
        .t0) :=
  (m14CultureCycleDeliveryAt base).observer_safe

theorem m14CultureCycleDelivery_writeBack_is_generated (base : Nat) :
    (m14CultureCycleDeliveryAt base).targetValue =
      (m14CultureCyclePathAt base).transport
        (m14CultureCycleDeliveryAt base).sourceValue :=
  (m14CultureCycleDeliveryAt base).targetValue_eq_transport

theorem everyM14CultureCycleWriteBack_is_canonical
    (base : Nat)
    (writeBack : SourceOwnedTransportPath.GeneratedPathWriteBackAt
      (m14CultureCyclePathAt base)
      (m14CultureCycleDeliveryAt base).sourceValue) :
    writeBack = (m14CultureCyclePathAt base).generatedWriteBack
      (m14CultureCycleDeliveryAt base).sourceValue :=
  writeBack.eq_generated

/-- Direct consumer of the actual three-support communication checkpoint.
It exposes the original relation receipts, exact contact endpoints, ordered
path, whole-carrier write-back, target practice effect, and observer safety. -/
theorem sourceGeneratedM14ActualRelationCultureNetwork_directConsumer
    (base : Nat) :
    type_of% (actualRelationThreeCycle_directConsumer base) ∧
      (∀ support : ThreeCycleTime,
        type_of% (m14CultureContactEvent_macroEdge_exact base support)) ∧
      (∀ support : ThreeCycleTime,
        (m14CultureContactEdgeAt base support).actualEvent =
          sourceGeneratedM14CultureContactEventAt base support) ∧
      (m14CultureCyclePathAt base).length = 3 ∧
      (m14CultureCyclePathAt base).events =
        [sourceGeneratedM14CultureContactEventAt base .t0,
          sourceGeneratedM14CultureContactEventAt base .t1,
          sourceGeneratedM14CultureContactEventAt base .t2] ∧
      (∀ support : ThreeCycleTime,
        (show Int from
          (m14CultureEdgeDeliveryAt base support).effect) = 1) ∧
      (∀ support : ThreeCycleTime,
        ConsumerSafe
          ((M14CultureCommunicationAt base).observe
            (threeCycleNext support))
          ((m14CultureOperationalSourcesAt base).consumerSource.consumerAt
            (threeCycleNext support))) ∧
      (m14CultureCycleDeliveryAt base).targetValue =
        (m14CultureCycleDeliveryAt base).sourceValue ∧
      (show Int from (m14CultureCycleDeliveryAt base).effect) = 1 ∧
      type_of% (m14CultureCycleDelivery_writeBack_is_generated base) :=
  ⟨actualRelationThreeCycle_directConsumer base,
    m14CultureContactEvent_macroEdge_exact base,
    m14CultureContactEdge_actualEvent_exact base,
    m14CultureCyclePath_length base,
    m14CultureCyclePath_events_exact base,
    m14CultureEdgeDelivery_effect_eq_one base,
    m14CultureEdgeDelivery_consumerSafe base,
    m14CultureCycleDelivery_targetValue_eq_sourceValue base,
    m14CultureCycleDelivery_effect_eq_one base,
    m14CultureCycleDelivery_writeBack_is_generated base⟩

end
end Communication
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication.actualRelationCycleLineage_targetGenerated
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication.m14CultureCyclePath_events_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication.m14CultureEdgeDelivery_effect_eq_one
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication.everyM14CultureCycleWriteBack_is_canonical
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication.sourceGeneratedM14ActualRelationCultureNetwork_directConsumer

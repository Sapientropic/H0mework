import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Runtime.Payment.Novelty.PostSettlement.Representation.Revision.Compiler.SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler

/-!
# Pair-intent U8 revised root

The revised root is installed directly on the canonical minimal coface.  Its
law surface is the coface network's root semantic, and its initial generated
ledger exposes exactly the three inherited target rows plus the generated
obstruction row.  The old target successor and the revised ingress are joined
only by an occurrence presentation; no sibling occurrence or ledger is kept.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Root

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ConstructiveRoot.ObstructionGeneratedMinimalCoface
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityRepresentationClaimWorld
open M14SourceGeneratedContributionCapacityRepresentationPairIntentCompiler
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRoot
open M14SourceGeneratedContributionCapacityRepresentationPairIntentRootedFailure
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Lifecycle
open M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Compiler

def representationIntentU8DefaultEntryAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (support : (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support) →
      OpenResponsibilityAt
        (RepresentationIntentU8NAt oldVisit sourceIndex boundary) support
  | .inl oldSupport =>
      let oldEntry := representationIntentDefaultEntryAt oldVisit sourceIndex
        boundary oldSupport
      ⟨.inl oldEntry.1, oldEntry.2⟩
  | .inr direction => by
      cases direction
      exact representationIntentU8GeneratedEntryAt oldVisit sourceIndex boundary

def representationIntentU8LawExtensionDispositionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (support : (RepresentationIntentU8NAt oldVisit sourceIndex boundary).Support) :
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary).DispositionAt
      support .lawSurfaceExtension := by
  cases support with
  | inl oldSupport =>
      exact representationIntentLawExtensionDispositionAt oldVisit sourceIndex
        boundary oldSupport
  | inr direction =>
      cases direction
      exact GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget
        (representationIntentLawExtensionDispositionAt oldVisit sourceIndex
          boundary
          (representationIntentSupportAt oldVisit sourceIndex boundary))

def representationIntentU8RevisedU7
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    U7ProducerCalculus
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary) where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

def representationIntentU8RevisedU7Source
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    U7ActualSuccessorSource
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (representationIntentU8RevisedU7 oldVisit sourceIndex boundary) where
  EventAt := SourceGeneratedU7DemandAt
    (representationIntentU8RevisedU7 oldVisit sourceIndex boundary)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {support} {_obstruction} {_demand} _event =>
    representationIntentU8DefaultEntryAt oldVisit sourceIndex boundary support

def representationIntentU8RevisedCalculus
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    U7ObstructionEvolutionCalculus
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (representationIntentU8RevisedU7 oldVisit sourceIndex boundary) where
  source := representationIntentU8RevisedU7Source oldVisit sourceIndex boundary
  compile := by
    intro support obstruction demand event
    exact
      { disposition := .requiresTheoryAudit
          (representationIntentU8LawExtensionDispositionAt oldVisit sourceIndex
            boundary support)
        demandEntryDisposition := PUnit.unit }

def representationIntentU8RevisedTheory
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    TheoryState (RepresentationIntentU8NAt oldVisit sourceIndex boundary) :=
  TheoryState.rootSemantic
    (RepresentationIntentU8NAt oldVisit sourceIndex boundary)

def representationIntentU8RevisedInquiryAudit
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryFrontAuditAt
      (representationIntentU8RevisedU7 oldVisit sourceIndex boundary)
      (representationIntentU8RevisedCalculus oldVisit sourceIndex boundary)
      (representationIntentU8RevisedTheory oldVisit sourceIndex boundary)
      (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
        ).cofaceSupport :=
  .answered

inductive RepresentationIntentU8Projection
  | ledgerLifecycle
  | inquiry
  | answer
  | consumer (entryIndex : Fin 4)

def RepresentationIntentU8RootPayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    {current : (RepresentationIntentU8VAt oldVisit sourceIndex boundary).Current}
    (occurrence :
      (representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.actual.OccurrenceAt current) : Type :=
  SourceNativeLedgerEvolutionAt
      (representationIntentU8Source oldVisit sourceIndex boundary) occurrence ×
    ((entry : OpenResponsibilityAt
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      ((representationIntentU8Source oldVisit sourceIndex boundary
        ).toRootSource.account.supportOf occurrence)) →
      AdmittedObligation
        (RepresentationIntentU8LifecycleV oldVisit sourceIndex boundary))

def representationIntentU8ProjectionLaw
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw
      (representationIntentU8RestructuringSource oldVisit sourceIndex boundary
        ).toLedgerSource where
  Projection := RepresentationIntentU8Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_} occurrence _ =>
    match projection with
    | .ledgerLifecycle =>
        RepresentationIntentU8RootPayloadAt oldVisit sourceIndex boundary
          occurrence
    | .inquiry =>
        SourceNativeInquiryCompilationTokenAt
          (representationIntentU8DefaultEntryAt oldVisit sourceIndex boundary
            (RepresentationIntentCofaceAt oldVisit sourceIndex boundary
              ).cofaceSupport)
          () (ULift.up.{1, 0} occurrence)
          (representationIntentU8RevisedInquiryAudit oldVisit sourceIndex
            boundary) PUnit
    | .answer => PUnit
    | .consumer entryIndex =>
        SourceNativeInquiryAnswerConsumerTokenAt
          () (ULift.up.{1, 0} occurrence)
          (representationIntentU8EntryAt oldVisit sourceIndex boundary
            entryIndex) PUnit.unit
  project := by
    intro projection current occurrence active
    cases projection with
    | ledgerLifecycle =>
        exact
          ⟨(representationIntentU8LedgerCompiler oldVisit sourceIndex boundary
            ).compile occurrence,
            fun entry => representationIntentU8ObligationAt oldVisit
              sourceIndex boundary occurrence.2.materialWitness entry⟩
    | inquiry => exact .canonical PUnit.unit
    | answer => exact PUnit.unit
    | consumer _entryIndex => exact .canonical

def representationIntentU8AuthoritySource
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritySource
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (RepresentationIntentU8VAt oldVisit sourceIndex boundary) where
  restructuringSource :=
    representationIntentU8RestructuringSource oldVisit sourceIndex boundary
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      (representationIntentU8RestructuringSource oldVisit sourceIndex boundary)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface :=
    representationIntentU8RevisedTheory oldVisit sourceIndex boundary
  projectionLaw :=
    representationIntentU8ProjectionLaw oldVisit sourceIndex boundary

def representationIntentU8AuthoritativeRoot
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (RepresentationIntentU8VAt oldVisit sourceIndex boundary) where
  source := representationIntentU8AuthoritySource oldVisit sourceIndex boundary
  emitted := representationIntentU8Emitted oldVisit sourceIndex boundary
  compiler_commutes := fun current => by cases current <;> rfl

def representationIntentU8LivingRoot
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (RepresentationIntentU8NAt oldVisit sourceIndex boundary)
      (RepresentationIntentU8VAt oldVisit sourceIndex boundary) :=
  (representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary
    ).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem representationIntentU8Root_lawSurface_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8LivingRoot oldVisit sourceIndex boundary
      ).source.base.lawSurface =
      TheoryState.rootSemantic
        (RepresentationIntentU8NAt oldVisit sourceIndex boundary) :=
  rfl

def representationIntentU8OccurrencePresentation
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructivePresentation
      ((InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
          (RepresentationIntentRootedAt oldVisit sourceIndex boundary
            ).oldSuccessor.next)
      ((representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary
        ).toRoot.actual.OccurrenceAt false) where
  forward := fun _ =>
    representationIntentU8Emitted oldVisit sourceIndex boundary false
  backward := fun _ =>
    (InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
      ).emitted
        (RepresentationIntentRootedAt oldVisit sourceIndex boundary
          ).oldSuccessor.next
  backward_forward := by
    intro occurrence
    exact (representationIntentOccurrence_eq_emitted oldVisit sourceIndex
      boundary occurrence).symm
  forward_backward := by
    intro occurrence
    exact (representationIntentU8Occurrence_eq_emitted oldVisit sourceIndex
      boundary occurrence).symm

@[simp] theorem representationIntentU8Occurrence_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8OccurrencePresentation oldVisit sourceIndex boundary
      ).forward
        ((InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
          ).emitted
            (RepresentationIntentRootedAt oldVisit sourceIndex boundary
              ).oldSuccessor.next) =
      (representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary
        ).emitted false :=
  rfl

def representationIntentU8FirstWrite
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    CanonicalFirstRootWriteAt
      (representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary
        ).toLedgerRoot :=
  PUnit.unit

def representationIntentU8InitialVisit
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeTemporalVisitAt
      (representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary
        ).toLedgerRoot :=
  .finite
    (representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary
      ).toRoot.initialVisit

def representationIntentU8InitialGenerated
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (representationIntentU8AuthoritativeRoot oldVisit sourceIndex boundary
    ).toLedgerRoot
    |>.generatedAtTemporalVisit
      (representationIntentU8InitialVisit oldVisit sourceIndex boundary)

def representationIntentU8InheritedRowAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) (index : Fin 3) :
    (representationIntentU8InitialGenerated oldVisit sourceIndex boundary
      ).GeneratedEntryRowAt
        (representationIntentU8InheritedEntryAt oldVisit sourceIndex boundary
          index) :=
  ((representationIntentU8InitialGenerated oldVisit sourceIndex boundary
    ).canonicalGeneratedEntryRow?
      (representationIntentU8InheritedEntryAt oldVisit sourceIndex boundary
        index)).get (by
          fin_cases index <;> rfl)

def representationIntentU8GeneratedRow
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (representationIntentU8InitialGenerated oldVisit sourceIndex boundary
      ).GeneratedEntryRowAt
        (representationIntentU8GeneratedEntryAt oldVisit sourceIndex
          boundary) :=
  ((representationIntentU8InitialGenerated oldVisit sourceIndex boundary
    ).canonicalGeneratedEntryRow?
      (representationIntentU8GeneratedEntryAt oldVisit sourceIndex
        boundary)).get (by rfl)

def representationIntentU8OldEntryRows
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (oldEntry : OpenResponsibilityAt
      (RepresentationIntentNAt oldVisit sourceIndex boundary)
      ((InstalledRepresentationIntentRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toRoot.supportAt
          (RepresentationIntentRootedAt oldVisit sourceIndex boundary
            ).oldSuccessor.next)) :
    (representationIntentU8InitialGenerated oldVisit sourceIndex boundary
      ).GeneratedEntryRowAt
        ((RepresentationIntentCofaceAt oldVisit sourceIndex boundary
          ).cofaceLedgerRetract.forward oldEntry) := by
  let index := representationIntentEntryIndex oldVisit sourceIndex boundary
    oldEntry
  have entry_eq := representationIntentEntryAt_index oldVisit sourceIndex
    boundary oldEntry
  rw [← entry_eq]
  exact representationIntentU8InheritedRowAt oldVisit sourceIndex boundary index

end
end M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Root
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Root.representationIntentU8Root_lawSurface_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Root.representationIntentU8Occurrence_commutes
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityRepresentationPairIntentU8Root.representationIntentU8OldEntryRows

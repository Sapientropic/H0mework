import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.U8.Compiler.SourceGeneratedContributionCapacityU8Compiler

/-!
# Source-generated contribution-capacity self-U8 root

The revised root is the exact obstruction-generated minimal coface.  Its
root-semantic law surface makes the formerly excluded capacity claim
addressable, while the first whole-ledger write retains both inherited
zero-budget rows and emits the new residual row.  Inquiry, answer and
consumer remain separate installed projection faces.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityU8Root

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityCutWorld
open M14SourceGeneratedContributionCapacityCutCompiler
open M14SourceGeneratedContributionCapacityCutRoot
open M14SourceGeneratedContributionCapacityCutActionSource
open M14SourceGeneratedContributionCapacityFailure
open M14SourceGeneratedContributionCapacityU8Lifecycle
open M14SourceGeneratedContributionCapacityU8Compiler

def contributionCapacityU8DefaultEntryAt
    (oldVisit : OldVisit) :
    (indexedSupport : (CapacityU8NAt oldVisit).Support) →
      OpenResponsibilityAt (CapacityU8NAt oldVisit) indexedSupport
  | .inl oldSupport =>
      ⟨.inl (contributionCapacityCutDefaultEntryAt
        (capacityActionRootedAt oldVisit) oldSupport).1,
        (contributionCapacityCutDefaultEntryAt
          (capacityActionRootedAt oldVisit) oldSupport).2⟩
  | .inr _direction => contributionCapacityU8GeneratedResidual oldVisit

def contributionCapacityU8TransferDispositionAt
    (oldVisit : OldVisit)
    (indexedSupport : (CutN (capacityActionRootedAt oldVisit)).Support) :
    (CutN (capacityActionRootedAt oldVisit)).DispositionAt
      indexedSupport .transfer := by
  rcases indexedSupport with ⟨oldSupport, cutPhase⟩
  rcases oldSupport with ⟨worldSupport, mergePhase⟩
  rcases worldSupport with ⟨cofaceSupport, lossPhase⟩
  cases cofaceSupport with
  | inl oldSupport => exact ()
  | inr direction =>
      cases direction
      exact GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget ()

def contributionCapacityRevisedU7
    (oldVisit : OldVisit) : U7ProducerCalculus (CapacityU8NAt oldVisit) where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

def contributionCapacityRevisedU7Source
    (oldVisit : OldVisit) :
    U7ActualSuccessorSource (CapacityU8NAt oldVisit)
      (contributionCapacityRevisedU7 oldVisit) where
  EventAt := SourceGeneratedU7DemandAt
    (contributionCapacityRevisedU7 oldVisit)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := fun {support} {_obstruction} {_demand} _event =>
    contributionCapacityU8DefaultEntryAt oldVisit support

def contributionCapacityRevisedCalculus
    (oldVisit : OldVisit) :
    U7ObstructionEvolutionCalculus (CapacityU8NAt oldVisit)
      (contributionCapacityRevisedU7 oldVisit) where
  source := contributionCapacityRevisedU7Source oldVisit
  compile := by
    intro indexedSupport indexedObstruction demand event
    cases indexedSupport with
    | inl oldSupport =>
        let receipt := contributionCapacityU8TransferDispositionAt
          oldVisit oldSupport
        exact
          { disposition := .redirected ⟨receipt, rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred receipt rfl rfl
                (Nat.le_refl _), rfl⟩ }
    | inr direction =>
        cases direction
        let oldReceipt := contributionCapacityU8TransferDispositionAt
          oldVisit
          (contributionCapacityCutTargetSupport
            (capacityActionRootedAt oldVisit))
        let receipt :=
          GeneratedMinimalCofaceAt.CofaceTargetDispositionAt.ofTarget
            (generated := CapacityCofaceAt oldVisit) oldReceipt
        exact
          { disposition := .redirected ⟨receipt, rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred receipt rfl rfl
                (Nat.le_refl _), rfl⟩ }

def contributionCapacityRevisedTheory
    (oldVisit : OldVisit) : TheoryState (CapacityU8NAt oldVisit) :=
  TheoryState.rootSemantic (CapacityU8NAt oldVisit)

def contributionCapacityRevisedInquiryAudit
    (oldVisit : OldVisit) :
    SourceNativeInquiryFrontAuditAt
      (contributionCapacityRevisedU7 oldVisit)
      (contributionCapacityRevisedCalculus oldVisit)
      (contributionCapacityRevisedTheory oldVisit)
      (CapacityCofaceAt oldVisit).cofaceSupport :=
  .answered

inductive ContributionCapacityU8Projection
  | ledgerLifecycle
  | inquiry
  | answer
  | consumer (entryIndex : Fin 3)

def ContributionCapacityU8RootPayloadAt
    (oldVisit : OldVisit)
    {current : (CapacityU8VAt oldVisit).Current}
    (occurrence :
      (contributionCapacityU8Source oldVisit).toRootSource.actual.OccurrenceAt
        current) : Type :=
  SourceNativeLedgerEvolutionAt (contributionCapacityU8Source oldVisit)
      occurrence ×
    ((entry : OpenResponsibilityAt (CapacityU8NAt oldVisit)
      ((contributionCapacityU8Source oldVisit).toRootSource.account.supportOf
        occurrence)) →
      AdmittedObligation (ContributionCapacityU8LifecycleV oldVisit))

def contributionCapacityU8ProjectionLaw
    (oldVisit : OldVisit) :
    SourceNativeProjectionLaw
      (contributionCapacityU8RestructuringSource oldVisit).toLedgerSource where
  Projection := ContributionCapacityU8Projection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence _ =>
    match projection with
    | .ledgerLifecycle =>
        ContributionCapacityU8RootPayloadAt oldVisit occurrence
    | .inquiry => SourceNativeInquiryCompilationTokenAt
        (contributionCapacityU8GeneratedResidual oldVisit) ()
        (ULift.up.{1, 0} occurrence)
        (contributionCapacityRevisedInquiryAudit oldVisit) PUnit
    | .answer => PUnit
    | .consumer entryIndex => SourceNativeInquiryAnswerConsumerTokenAt
        () (ULift.up.{1, 0} occurrence)
        (contributionCapacityU8EntryAt oldVisit entryIndex) PUnit.unit
  project := fun projection {_current} occurrence _ => by
    cases projection with
    | ledgerLifecycle =>
        exact
          ⟨(contributionCapacityU8LedgerCompiler oldVisit).compile occurrence,
            fun entry => contributionCapacityU8ObligationAt oldVisit
              occurrence.2.materialWitness entry⟩
    | inquiry => exact .canonical PUnit.unit
    | answer => exact PUnit.unit
    | consumer _entryIndex => exact .canonical

def contributionCapacityU8AuthoritySource
    (oldVisit : OldVisit) :
    SourceNativeAuthoritySource (CapacityU8NAt oldVisit)
      (CapacityU8VAt oldVisit) where
  restructuringSource := contributionCapacityU8RestructuringSource oldVisit
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal
      (contributionCapacityU8RestructuringSource oldVisit)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := contributionCapacityRevisedTheory oldVisit
  projectionLaw := contributionCapacityU8ProjectionLaw oldVisit

def contributionCapacityU8AuthoritativeRoot
    (oldVisit : OldVisit) :
    SourceNativeAuthoritativeRootClosure (CapacityU8NAt oldVisit)
      (CapacityU8VAt oldVisit) where
  source := contributionCapacityU8AuthoritySource oldVisit
  emitted := contributionCapacityU8Emitted oldVisit
  compiler_commutes := fun _ => rfl

def contributionCapacityU8LivingRoot
    (oldVisit : OldVisit) :
    SourceNativeLivingRootClosure (CapacityU8NAt oldVisit)
      (CapacityU8VAt oldVisit) :=
  (contributionCapacityU8AuthoritativeRoot oldVisit)
    |>.toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem contributionCapacityU8Root_lawSurface_exact
    (oldVisit : OldVisit) :
    (contributionCapacityU8LivingRoot oldVisit).source.base.lawSurface =
      TheoryState.rootSemantic (CapacityU8NAt oldVisit) :=
  rfl

/-! ## Exact old-successor occurrence seam -/

def contributionCapacityU8OccurrencePresentation
    (oldVisit : OldVisit) :
    ConstructivePresentation
      ((CapacityRootAt oldVisit).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
        (capacityRootedFailureAt oldVisit).oldSuccessor.next)
      ((contributionCapacityU8AuthoritativeRoot oldVisit).toRoot.actual.OccurrenceAt
        (contributionCapacityU8AuthoritativeRoot oldVisit).toRoot.source.initial) where
  forward := fun _ => contributionCapacityU8Emitted oldVisit (0 : Nat)
  backward := fun _ =>
    (CapacityRootAt oldVisit).emitted
      (capacityRootedFailureAt oldVisit).oldSuccessor.next
  backward_forward := by
    intro occurrence
    exact (contributionCapacityCutOccurrence_eq_emitted
      (capacityActionRootedAt oldVisit) occurrence).symm
  forward_backward := by
    intro occurrence
    exact (contributionCapacityU8Occurrence_eq_emitted
      oldVisit occurrence).symm

@[simp] theorem contributionCapacityU8Occurrence_commutes
    (oldVisit : OldVisit) :
    (contributionCapacityU8OccurrencePresentation oldVisit).forward
        ((CapacityRootAt oldVisit).emitted
          (capacityRootedFailureAt oldVisit).oldSuccessor.next) =
      (contributionCapacityU8AuthoritativeRoot oldVisit).emitted
        (contributionCapacityU8AuthoritativeRoot oldVisit).toRoot.source.initial :=
  rfl

/-! ## First-write rows and authority -/

abbrev ContributionCapacityU8RootVisitAt (oldVisit : OldVisit) :=
  SourceNativeTemporalVisitAt
    (contributionCapacityU8LivingRoot oldVisit).toAuthoritativeRoot.toLedgerRoot

abbrev contributionCapacityU8InitialVisit
    (oldVisit : OldVisit) : ContributionCapacityU8RootVisitAt oldVisit :=
  .finite
    (contributionCapacityU8LivingRoot oldVisit).toAuthoritativeRoot.toRoot.initialVisit

def contributionCapacityU8InitialGenerated
    (oldVisit : OldVisit) :=
  (contributionCapacityU8LivingRoot oldVisit).toAuthoritativeRoot.toLedgerRoot
    |>.generatedAtTemporalVisit (contributionCapacityU8InitialVisit oldVisit)

def contributionCapacityU8InheritedContributionRow
    (oldVisit : OldVisit) :
    (contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
      (contributionCapacityU8InheritedContribution oldVisit) :=
  ((contributionCapacityU8InitialGenerated oldVisit).canonicalGeneratedEntryRow?
    (contributionCapacityU8InheritedContribution oldVisit)).get (by rfl)

def contributionCapacityU8InheritedObstructionRow
    (oldVisit : OldVisit) :
    (contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
      (contributionCapacityU8InheritedObstruction oldVisit) :=
  ((contributionCapacityU8InitialGenerated oldVisit).canonicalGeneratedEntryRow?
    (contributionCapacityU8InheritedObstruction oldVisit)).get (by rfl)

def contributionCapacityU8GeneratedResidualRow
    (oldVisit : OldVisit) :
    (contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
      (contributionCapacityU8GeneratedResidual oldVisit) :=
  ((contributionCapacityU8InitialGenerated oldVisit).canonicalGeneratedEntryRow?
    (contributionCapacityU8GeneratedResidual oldVisit)).get (by rfl)

def contributionCapacityU8OldEntryRows
    (oldVisit : OldVisit)
    (oldEntry : OpenResponsibilityAt
      (CutN (capacityActionRootedAt oldVisit))
      ((CapacityRootAt oldVisit).toAuthoritativeRoot.toRoot.supportAt
        (capacityRootedFailureAt oldVisit).oldSuccessor.next)) :
    (contributionCapacityU8InitialGenerated oldVisit).GeneratedEntryRowAt
      ((CapacityCofaceAt oldVisit).cofaceLedgerRetract.forward oldEntry) := by
  rcases oldEntry with ⟨oldResponsibility, isOpen⟩
  rcases isOpen with contribution | obstruction
  · rcases contribution.down with ⟨support_eq, responsibility_eq⟩
    cases support_eq
    cases responsibility_eq
    exact contributionCapacityU8InheritedContributionRow oldVisit
  · rcases obstruction.down with ⟨support_eq, responsibility_eq⟩
    cases support_eq
    cases responsibility_eq
    exact contributionCapacityU8InheritedObstructionRow oldVisit

def contributionCapacityU8FirstWrite
    (oldVisit : OldVisit) :
    CanonicalFirstRootWriteAt
      (contributionCapacityU8AuthoritativeRoot oldVisit).toLedgerRoot :=
  PUnit.unit

end
end M14SourceGeneratedContributionCapacityU8Root
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Root.contributionCapacityU8LivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Root.contributionCapacityU8OldEntryRows
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityU8Root.contributionCapacityU8FirstWrite

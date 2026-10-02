import H0mework.Versions.R2.Foundation.Source.SequentialAction
import H0mework.Realization.Audit.DebtFirstWrite
import H0mework.Foundation.Responsibility.LivingLawRootGeneratedDebtActivationJointLedgerKernel

/-! Actual debt admission retains every old row and generates one fresh row
from an existing strict Step. It is distinct from the no-fresh transporter. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootInquiryCompletion

open DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite

universe u

noncomputable section

/-- The target is a complete source produced at one exact old event. Birth is
computed from `stepEvent`; neither a coverage classifier nor a terminal enters. -/
structure SourceNativeDebtAdmissionActualActionTargetAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (sourceRoot : SourceNativeLivingRootClosure N V)
    (sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot)
    (sourceEvent : ExactTemporalCausalRootEventAt sourceRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit)
    (sourceEntry : OpenResponsibilityAt N
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current)))
    (_sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot sourceVisit sourceEntry) :
    Type (u + 9) where
  law : DebtActivationLaw.{u}
  sourceState : law.DebtState
  stepEvent : SourceFixedDebtAdmissionEventAt law sourceState
  sourceSuccessor : SourceNativeLedgerGeneratedSuccessorAt sourceEvent.occurrence sourceEvent.wholeLedgerWriteBack
  TargetV : Vocabulary.{u}
  targetRoot : SourceNativeLivingRootClosure (ExtendedNetwork N law) TargetV
  initialSupport_eq :
    targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (targetRoot.emitted targetRoot.toAuthoritativeRoot.toRoot.source.initial) =
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        sourceEvent.occurrence, some sourceState)
  initialOldRow : (entry : OpenResponsibilityAt N
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        sourceEvent.occurrence)) →
    (targetRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
      (initialSupport_eq.symm ▸ oldEntry (law := law) (state? := some sourceState) entry)
  initialBornRow :
    (targetRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit)).GeneratedEntryRowAt
      (initialSupport_eq.symm ▸ debtEntry (N := N) (law := law)
        (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
          sourceEvent.occurrence) sourceState)
  firstSuccessor : SourceNativeLedgerGeneratedSuccessorAt
    (targetRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit)).occurrence
    (targetRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit)).wholeLedgerWriteBack
  firstSupport_eq :
    targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        firstSuccessor.targetOccurrence =
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        sourceSuccessor.targetOccurrence, some stepEvent.target)
  firstDestination_heq : HEq firstSuccessor.ledgerEvolution.destination
    (jointStepLedgerEvolution sourceSuccessor.ledgerEvolution sourceEntry stepEvent.step).destination
  oldProjection : sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection →
    targetRoot.toAuthoritativeRoot.source.projectionLaw.Projection
  oldProjection_injective : Function.Injective oldProjection
  oldOutcome_heq : (projection : sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection) →
    HEq (targetRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt (oldProjection projection)
      (targetRoot.emitted targetRoot.toAuthoritativeRoot.toRoot.source.initial))
      (sourceRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection sourceEvent.occurrence)
  canonical_targetNextVisit_eq :
    let targetEntry := initialSupport_eq.symm ▸
      oldEntry (law := law) (state? := some sourceState) sourceEntry
    let targetAuthority := SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
      targetRoot targetEntry (initialOldRow sourceEntry)
    (targetRoot.generatedCausalEntryAnswerAndNextAt
      (.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit) targetEntry targetAuthority).nextCurrent =
      ⟨TargetV, targetRoot.toAuthoritativeRoot,
        (SourceNativeTemporalVisitAt.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit).next
          firstSuccessor.next_eq⟩
  Answer : Type u
  answer : Answer
  Receipt : Answer → Type (u + 3)
  receipt : Receipt answer

namespace SourceNativeDebtAdmissionActualActionTargetAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {sourceRoot : SourceNativeLivingRootClosure N V}
  {sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot}
  {sourceEvent : ExactTemporalCausalRootEventAt sourceRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit}
  {sourceEntry : OpenResponsibilityAt N
    (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (sourceRoot.emitted sourceVisit.current))}
  {sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot sourceVisit sourceEntry}
variable (target : SourceNativeDebtAdmissionActualActionTargetAt
  sourceRoot sourceVisit sourceEvent sourceEntry sourceAuthority)

abbrev TargetN := ExtendedNetwork N target.law

def admission : SourceGeneratedDebtAdmissionFirstWriteAt
    (N := N) (law := target.law)
    (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      sourceEvent.occurrence) target.stepEvent :=
  DebtAdmissionFirstWrite.generate _ target.stepEvent

def targetInitialVisit : SourceNativeTemporalVisitAt target.targetRoot.toAuthoritativeRoot.toLedgerRoot :=
  .finite target.targetRoot.toAuthoritativeRoot.toRoot.initialVisit

def translatedSourceEntry : OpenResponsibilityAt target.TargetN
    (target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (target.targetRoot.emitted target.targetRoot.toAuthoritativeRoot.toRoot.source.initial)) :=
  target.initialSupport_eq.symm ▸ oldEntry (law := target.law) (state? := some target.sourceState) sourceEntry

def initialAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt target.targetRoot
    target.targetInitialVisit target.translatedSourceEntry :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    target.targetRoot target.translatedSourceEntry (target.initialOldRow sourceEntry)

def bornEntry : OpenResponsibilityAt target.TargetN
    (target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (target.targetRoot.emitted target.targetRoot.toAuthoritativeRoot.toRoot.source.initial)) :=
  target.initialSupport_eq.symm ▸ target.admission.initialEntry

def bornAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt target.targetRoot
    target.targetInitialVisit target.bornEntry :=
  SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
    target.targetRoot target.bornEntry target.initialBornRow

/-- Old/fresh provenance is obtained by dependent elimination of the actual
extended carrier, not from an external classification or coverage premise. -/
def InitialOriginAt
    (entry : OpenResponsibilityAt target.TargetN
      (target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (target.targetRoot.emitted target.targetRoot.toAuthoritativeRoot.toRoot.source.initial))) : Type u :=
  (Sigma fun old : OpenResponsibilityAt N
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        sourceEvent.occurrence) =>
    ULift.{u, 0} (PLift (entry = target.initialSupport_eq.symm ▸
      oldEntry (law := target.law) (state? := some target.sourceState) old))) ⊕
    ULift.{u, 0} (PLift (entry = target.bornEntry))

def initialOrigin (entry : OpenResponsibilityAt target.TargetN
    (target.targetRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (target.targetRoot.emitted target.targetRoot.toAuthoritativeRoot.toRoot.source.initial))) :
    target.InitialOriginAt entry := by
  have back : target.initialSupport_eq.symm ▸ (target.initialSupport_eq ▸ entry) = entry := by
    exact Eq.recOn target.initialSupport_eq rfl
  generalize activeEq : target.initialSupport_eq ▸ entry = active at back
  rcases active with ⟨responsibility, opened⟩
  cases responsibility with
  | inl old => exact .inl ⟨⟨old, opened⟩, ⟨⟨back.symm⟩⟩⟩
  | inr debt =>
      rcases opened with ⟨⟨debtEq⟩⟩
      subst debt
      exact .inr ⟨⟨back.symm⟩⟩

def targetAnswerAndNext := target.targetRoot.generatedCausalEntryAnswerAndNextAt
  target.targetInitialVisit target.translatedSourceEntry target.initialAuthority

def targetVisit : SourceNativeTemporalVisitAt target.targetRoot.toAuthoritativeRoot.toLedgerRoot :=
  target.targetInitialVisit.next target.firstSuccessor.next_eq

theorem targetAnswerAndNext_next_eq : target.targetAnswerAndNext.nextCurrent =
    ⟨target.TargetV, target.targetRoot.toAuthoritativeRoot, target.targetVisit⟩ :=
  target.canonical_targetNextVisit_eq

end SourceNativeDebtAdmissionActualActionTargetAt

/-- A fixed source program owns the complete born source before the inquiry
emitter. Its operational input is only the exact old occurrence. -/
structure SourceNativeDebtAdmissionActualActionProgramAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (sourceRoot : SourceNativeLivingRootClosure N V)
    (sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot)
    (sourceEntry : OpenResponsibilityAt N
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current)))
    (_sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot sourceVisit sourceEntry) :
    Type (u + 10) where
  targetAt : (sourceEvent : ExactTemporalCausalRootEventAt
    sourceRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit) →
    SourceNativeDebtAdmissionActualActionTargetAt sourceRoot sourceVisit sourceEvent sourceEntry _sourceAuthority

structure SourceGeneratedDebtAdmissionActualActionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {sourceRoot : SourceNativeLivingRootClosure N V}
    {sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot}
    {sourceEntry : OpenResponsibilityAt N
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current))}
    {sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot sourceVisit sourceEntry}
    (program : SourceNativeDebtAdmissionActualActionProgramAt sourceRoot sourceVisit sourceEntry sourceAuthority)
    (sourceEvent : ExactTemporalCausalRootEventAt sourceRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit) :
    Type (u + 10) where
  private mk ::

namespace SourceNativeDebtAdmissionActualActionProgramAt

def generate
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {sourceRoot : SourceNativeLivingRootClosure N V}
    {sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot}
    {sourceEntry : OpenResponsibilityAt N
      (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (sourceRoot.emitted sourceVisit.current))}
    {sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot sourceVisit sourceEntry}
    (program : SourceNativeDebtAdmissionActualActionProgramAt sourceRoot sourceVisit sourceEntry sourceAuthority)
    (sourceEvent : ExactTemporalCausalRootEventAt sourceRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit) :
    SourceGeneratedDebtAdmissionActualActionAt program sourceEvent := .mk

end SourceNativeDebtAdmissionActualActionProgramAt

namespace SourceGeneratedDebtAdmissionActualActionAt

variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
  {sourceRoot : SourceNativeLivingRootClosure N V}
  {sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot}
  {sourceEntry : OpenResponsibilityAt N
    (sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (sourceRoot.emitted sourceVisit.current))}
  {sourceAuthority : SourceNativeLivingTemporalCausalEntryAuthorityAt sourceRoot sourceVisit sourceEntry}
  {program : SourceNativeDebtAdmissionActualActionProgramAt sourceRoot sourceVisit sourceEntry sourceAuthority}
  {sourceEvent : ExactTemporalCausalRootEventAt sourceRoot.toAuthoritativeRoot.toLedgerRoot sourceVisit}

def target (_generated : SourceGeneratedDebtAdmissionActualActionAt program sourceEvent) :=
  program.targetAt sourceEvent

def answer (generated : SourceGeneratedDebtAdmissionActualActionAt program sourceEvent) :
    generated.target.Answer := generated.target.answer

def receipt (generated : SourceGeneratedDebtAdmissionActualActionAt program sourceEvent) :
    generated.target.Receipt generated.answer := generated.target.receipt

end SourceGeneratedDebtAdmissionActualActionAt

end
end RootInquiryCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

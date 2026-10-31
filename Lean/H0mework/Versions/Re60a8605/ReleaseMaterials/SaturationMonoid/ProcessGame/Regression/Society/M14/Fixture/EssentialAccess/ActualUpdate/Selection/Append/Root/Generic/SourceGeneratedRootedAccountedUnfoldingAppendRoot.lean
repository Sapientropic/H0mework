import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.Root.Generic.SourceGeneratedRootedAccountedUnfoldingAppendLedger
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.U8.Revised.Inquiry.SourceGeneratedCriticalEventSelectionRevisedInquiry

/-!
# Polymorphic rooted-accounted-unfolding append root

This is the target-local root surface over the unique polymorphic append
ledger.  It installs inquiry, answer and consumer faces and transports every
source projection at the exact predecessor occurrence.  The target current
is still generated only by the first whole-ledger write; it is not stored as
the new source initial and no selection, action or future table is accepted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedRootedAccountedUnfoldingAppendRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedCriticalEventSelectionRevisedLedger
open M14SourceGeneratedCriticalEventSelectionRevisedInquiry
open M14SourceGeneratedRootedAccountedUnfoldingAppendLedger

abbrev rootedAppendTheory := revisedInquiryTheory

inductive RootedAppendLocalProjection
  | ledger
  | inquiry
  | answer
  | consumer

abbrev RootedAppendProjection (InheritedProjection : Type) :=
  RootedAppendLocalProjection ⊕ InheritedProjection

namespace RootedAppendProjection

def ledger {InheritedProjection : Type} :
    RootedAppendProjection InheritedProjection :=
  .inl .ledger

def inquiry {InheritedProjection : Type} :
    RootedAppendProjection InheritedProjection :=
  .inl .inquiry

def answer {InheritedProjection : Type} :
    RootedAppendProjection InheritedProjection :=
  .inl .answer

def consumer {InheritedProjection : Type} :
    RootedAppendProjection InheritedProjection :=
  .inl .consumer

def inherited {InheritedProjection : Type} (projection : InheritedProjection) :
    RootedAppendProjection InheritedProjection :=
  .inr projection

end RootedAppendProjection

def rootedAppendInquiryEntryAt {Atom : Type}
    (_current : RootedAccountedUnfolding Atom) :
    OpenResponsibilityAt NewN minimalCoface.cofaceSupport :=
  newRevisedEntry

def rootedAppendInquiryAuditAt {Atom : Type}
    (_current : RootedAccountedUnfolding Atom) :
    SourceNativeInquiryFrontAuditAt revisedInquiryU7 revisedInquiryCalculus
      revisedInquiryTheory minimalCoface.cofaceSupport :=
  .answered

def rootedAppendProjectionLaw
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom) :
    SourceNativeProjectionLaw
      (rootedAppendRestructuringSource prior nextAtom).toLedgerSource where
  Projection := RootedAppendProjection
    sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection
  ActiveAt := fun projection {_current} _occurrence =>
    match projection with
    | .inl .ledger => PUnit
    | .inl .inquiry => PUnit
    | .inl .answer => PUnit
    | .inl .consumer => PUnit
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.ActiveAt
          oldProjection sourceOccurrence
  InactiveAt := fun projection {_current} _occurrence =>
    match projection with
    | .inl .ledger => PEmpty
    | .inl .inquiry => PEmpty
    | .inl .answer => PEmpty
    | .inl .consumer => PEmpty
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.InactiveAt
          oldProjection sourceOccurrence
  classify := fun projection {_current} _occurrence =>
    match projection with
    | .inl .ledger => .inl PUnit.unit
    | .inl .inquiry => .inl PUnit.unit
    | .inl .answer => .inl PUnit.unit
    | .inl .consumer => .inl PUnit.unit
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.classify
          oldProjection sourceOccurrence
  PayloadAt := fun projection {current} occurrence active =>
    match projection with
    | .inl .ledger =>
        SourceNativeLedgerEvolutionAt
          (rootedAppendSource prior nextAtom) occurrence
    | .inl .inquiry =>
        SourceNativeInquiryCompilationTokenAt
          (rootedAppendInquiryEntryAt current) ()
          (ULift.up.{1, 0} occurrence)
          (rootedAppendInquiryAuditAt current) PUnit
    | .inl .answer => PUnit
    | .inl .consumer =>
        SourceNativeInquiryAnswerConsumerTokenAt ()
          (ULift.up.{1, 0} occurrence)
          (rootedAppendInquiryEntryAt current) PUnit.unit
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.PayloadAt
          oldProjection sourceOccurrence active
  project := fun projection {_current} occurrence active =>
    match projection with
    | .inl .ledger =>
        (rootedAppendLedgerCompiler prior nextAtom).compile occurrence
    | .inl .inquiry => .canonical PUnit.unit
    | .inl .answer => PUnit.unit
    | .inl .consumer => .canonical
    | .inr oldProjection =>
        sourceRoot.toAuthoritativeRoot.source.projectionLaw.project
          oldProjection sourceOccurrence active

theorem rootedAppendInheritedProjection_outcome_exact
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom)
    (projection :
      sourceRoot.toAuthoritativeRoot.source.projectionLaw.Projection)
    {current : (RootedAppendVAt prior nextAtom).Current}
    (occurrence :
      (rootedAppendSource prior nextAtom).toRootSource.actual.OccurrenceAt
        current) :
    HEq ((rootedAppendProjectionLaw sourceRoot sourceOccurrence prior nextAtom
      ).outcomeAt (RootedAppendProjection.inherited projection) occurrence)
      (sourceRoot.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        projection sourceOccurrence) := by
  unfold SourceNativeProjectionLaw.outcomeAt
  dsimp only [rootedAppendProjectionLaw, RootedAppendProjection.inherited]
  generalize classifier_eq :
    sourceRoot.toAuthoritativeRoot.source.projectionLaw.classify
      projection sourceOccurrence = classified
  cases classified <;> exact HEq.rfl

def rootedAppendAuthoritySource
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom) :
    SourceNativeAuthoritySource NewN (RootedAppendVAt prior nextAtom) where
  restructuringSource := rootedAppendRestructuringSource prior nextAtom
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (rootedAppendRestructuringSource prior nextAtom)
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := rootedAppendTheory
  projectionLaw := rootedAppendProjectionLaw sourceRoot sourceOccurrence
    prior nextAtom

def rootedAppendLivingRoot
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom) :
    SourceNativeLivingRootClosure NewN (RootedAppendVAt prior nextAtom) where
  source :=
    { base := rootedAppendAuthoritySource sourceRoot sourceOccurrence prior
        nextAtom
      terminalHandoff :=
        (rootedAppendAuthoritySource sourceRoot sourceOccurrence prior nextAtom
          ).emptyFaithfulTerminalHandoff
            (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := rootedAppendEmitted prior nextAtom
  compiler_commutes := fun _ => rfl

def installedRootedAppendInquiry
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom) :=
  (rootedAppendProjectionLaw sourceRoot sourceOccurrence prior nextAtom).project
    RootedAppendProjection.inquiry (rootedAppendEmitted prior nextAtom
      (rootedAppendedCurrent prior nextAtom)) PUnit.unit

def installedRootedAppendAnswer
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom) :=
  (rootedAppendProjectionLaw sourceRoot sourceOccurrence prior nextAtom).project
    RootedAppendProjection.answer (rootedAppendEmitted prior nextAtom
      (rootedAppendedCurrent prior nextAtom)) PUnit.unit

def installedRootedAppendConsumer
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom) :=
  (rootedAppendProjectionLaw sourceRoot sourceOccurrence prior nextAtom).project
    RootedAppendProjection.consumer (rootedAppendEmitted prior nextAtom
      (rootedAppendedCurrent prior nextAtom)) PUnit.unit

theorem installedRootedAppendFaces_exact
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom) :
    installedRootedAppendInquiry sourceRoot sourceOccurrence prior nextAtom =
        SourceNativeInquiryCompilationTokenAt.canonical PUnit.unit ∧
      installedRootedAppendAnswer sourceRoot sourceOccurrence prior nextAtom =
        PUnit.unit ∧
      installedRootedAppendConsumer sourceRoot sourceOccurrence prior nextAtom =
        SourceNativeInquiryAnswerConsumerTokenAt.canonical :=
  ⟨rfl, rfl, rfl⟩

theorem rootedAppendRoot_directConsumer
    {Atom : Type}
    {SourceV : ConstructiveRoot.Vocabulary}
    (sourceRoot : SourceNativeLivingRootClosure NewN SourceV)
    {sourceCurrent : SourceV.Current}
    (sourceOccurrence :
      sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
        sourceCurrent)
    (prior : RootedAccountedUnfolding Atom)
    (nextAtom : Atom) :
    (rootedAppendLivingRoot sourceRoot sourceOccurrence prior nextAtom
      ).toAuthoritativeRoot.toRoot.source.initial = prior ∧
      (rootedAppendFirstSuccessor prior nextAtom).targetCurrent =
        rootedAppendedCurrent prior nextAtom ∧
      (rootedAppendedCurrent prior nextAtom).root = nextAtom ∧
      (rootedAppendedCurrent prior nextAtom).branches =
        AccountedBranches.singleton prior ∧
      installedRootedAppendInquiry sourceRoot sourceOccurrence prior nextAtom =
        SourceNativeInquiryCompilationTokenAt.canonical PUnit.unit ∧
      installedRootedAppendAnswer sourceRoot sourceOccurrence prior nextAtom =
        PUnit.unit ∧
      installedRootedAppendConsumer sourceRoot sourceOccurrence prior nextAtom =
        SourceNativeInquiryAnswerConsumerTokenAt.canonical :=
  ⟨rfl, rootedAppendFirstSuccessor_target_exact prior nextAtom, rfl, rfl,
    rfl, rfl, rfl⟩

end
end M14SourceGeneratedRootedAccountedUnfoldingAppendRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRootedAccountedUnfoldingAppendRoot.rootedAppendLivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRootedAccountedUnfoldingAppendRoot.rootedAppendInheritedProjection_outcome_exact
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedRootedAccountedUnfoldingAppendRoot.rootedAppendRoot_directConsumer

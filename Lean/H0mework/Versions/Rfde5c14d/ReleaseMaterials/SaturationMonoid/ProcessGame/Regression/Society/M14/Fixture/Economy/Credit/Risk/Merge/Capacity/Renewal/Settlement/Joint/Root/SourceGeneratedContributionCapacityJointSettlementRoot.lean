import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Compiler.SourceGeneratedContributionCapacityJointSettlementRestructuring
import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Root.SourceGeneratedContributionCapacityPostSettlementRenewalRoot

/-!
# Joint survivor-settlement root and empty-ledger handoff

The action-generated target root first writes the complete translated `Fin 2`
ledger and then emits its exact faithful terminal.  Row material and terminal
receipts remain separate projections.  The terminal handoff stays inside the
same generated network and is fixed to its unique empty support, where a
nonterminal renewal root continues to emit fresh actual-service occurrences.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedContributionCapacityJointSettlementRoot

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedContributionCapacityReopeningWorld
open M14SourceGeneratedContributionCapacityReopeningRoot
open M14SourceGeneratedContributionCapacityJointSettlementWorld
open M14SourceGeneratedContributionCapacityJointSettlementMaterial
open M14SourceGeneratedContributionCapacityJointSettlementCompiler
open M14SourceGeneratedContributionCapacityJointSettlementRestructuring
open M14SourceGeneratedContributionCapacityPostSettlementRenewalCompiler
open M14SourceGeneratedContributionCapacityPostSettlementRenewalRoot

inductive ContributionCapacityJointSettlementProjection
  | ledger
  | material (entryIndex : Fin 2)
  | inquiry (entryIndex : Fin 2)
  | terminal (entryIndex : Fin 2)
  | consumer (entryIndex : Fin 2)

def contributionCapacityJointSettlementU7
    (oldVisit : OldVisit) : U7ProducerCalculus (JointSettlementNAt oldVisit) where
  DemandAt := fun _ => Unit
  generateDemand := fun _ => ()

def contributionCapacityJointSettlementU7Source
    (oldVisit : OldVisit) :
    U7ActualSuccessorSource (JointSettlementNAt oldVisit)
      (contributionCapacityJointSettlementU7 oldVisit) where
  EventAt := SourceGeneratedU7DemandAt
    (contributionCapacityJointSettlementU7 oldVisit)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := fun event => event
  demandEntryAt := by
    intro support obstruction demand event
    cases support with
    | inl oldSupport =>
        exact (contributionCapacityJointSettlementTranslation oldVisit
          ).oldOpenLedger oldSupport |>.forward
            (contributionCapacityReopeningDefaultEntryAt oldVisit oldSupport)
    | inr emptyUnit => cases emptyUnit; exact PEmpty.elim obstruction

def contributionCapacityJointSettlementCalculus
    (oldVisit : OldVisit) :
    U7ObstructionEvolutionCalculus (JointSettlementNAt oldVisit)
      (contributionCapacityJointSettlementU7 oldVisit) where
  source := contributionCapacityJointSettlementU7Source oldVisit
  compile := by
    intro support obstruction demand event
    cases support with
    | inl oldSupport =>
        let receipt := contributionCapacityReopeningTransferDispositionAt
          oldVisit oldSupport.1
        exact
          { disposition := .redirected ⟨receipt, rfl⟩
            demandEntryDisposition :=
              ⟨LedgerEntryEvolutionAt.transferred receipt rfl rfl
                (Nat.le_refl _), rfl⟩ }
    | inr emptyUnit => cases emptyUnit; exact PEmpty.elim obstruction

def contributionCapacityJointSettlementTheory
    (oldVisit : OldVisit) : TheoryState (JointSettlementNAt oldVisit) :=
  TheoryState.rootSemantic (JointSettlementNAt oldVisit)

def contributionCapacityJointSettlementInquiryAudit
    (oldVisit : OldVisit)
    (support : (JointSettlementNAt oldVisit).Support) :
    SourceNativeInquiryFrontAuditAt
      (contributionCapacityJointSettlementU7 oldVisit)
      (contributionCapacityJointSettlementCalculus oldVisit)
      (contributionCapacityJointSettlementTheory oldVisit) support :=
  .answered

def contributionCapacityJointSettlementEntryAtOccurrence
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    {current : Bool}
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt current)
    (entryIndex : Fin 2) :
    OpenResponsibilityAt (JointSettlementNAt oldVisit) occurrence.1 := by
  rcases occurrence with ⟨support, event⟩
  cases event
  · exact contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex
  · exact contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex

def contributionCapacityJointSettlementTerminalPayloadAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    {current : Bool}
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt current)
    (entryIndex : Fin 2) : Type :=
  match current with
  | false => PUnit
  | true =>
      (contributionCapacityJointSettlementTerminalPatch oldVisit sourceIndex
        material occurrence).CanonicalGeneratedEntryAt
          (contributionCapacityJointSettlementEntryAtOccurrence oldVisit
            sourceIndex material occurrence entryIndex)

def contributionCapacityJointSettlementTerminalPayload
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    {current : Bool}
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt current)
    (entryIndex : Fin 2) :
    contributionCapacityJointSettlementTerminalPayloadAt oldVisit sourceIndex
      material occurrence entryIndex := by
  cases current with
  | false => exact PUnit.unit
  | true =>
      exact
        (contributionCapacityJointSettlementTerminalPatch oldVisit sourceIndex
          material occurrence).canonicalGeneratedEntryAt
            (contributionCapacityJointSettlementEntryAtOccurrence oldVisit
              sourceIndex material occurrence entryIndex)

abbrev contributionCapacityJointSettlementProjectionLaw
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeProjectionLaw
      (contributionCapacityJointSettlementRestructuringSource oldVisit
        sourceIndex material).toLedgerSource where
  Projection := ContributionCapacityJointSettlementProjection
  ActiveAt := fun _ {_} _ => PUnit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} occurrence _ =>
    match projection with
    | .ledger => SourceNativeLedgerEvolutionAt
        (contributionCapacityJointSettlementSource oldVisit sourceIndex
          material) occurrence
    | .material entryIndex =>
        ContributionCapacityJointSettlementTerminalRowEvidenceAt oldVisit
          sourceIndex material entryIndex
    | .inquiry entryIndex => SourceNativeInquiryCompilationTokenAt
        (contributionCapacityJointSettlementEntryAtOccurrence oldVisit
          sourceIndex material occurrence entryIndex) ()
        (ULift.up.{1, 0} occurrence)
        (contributionCapacityJointSettlementInquiryAudit oldVisit occurrence.1)
        (contributionCapacityJointSettlementTerminalPayloadAt oldVisit
          sourceIndex material occurrence entryIndex)
    | .terminal entryIndex =>
        contributionCapacityJointSettlementTerminalPayloadAt oldVisit
          sourceIndex material occurrence entryIndex
    | .consumer entryIndex => SourceNativeInquiryAnswerConsumerTokenAt ()
        (ULift.up.{1, 0} occurrence)
        (contributionCapacityJointSettlementEntryAtOccurrence oldVisit
          sourceIndex material occurrence entryIndex)
        (contributionCapacityJointSettlementTerminalPayload oldVisit
          sourceIndex material occurrence entryIndex)
  project := by
    intro projection current occurrence active
    cases projection with
    | ledger =>
        exact (contributionCapacityJointSettlementLedgerCompiler oldVisit
          sourceIndex material).compile occurrence
    | material entryIndex =>
        exact contributionCapacityJointSettlementTerminalRowEvidenceAt
          oldVisit sourceIndex material entryIndex
    | inquiry entryIndex =>
        exact .canonical
          (contributionCapacityJointSettlementTerminalPayload oldVisit
            sourceIndex material occurrence entryIndex)
    | terminal entryIndex =>
        exact contributionCapacityJointSettlementTerminalPayload oldVisit
          sourceIndex material occurrence entryIndex
    | consumer entryIndex => exact .canonical

theorem contributionCapacityJointSettlementTerminalExhaustsActualInventory
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    {current : Bool} →
    (occurrence :
      (contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.OccurrenceAt current) →
    (terminal :
      (ContributionCapacityJointSettlementVAt oldVisit).FaithfulTerminalAt
        current) →
    ((contributionCapacityJointSettlementSource oldVisit sourceIndex material)
        |>.toRootSource.actual.compile occurrence) =
      .faithfulTerminal terminal →
    IsEmpty (SourceNativeActualOutgoingEventAt
      (contributionCapacityJointSettlementRestructuringSource oldVisit
        sourceIndex material).toLedgerSource current) := by
  intro current occurrence terminal terminal_eq
  cases current with
  | false => exact nomatch terminal
  | true =>
      constructor
      rintro ⟨outOccurrence, successor⟩
      rcases outOccurrence with ⟨support, event⟩
      cases event
      exact nomatch successor

def contributionCapacityJointSettlementAuthoritySource
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeAuthoritySource (JointSettlementNAt oldVisit)
      (ContributionCapacityJointSettlementVAt oldVisit) where
  restructuringSource :=
    contributionCapacityJointSettlementRestructuringSource oldVisit
      sourceIndex material
  eventInventoryAdmission := .refl
    (contributionCapacityJointSettlementRestructuringSource oldVisit
      sourceIndex material)
    (contributionCapacityJointSettlementTerminalExhaustsActualInventory
      oldVisit sourceIndex material)
  lawSurface := contributionCapacityJointSettlementTheory oldVisit
  projectionLaw := contributionCapacityJointSettlementProjectionLaw oldVisit
    sourceIndex material

def contributionCapacityJointSettlementTerminalHandoff
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeTerminalHandoffLaw
      (contributionCapacityJointSettlementAuthoritySource oldVisit sourceIndex
        material) :=
  SourceNativeTerminalHandoffLaw.create
    (fun {_current} _history {_occurrence} _terminal => Unit)
    (fun {_current} _history {_occurrence} _terminal => ())
    (fun _event => PostSettlementRenewalVAt oldVisit)
    (fun _event =>
      contributionCapacityPostSettlementRenewalAuthoritativeRoot oldVisit
        sourceIndex)
    (fun _event =>
      contributionCapacityPostSettlementRenewalInitialOccurrencePresentation
        oldVisit sourceIndex)
    (by intros; rfl)
    (by intros; rfl)
    (by
      intro current history occurrence terminal event targetEntry
      exact PEmpty.elim targetEntry.2)
    (by
      intro current history occurrence terminal event sourceEntry targetEntry
        sameDebt
      exact PEmpty.elim targetEntry.2)
    (by
      intro current history occurrence terminal event sourceEntry left right
        leftDebt rightDebt
      exact PEmpty.elim left.2)

def contributionCapacityJointSettlementLivingRoot
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeLivingRootClosure (JointSettlementNAt oldVisit)
      (ContributionCapacityJointSettlementVAt oldVisit) where
  source :=
    { base := contributionCapacityJointSettlementAuthoritySource oldVisit
        sourceIndex material
      terminalHandoff := contributionCapacityJointSettlementTerminalHandoff
        oldVisit sourceIndex material }
  emitted := contributionCapacityJointSettlementEmitted oldVisit sourceIndex
    material
  compiler_commutes := by
    intro current
    cases current with
    | false => rfl
    | true => exact True.intro

abbrev ContributionCapacityJointSettlementRootAt
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :=
  contributionCapacityJointSettlementLivingRoot oldVisit sourceIndex material

def contributionCapacityJointSettlementInitialVisit
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeTemporalVisitAt
      ((ContributionCapacityJointSettlementRootAt oldVisit sourceIndex material)
        |>.toAuthoritativeRoot.toLedgerRoot) :=
  .finite ((ContributionCapacityJointSettlementRootAt oldVisit sourceIndex
    material).toAuthoritativeRoot.toRoot.initialVisit)

def contributionCapacityJointSettlementTerminalVisit
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeTemporalVisitAt
      ((ContributionCapacityJointSettlementRootAt oldVisit sourceIndex material)
        |>.toAuthoritativeRoot.toLedgerRoot) :=
  (contributionCapacityJointSettlementInitialVisit oldVisit sourceIndex
    material).next rfl

def contributionCapacityJointSettlementInitialGenerated
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :=
  (ContributionCapacityJointSettlementRootAt oldVisit sourceIndex material)
    |>.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
      (contributionCapacityJointSettlementInitialVisit oldVisit sourceIndex
        material)

def contributionCapacityJointSettlementInitialEntryRow
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex)
    (entryIndex : Fin 2) :
    (contributionCapacityJointSettlementInitialGenerated oldVisit sourceIndex
      material).GeneratedEntryRowAt
        (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex) :=
  ((contributionCapacityJointSettlementInitialGenerated oldVisit sourceIndex
    material).canonicalGeneratedEntryRow?
      (contributionCapacityJointSettlementLiveEntryAt oldVisit entryIndex)
    ).get (by
      refine Fin.cases ?_ (fun tail => ?_) entryIndex
      · rfl
      · change Fin 1 at tail
        have tail_eq : tail = (0 : Fin 1) := Subsingleton.elim _ _
        subst tail
        rfl)

def contributionCapacityJointSettlementFirstSuccessor
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceNativeLedgerGeneratedSuccessorAt
      (contributionCapacityJointSettlementInitialGenerated oldVisit
        sourceIndex material).occurrence
      (contributionCapacityJointSettlementInitialGenerated oldVisit
        sourceIndex material).wholeLedgerWriteBack :=
  PUnit.unit

def contributionCapacityJointSettlementExactTerminal
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    SourceFaithfulTerminalOccurrenceAt
      (ContributionCapacityJointSettlementRootAt oldVisit sourceIndex
        material).source.base
      ((ContributionCapacityJointSettlementRootAt oldVisit sourceIndex
        material).emitted true) where
  terminal := .settled
  structural_eq := rfl
  ledgerEvolution := contributionCapacityJointSettlementTerminalEvolution
    oldVisit sourceIndex material
    (contributionCapacityJointSettlementEmitted oldVisit sourceIndex material
      true)
  generated_eq := rfl

@[simp] theorem contributionCapacityJointSettlementGeneratedHandoff_exact
    (oldVisit : OldVisit) (sourceIndex : Nat)
    (material : JointMaterialAt oldVisit sourceIndex) :
    (ContributionCapacityJointSettlementRootAt oldVisit sourceIndex material
      |>.generatedTerminalHandoffAt
        (contributionCapacityJointSettlementTerminalVisit oldVisit sourceIndex
          material)
        (contributionCapacityJointSettlementExactTerminal oldVisit sourceIndex
          material)) =
      ⟨PostSettlementRenewalVAt oldVisit,
        contributionCapacityPostSettlementRenewalAuthoritativeRoot oldVisit
          sourceIndex,
        contributionCapacityPostSettlementRenewalInitialVisit oldVisit
          sourceIndex⟩ := by
  unfold SourceNativeLivingRootClosure.generatedTerminalHandoffAt
  rfl

end
end M14SourceGeneratedContributionCapacityJointSettlementRoot
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementRoot.contributionCapacityJointSettlementLivingRoot
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementRoot.contributionCapacityJointSettlementExactTerminal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedContributionCapacityJointSettlementRoot.contributionCapacityJointSettlementGeneratedHandoff_exact

import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Coordinates
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Recovery

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionBody
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {event : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
    {TargetN : WorldRelationNetwork.{0}} {TargetV : ConstructiveRoot.Vocabulary.{0}}
    (targetRoot : SourceNativeLivingRootClosure TargetN TargetV)

abbrev SourceSupport := root.toAuthoritativeRoot.toRoot.supportAt visit.current
abbrev TargetSupport := targetRoot.toAuthoritativeRoot.toRoot.supportAt targetRoot.toAuthoritativeRoot.toRoot.source.initial
abbrev SourceEntry := OpenResponsibilityAt N (SourceSupport (root := root) (visit := visit))
abbrev TargetEntry := OpenResponsibilityAt TargetN (TargetSupport targetRoot)
abbrev SourceOccurrence := root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt visit.current
abbrev TargetOccurrence := targetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt targetRoot.toAuthoritativeRoot.toRoot.source.initial
abbrev Generated := targetRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
  (.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit)

local notation "Ledger" => ConstructiveRetract (SourceEntry (root := root) (visit := visit)) (TargetEntry targetRoot)
local notation "CP" => ConstructivePresentation (SourceOccurrence (root := root) (visit := visit)) (TargetOccurrence targetRoot)

structure Values where
  translation : TypedSemanticWorldNetworkTranslationAt N TargetN
  occurrencePresentation : CP
  initialSupport_eq : TargetSupport targetRoot = translation.support.forward (SourceSupport (root := root) (visit := visit))
  initialOpenLedger : Ledger
  initialOpenLedger_heq : HEq initialOpenLedger (translation.oldOpenLedger (SourceSupport (root := root) (visit := visit)))
  row : (Generated targetRoot).GeneratedEntryRowAt (initialOpenLedger.forward entry)
  successor : SourceNativeLedgerGeneratedSuccessorAt (Generated targetRoot).occurrence (Generated targetRoot).wholeLedgerWriteBack

structure Check (values : Values (root := root) (visit := visit) (entry := entry) targetRoot) : Prop where
  occurrence : values.occurrencePresentation.forward event.occurrence = targetRoot.emitted targetRoot.toAuthoritativeRoot.toRoot.source.initial
  responsibility : ∀ sourceEntry, values.translation.responsibility.forward sourceEntry.1 =
    (values.initialOpenLedger.forward sourceEntry).1
  claim : ∀ sourceEntry, values.translation.claim.forward (OpenResponsibilityAt.claim sourceEntry) =
    OpenResponsibilityAt.claim (values.initialOpenLedger.forward sourceEntry)
  budget : ∀ sourceEntry, OpenResponsibilityAt.progressBudget (values.initialOpenLedger.forward sourceEntry) ≤
    OpenResponsibilityAt.progressBudget sourceEntry
  noFresh : ∀ targetEntry, Nonempty (Sigma fun sourceEntry => PLift (values.initialOpenLedger.forward sourceEntry = targetEntry))
  next_eq :
    let targetEntry := values.initialOpenLedger.forward entry
    let targetAuthority := SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow targetRoot targetEntry values.row
    let answerAndNext := targetRoot.generatedCausalEntryAnswerAndNextAt
      (.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit) targetEntry targetAuthority
    answerAndNext.nextCurrent = ⟨TargetV, targetRoot.toAuthoritativeRoot,
      (SourceNativeTemporalVisitAt.finite targetRoot.toAuthoritativeRoot.toRoot.initialVisit).next values.successor.next_eq⟩

structure Body where
  values : Values (root := root) (visit := visit) (entry := entry) targetRoot
  checked : Check (event := event) targetRoot values

def ledgerFromTranslation (translation : TypedSemanticWorldNetworkTranslationAt N TargetN)
    (same : TargetSupport targetRoot = translation.support.forward (SourceSupport (root := root) (visit := visit))) : Ledger :=
  Eq.mp (congrArg (fun support => ConstructiveRetract (SourceEntry (root := root) (visit := visit))
    (OpenResponsibilityAt TargetN support)) same.symm)
      (translation.oldOpenLedger (SourceSupport (root := root) (visit := visit)))

theorem ledgerFromTranslation_heq (translation : TypedSemanticWorldNetworkTranslationAt N TargetN)
    (same : TargetSupport targetRoot = translation.support.forward (SourceSupport (root := root) (visit := visit))) :
    HEq (ledgerFromTranslation targetRoot translation same)
      (translation.oldOpenLedger (SourceSupport (root := root) (visit := visit))) :=
  cast_heq _ _

variable {rank : Ordinal.{0}}
    (oldCoordinates : MotherActionTranslation.Coordinates (rank := rank) N)
    (newCoordinates : MotherActionTranslation.Coordinates (rank := rank) TargetN)
    (oldOccurrence : SourceOccurrence (root := root) (visit := visit) ↪ MotherArenaHigher.Base rank)
    (newOccurrence : TargetOccurrence targetRoot ↪ MotherArenaHigher.Base rank)

local notation "M" => MotherArenaHigher.Material rank

/-- Both value programs are read from material. Ledger/row/next are then
read from their exact original dependency sources; laws stay internal. -/
def form (material : M) : Option (Body (root := root) (visit := visit) (event := event) (entry := entry) targetRoot) :=
  let parts := MotherArenaHigher.split rank material
  (MotherActionTranslation.form oldCoordinates newCoordinates parts.1).bind (fun translation =>
  (MotherArenaAdmission.formPresentationSection (MotherActionTranslation.unitAddress rank)
    (fun _ => oldOccurrence) (fun _ => newOccurrence) parts.2).bind (fun presentations =>
  if same : TargetSupport targetRoot = translation.support.forward (SourceSupport (root := root) (visit := visit)) then
    let ledger := ledgerFromTranslation targetRoot translation same
    ((Generated targetRoot).canonicalGeneratedEntryRow? (ledger.forward entry)).bind (fun row =>
    (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated? (Generated targetRoot).wholeLedgerWriteBack).bind (fun successor =>
      let values : Values (root := root) (visit := visit) (entry := entry) targetRoot :=
        ⟨translation, presentations (), same, ledger, ledgerFromTranslation_heq targetRoot translation same, row, successor⟩
      if checked : Check (event := event) targetRoot values then some ⟨values, checked⟩ else none))
  else none))


theorem every_body (body : Body (root := root) (visit := visit) (event := event) (entry := entry) targetRoot) :
    ∃ material : M, form targetRoot oldCoordinates newCoordinates oldOccurrence newOccurrence material = some body := by
  rcases body with ⟨⟨translation, presentation, support, ledger, ledgerHeq, row, successor⟩, checked⟩
  have ledgerSame : ledgerFromTranslation targetRoot translation support = ledger := eq_of_heq
    ((ledgerFromTranslation_heq targetRoot translation support).trans ledgerHeq.symm)
  subst ledger
  obtain ⟨translationM, translationFormed⟩ := MotherActionTranslation.every_translation
    oldCoordinates newCoordinates translation
  obtain ⟨presentationM, presentationFormed⟩ := MotherArenaAdmission.every_presentation_section
    (MotherActionTranslation.unitAddress rank) (fun _ => oldOccurrence) (fun _ => newOccurrence)
    (fun _ => presentation)
  have rowFormed := MotherNativeAuthority.row_selector_recovers (Generated targetRoot)
    ((ledgerFromTranslation targetRoot translation support).forward entry) row
  have successorFormed := MotherActionRecovery.successor_recovers (Generated targetRoot).wholeLedgerWriteBack successor
  refine ⟨MotherArenaHigher.pack rank (translationM, presentationM), ?_⟩
  simp only [form, MotherArenaHigher.split_pack, translationFormed, Option.bind_some, presentationFormed,
    dif_pos support, rowFormed, successorFormed]
  rw [dif_pos checked]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionBody

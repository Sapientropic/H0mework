import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Coordinates
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Frontier

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open scoped Classical
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {oldWorld : SourceNativeAuthoritativeRootClosure N V}
    {oldVisit : SourceNativeTemporalVisitAt oldWorld.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {oldTheory : TheoryState N}
    {support : N.Support} {obstruction : N.ObstructionAt support}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (rooted : RootedActualExpressibilityFailureAt oldWorld oldVisit U7 failure)
    {NewN : WorldRelationNetwork.{0}} {NewV : ConstructiveRoot.Vocabulary.{0}}
    (newRoot : SourceNativeLivingRootClosure NewN NewV)

abbrev OldSupport := oldWorld.toRoot.supportAt rooted.oldSuccessor.next
abbrev NewSupport := newRoot.toAuthoritativeRoot.toRoot.supportAt newRoot.toAuthoritativeRoot.toRoot.source.initial
abbrev OldEntry := OpenResponsibilityAt N (OldSupport rooted)
abbrev NewEntry := OpenResponsibilityAt NewN (NewSupport newRoot)
abbrev OldOccurrence := oldWorld.toRoot.actual.OccurrenceAt rooted.oldSuccessor.next
abbrev NewOccurrence := newRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt newRoot.toAuthoritativeRoot.toRoot.source.initial
abbrev Generated := newRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit
  (.finite newRoot.toAuthoritativeRoot.toRoot.initialVisit)

abbrev Point (translation : TypedSemanticWorldNetworkTranslationAt N NewN) :=
  Σ entry : NewEntry newRoot, NewN.HoldsAt (NewSupport newRoot) entry.claim ×
    NewN.SemanticChangeAt (NewSupport newRoot) (translation.claim.forward (N.obstructionClaim obstruction)) entry.claim

structure Values where
  translation : TypedSemanticWorldNetworkTranslationAt N NewN
  ledger : ConstructiveRetract (OldEntry rooted) (NewEntry newRoot)
  occurrence : ConstructivePresentation (OldOccurrence rooted) (NewOccurrence newRoot)
  point : Point (obstruction := obstruction) newRoot translation

structure Check (values : Values rooted newRoot) : Prop where
  support : values.translation.support.backward (NewSupport newRoot) = OldSupport rooted
  claim : ∀ oldEntry, values.translation.claim.forward (OpenResponsibilityAt.claim oldEntry) =
    OpenResponsibilityAt.claim (values.ledger.forward oldEntry)
  budget : ∀ oldEntry, OpenResponsibilityAt.progressBudget (values.ledger.forward oldEntry) ≤
    OpenResponsibilityAt.progressBudget oldEntry
  occurrence : values.occurrence.forward (oldWorld.emitted rooted.oldSuccessor.next) =
    newRoot.emitted newRoot.toAuthoritativeRoot.toRoot.source.initial
  zero : values.point.1.progressBudget = 0
  noClaim : IsEmpty (Sigma fun oldClaim : N.Claim => PLift
    (values.translation.claim.forward oldClaim = values.point.1.claim))
  noIncidence : IsEmpty (Sigma fun oldIncidence : N.Incidence => PLift
    (values.translation.incidence.forward oldIncidence = NewN.incidenceAt (NewSupport newRoot)))
  noEntry : IsEmpty (Sigma fun oldEntry : OldEntry rooted => PLift
    (values.ledger.forward oldEntry = values.point.1))

variable {rank : Ordinal.{0}}
    (oldCoordinates : Coordinates (rank := rank) N)
    (newCoordinates : Coordinates (rank := rank) NewN)
    (oldOccurrence : OldOccurrence rooted ↪ MotherArenaHigher.Base rank)
    (newOccurrence : NewOccurrence newRoot ↪ MotherArenaHigher.Base rank)
local notation "M" => MotherArenaHigher.Material rank
local notation "unitCode" => MotherActionTranslation.unitAddress rank

private def prodCode {A C : Type} (left : A ↪ MotherArenaHigher.Base rank)
    (right : C ↪ MotherArenaHigher.Base rank) : A × C ↪ MotherArenaHigher.Base rank where
  toFun point := MotherArenaHigher.pair rank (left point.1, right point.2)
  inj' := by
    intro first last same
    have pairSame := congrArg (MotherArenaHigher.unpair rank) same
    simp only [MotherArenaHigher.unpair_pair] at pairSame
    exact Prod.ext (left.injective (congrArg Prod.fst pairSame)) (right.injective (congrArg Prod.snd pairSame))

def pointCode (translation : TypedSemanticWorldNetworkTranslationAt N NewN) :
    Point (obstruction := obstruction) newRoot translation ↪ MotherArenaHigher.Base rank :=
  MotherArenaObligation.sigmaEmbedding (newCoordinates.network.entry (NewSupport newRoot))
    (fun entry => prodCode (holdsMember newCoordinates (NewSupport newRoot) entry.claim)
      (changeMember newCoordinates (NewSupport newRoot) (translation.claim.forward (N.obstructionClaim obstruction)) entry.claim))

/-- All noncanonical revised values are material graphs, including the
backward ledger program and the actual typed semantic-change witness. -/
def formValues (material : M) : Option (Values rooted newRoot) :=
  let first := MotherArenaHigher.split rank material
  let second := MotherArenaHigher.split rank first.2
  let third := MotherArenaHigher.split rank second.2
  (MotherActionTranslation.form oldCoordinates.network newCoordinates.network first.1).bind (fun translation =>
  (MotherActionRetract.form unitCode (fun _ => oldCoordinates.network.entry (OldSupport rooted))
    (fun _ => newCoordinates.network.entry (NewSupport newRoot)) second.1).bind (fun ledgers =>
  (MotherArenaAdmission.formPresentationSection unitCode (fun _ => oldOccurrence)
    (fun _ => newOccurrence) third.1).bind (fun occurrences =>
  (MotherArenaReceipts.NativeSection.form unitCode
    (fun _ => pointCode newRoot newCoordinates translation) third.2).map (fun points =>
      ⟨translation, ledgers (), occurrences (), points ()⟩))))

theorem every_values (values : Values rooted newRoot) :
    ∃ material : M, formValues rooted newRoot oldCoordinates newCoordinates oldOccurrence newOccurrence material = some values := by
  obtain ⟨translationM, translationFormed⟩ := MotherActionTranslation.every_translation
    oldCoordinates.network newCoordinates.network values.translation
  obtain ⟨ledgerM, ledgerFormed⟩ := MotherActionRetract.every_retract unitCode
    (fun _ => oldCoordinates.network.entry (OldSupport rooted))
    (fun _ => newCoordinates.network.entry (NewSupport newRoot)) (fun _ => values.ledger)
  obtain ⟨occurrenceM, occurrenceFormed⟩ := MotherArenaAdmission.every_presentation_section unitCode
    (fun _ => oldOccurrence) (fun _ => newOccurrence) (fun _ => values.occurrence)
  obtain ⟨pointM, pointFormed⟩ := MotherArenaReceipts.NativeSection.every_section unitCode
    (fun _ => pointCode newRoot newCoordinates values.translation) (fun _ => values.point)
  refine ⟨MotherArenaHigher.pack rank (translationM, MotherArenaHigher.pack rank
    (ledgerM, MotherArenaHigher.pack rank (occurrenceM, pointM))), ?_⟩
  simp only [formValues, MotherArenaHigher.split_pack, translationFormed, ledgerFormed,
    occurrenceFormed, pointFormed, Option.bind_some, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision

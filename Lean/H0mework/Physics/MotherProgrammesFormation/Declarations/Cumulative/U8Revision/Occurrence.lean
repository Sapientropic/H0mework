import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Body
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeAuthority.RowRecovery

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

def assembleOccurrence (values : Values rooted newRoot) (checked : Check rooted newRoot values)
    (firstWrite : CanonicalFirstRootWriteAt newRoot.toAuthoritativeRoot.toLedgerRoot)
    (rows : ∀ oldEntry, (Generated newRoot).GeneratedEntryRowAt (values.ledger.forward oldEntry))
    (newRow : (Generated newRoot).GeneratedEntryRowAt values.point.1) :
    GeneratedTypedSemanticWorldNetworkRevisionAt rooted where
  NewN := NewN
  translation := values.translation
  NewV := NewV
  newLivingRoot := newRoot
  new_support_restricts := checked.support
  oldTargetOpenLedger := values.ledger
  oldTargetOpenClaim_commutes := checked.claim
  oldTargetOpenProgressBudget_not_refilled := checked.budget
  occurrencePresentation := values.occurrence
  occurrence_commutes := checked.occurrence
  firstWrite := firstWrite
  newOnlyEntry := values.point.1
  newOnlyProgressBudget_eq_zero := checked.zero
  revisedClaimHolds := values.point.2.1
  semanticChange := values.point.2.2
  revisedClaim_hasNoOldPreimage := checked.noClaim
  newOnlyIncidence_hasNoOldPreimage := checked.noIncidence
  oldEntryRows := rows
  newOnlyEntry_hasNoOldPreimage := checked.noEntry
  newOnlyEntryRow := newRow

variable {rank : Ordinal.{0}}
    (oldCoordinates : Coordinates (rank := rank) N)
    (newCoordinates : Coordinates (rank := rank) NewN)
    (oldOccurrence : OldOccurrence rooted ↪ MotherArenaHigher.Base rank)
    (newOccurrence : NewOccurrence newRoot ↪ MotherArenaHigher.Base rank)
local notation "M" => MotherArenaHigher.Material rank

/-- First write and every old/new patch row are selected from the actual
revised root's original generated occurrence. -/
def formOccurrence (material : M) : Option (GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :=
  (formValues rooted newRoot oldCoordinates newCoordinates oldOccurrence newOccurrence material).bind (fun values =>
    if checked : Check rooted newRoot values then
      (uniqueMember (A := CanonicalFirstRootWriteAt newRoot.toAuthoritativeRoot.toLedgerRoot)).bind (fun firstWrite =>
        if allRows : ∀ oldEntry, ((Generated newRoot).canonicalGeneratedEntryRow? (values.ledger.forward oldEntry)).isSome then
          ((Generated newRoot).canonicalGeneratedEntryRow? values.point.1).map (fun newRow =>
            assembleOccurrence rooted newRoot values checked firstWrite
              (fun oldEntry => ((Generated newRoot).canonicalGeneratedEntryRow? (values.ledger.forward oldEntry)).get (allRows oldEntry)) newRow)
        else none)
    else none)

omit newRoot oldCoordinates newCoordinates oldOccurrence newOccurrence in
def valuesOf (original : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) : Values rooted original.newLivingRoot where
  translation := original.translation
  ledger := original.oldTargetOpenLedger
  occurrence := original.occurrencePresentation
  point := ⟨original.newOnlyEntry, original.revisedClaimHolds, original.semanticChange⟩

omit newRoot oldCoordinates newCoordinates oldOccurrence newOccurrence in
theorem checkOf (original : GeneratedTypedSemanticWorldNetworkRevisionAt rooted) :
    Check rooted original.newLivingRoot (valuesOf rooted original) :=
  ⟨original.new_support_restricts, original.oldTargetOpenClaim_commutes,
    original.oldTargetOpenProgressBudget_not_refilled, original.occurrence_commutes,
    original.newOnlyProgressBudget_eq_zero, original.revisedClaim_hasNoOldPreimage,
    original.newOnlyIncidence_hasNoOldPreimage, original.newOnlyEntry_hasNoOldPreimage⟩

omit newRoot oldCoordinates newCoordinates oldOccurrence newOccurrence in
theorem every_occurrence (original : GeneratedTypedSemanticWorldNetworkRevisionAt rooted)
    (oldCoordinates : Coordinates (rank := rank) N)
    (newCoordinates : Coordinates (rank := rank) original.NewN)
    (oldOccurrence : OldOccurrence rooted ↪ MotherArenaHigher.Base rank)
    (newOccurrence : NewOccurrence original.newLivingRoot ↪ MotherArenaHigher.Base rank) :
    ∃ material : M, formOccurrence rooted original.newLivingRoot oldCoordinates newCoordinates oldOccurrence newOccurrence material = some original := by
  obtain ⟨material, formed⟩ := every_values rooted original.newLivingRoot oldCoordinates newCoordinates oldOccurrence newOccurrence (valuesOf rooted original)
  have checked := checkOf rooted original
  have allRows : ∀ oldEntry, ((Generated original.newLivingRoot).canonicalGeneratedEntryRow?
      (original.oldTargetOpenLedger.forward oldEntry)).isSome := by
    intro oldEntry
    rw [MotherNativeAuthority.row_selector_recovers _ _ (original.oldEntryRows oldEntry)]
    rfl
  have rowsSame : (fun oldEntry => ((Generated original.newLivingRoot).canonicalGeneratedEntryRow?
      (original.oldTargetOpenLedger.forward oldEntry)).get (allRows oldEntry)) = original.oldEntryRows := by
    funext oldEntry
    exact Option.some.inj ((Option.some_get _).trans
      (MotherNativeAuthority.row_selector_recovers _ _ (original.oldEntryRows oldEntry)))
  refine ⟨material, ?_⟩
  rw [formOccurrence, formed]
  dsimp only [Option.bind_some]
  rw [dif_pos checked, uniqueMember_recovers original.firstWrite]
  dsimp only [Option.bind_some]
  dsimp only [valuesOf]
  erw [dif_pos allRows, MotherNativeAuthority.row_selector_recovers _ _ original.newOnlyEntryRow]
  dsimp only [Option.map_some]
  rw [rowsSame]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision

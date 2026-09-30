import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ActionFields.Assembly
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.ReceiptMaterial.Action

set_option autoImplicit false
set_option maxHeartbeats 3000000
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

local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit event entry authority

/-- Once the original roots supply their actual inverse schemas and
coordinates, one material forms every remaining target value and recovers
the whole original action record. The target enters coverage only. -/
theorem every_target_fields (target : Target) {oldRank : Ordinal.{0}}
    (oldCoordinates : MotherActionTranslation.Coordinates (rank := oldRank) N)
    (newCoordinates : MotherActionTranslation.Coordinates (rank := oldRank) target.TargetN)
    (oldOccurrence : SourceOccurrence (root := root) (visit := visit) ↪ MotherArenaHigher.Base oldRank)
    (newOccurrence : TargetOccurrence target.targetRoot ↪ MotherArenaHigher.Base oldRank) :
    ∃ rank : Ordinal.{3}, ∃ material : MotherReceiptHigher.Material rank,
      ∃ originalAddress : MotherArenaHigher.Base oldRank ↪ MotherReceiptHigher.Base rank,
      ∃ receiptAvailable : (MotherReceiptPayload.formJoint material).isSome,
      ∃ receipt : MotherReceiptPayload.Presentation target.Answer target.Receipt
        ⟨target.answer, target.receipt⟩ ((MotherReceiptPayload.formJoint material).get receiptAvailable),
      ∃ bodyAvailable : (form (event := event) (entry := entry) target.targetRoot oldCoordinates newCoordinates oldOccurrence newOccurrence
        (MotherReceiptPayload.readArena oldRank originalAddress material)).isSome,
        assemble ((form (event := event) (entry := entry) target.targetRoot oldCoordinates newCoordinates oldOccurrence newOccurrence
          (MotherReceiptPayload.readArena oldRank originalAddress material)).get bodyAvailable)
          target.Answer target.Receipt receipt.restrict = target := by
  obtain ⟨bodyMaterial, bodyFormed⟩ := every_body target.targetRoot oldCoordinates newCoordinates
    oldOccurrence newOccurrence (ofTarget target)
  obtain ⟨rank, material, address, receiptAvailable, receipt, originalRecovered, receiptRecovered, _retains⟩ :=
    MotherActionReceipt.every_target_receipt target oldRank bodyMaterial
  have bodyFormed : form (event := event) (entry := entry) target.targetRoot oldCoordinates newCoordinates oldOccurrence newOccurrence
      (MotherReceiptPayload.readArena oldRank address material) = some (ofTarget target) := by
    rw [originalRecovered]
    exact bodyFormed
  have bodyAvailable : (form (event := event) (entry := entry) target.targetRoot oldCoordinates newCoordinates oldOccurrence newOccurrence
      (MotherReceiptPayload.readArena oldRank address material)).isSome := by rw [bodyFormed]; rfl
  have bodySame : (form (event := event) (entry := entry) target.targetRoot oldCoordinates newCoordinates oldOccurrence newOccurrence
      (MotherReceiptPayload.readArena oldRank address material)).get bodyAvailable = ofTarget target :=
    Option.some.inj ((Option.some_get bodyAvailable).trans bodyFormed)
  refine ⟨rank, material, address, receiptAvailable, receipt, bodyAvailable, ?_⟩
  rw [bodySame, receiptRecovered]
  exact assemble_ofTarget target

/-- The actual restored living root is installed as the target field. Its
literal equality transports dependencies; no Equiv is promoted to equality. -/
def assembleRestored (target : Target) (restoredRoot : SourceNativeLivingRootClosure target.TargetN target.TargetV)
    (rootSame : restoredRoot = target.targetRoot)
    (body : Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot)
    (selected : Sigma target.Receipt) : Target :=
  assemble (targetRoot := restoredRoot)
    (Eq.mp (congrArg (Body (root := root) (visit := visit) (event := event) (entry := entry)) rootSame.symm) body)
    target.Answer target.Receipt selected

theorem assembleRestored_root (target : Target) (restoredRoot : SourceNativeLivingRootClosure target.TargetN target.TargetV)
    (rootSame : restoredRoot = target.targetRoot)
    (body : Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot)
    (selected : Sigma target.Receipt) :
    (assembleRestored target restoredRoot rootSame body selected).targetRoot = restoredRoot := rfl

theorem assembleRestored_recovers (target : Target) (restoredRoot : SourceNativeLivingRootClosure target.TargetN target.TargetV)
    (rootSame : restoredRoot = target.targetRoot)
    (body : Body (root := root) (visit := visit) (event := event) (entry := entry) target.targetRoot)
    (bodySame : body = ofTarget target) {rank : Ordinal.{3}} {value : MotherReceiptPayload.Value rank}
    (receipt : MotherReceiptPayload.Presentation target.Answer target.Receipt ⟨target.answer, target.receipt⟩ value) :
    assembleRestored target restoredRoot rootSame body receipt.restrict = target := by
  cases rootSame
  exact target_recovers target body bodySame receipt

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionBody

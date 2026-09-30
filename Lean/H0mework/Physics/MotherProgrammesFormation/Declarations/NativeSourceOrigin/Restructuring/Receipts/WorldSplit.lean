import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.WorldFrames

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherFullCompiler MotherSourcePrograms MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    {p : MotherNativeSourceOrigin.Presentation n v original generated}
    {law : SourceNativeLedgerRestructuringLaw original} {point : Point original}
    {before after : CompleteLiveLedgerAt N} {newBefore newAfter : CompleteLiveLedgerAt G}
    {whole : LedgerWriteEvolutionAt N before after} {image : LedgerWriteEvolutionAt G newBefore newAfter}
    (frame : WorldFrame p law point whole image) (left right : after.Entry)

theorem WorldFrame.split_check_iff (receipt : SplitReceipt law.vocabulary (law.obligationAt point.2 (whole.origin left).1)) :
    SplitCheck (right := right) receipt ↔
      SplitCheck (law := worldLaw p law) (event := (pointEquiv p point).2) (evolution := image)
        (left := frame.after left) (right := frame.after right)
        (splitReceiptCast (frame.origin_obligation left).symm receipt) := by
  let mapped := splitReceiptCast (frame.origin_obligation left).symm receipt
  have sources : mapped.sourceEvent = receipt.sourceEvent := splitCast_source _ receipt
  have children : mapped.children = receipt.children := splitCast_children _ receipt
  have members (entry : after.Entry) :
      ((worldLaw p law).obligationAt (pointEquiv p point).2 (frame.after entry) ∈ mapped.children) =
        (law.obligationAt point.2 entry ∈ receipt.children) :=
    congrArg₂ (fun child children => child ∈ children) (frame.after_obligation entry) children
  have budgets (entry : after.Entry) :
      ((frame.after entry).progressBudget < (image.origin (frame.after left)).1.progressBudget) =
        (entry.progressBudget < (whole.origin left).1.progressBudget) :=
    congrArg₂ (fun (a b : Nat) => a < b) (frame.after_budget entry) (frame.origin_budget left)
  constructor
  · intro checked
    refine {
      sourceEvent_eq := sources.trans (checked.sourceEvent_eq.trans (world_sourceEvent p law point).symm)
      left_member := Eq.mpr (members left) checked.left_member
      right_member := Eq.mpr (members right) checked.right_member
      covers_target := ?_
      budget := ?_
      no_phantom := ?_ }
    · intro entry same
      obtain ⟨entry, rfl⟩ := frame.after.surjective entry
      exact Eq.mpr (members entry) (checked.covers_target entry ((frame.origin_iff entry left).mpr same))
    · intro entry same
      obtain ⟨entry, rfl⟩ := frame.after.surjective entry
      exact Eq.mpr (budgets entry) (checked.budget entry ((frame.origin_iff entry left).mpr same))
    · intro child member
      obtain ⟨entry, entryEq, originEq⟩ := checked.no_phantom child (Eq.mp (congrArg (fun values => child ∈ values) children) member)
      exact ⟨frame.after entry, (frame.after_obligation entry).trans entryEq, (frame.origin_iff entry left).mp originEq⟩
  · intro checked
    refine {
      sourceEvent_eq := sources.symm.trans (checked.sourceEvent_eq.trans (world_sourceEvent p law point))
      left_member := Eq.mp (members left) checked.left_member
      right_member := Eq.mp (members right) checked.right_member
      covers_target := fun entry same => Eq.mp (members entry) (checked.covers_target (frame.after entry) ((frame.origin_iff entry left).mp same))
      budget := fun entry same => Eq.mp (budgets entry) (checked.budget (frame.after entry) ((frame.origin_iff entry left).mp same))
      no_phantom := ?_ }
    intro child member
    obtain ⟨entry, entryEq, originEq⟩ := checked.no_phantom child (Eq.mpr (congrArg (fun values => child ∈ values) children) member)
    obtain ⟨entry, rfl⟩ := frame.after.surjective entry
    exact ⟨entry, (frame.after_obligation entry).symm.trans entryEq, (frame.origin_iff entry left).mpr originEq⟩

def WorldFrame.splitCoverageEquiv {same : (whole.origin left).1 = (whole.origin right).1} :
    SourceNativeSplitCoverageAt law point.2 whole left right same ≃
      SourceNativeSplitCoverageAt (worldLaw p law) (pointEquiv p point).2 image (frame.after left) (frame.after right)
        ((frame.origin_iff left right).mp same) :=
  (splitCoverageBodyEquiv law).trans
    ((Equiv.subtypeEquiv (splitReceiptCast (frame.origin_obligation left).symm) (frame.split_check_iff left right)).trans
      (splitCoverageBodyEquiv (worldLaw p law)).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

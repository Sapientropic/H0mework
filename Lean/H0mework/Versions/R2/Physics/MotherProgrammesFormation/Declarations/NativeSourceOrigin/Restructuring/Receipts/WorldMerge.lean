import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.WorldSplit

set_option autoImplicit false
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
    (frame : WorldFrame p law point whole image) (left right : before.Entry)

theorem WorldFrame.merge_check_iff (receipt : MergeReceipt law.vocabulary) :
    MergeCheck (law := law) (event := point.2) (evolution := whole) (left := left) (right := right) receipt ↔
      MergeCheck (law := worldLaw p law) (event := (pointEquiv p point).2) (evolution := image)
        (left := frame.before left) (right := frame.before right) receipt := by
  have members (entry : before.Entry) :
      ((worldLaw p law).obligationAt (pointEquiv p point).2 (frame.before entry) ∈ receipt.parents) =
        (law.obligationAt point.2 entry ∈ receipt.parents) :=
    congrArg (fun value => value ∈ receipt.parents) (frame.before_obligation entry)
  constructor
  · intro checked
    refine {
      sourceEvent_eq := checked.sourceEvent_eq.trans (world_sourceEvent p law point).symm
      target_eq := checked.target_eq.trans (frame.destination_obligation left).symm
      left_member := Eq.mpr (members left) checked.left_member
      right_member := Eq.mpr (members right) checked.right_member
      covers_source := ?_
      no_phantom := ?_ }
    · intro entry same
      obtain ⟨entry, rfl⟩ := frame.before.surjective entry
      exact Eq.mpr (members entry) (checked.covers_source entry ((frame.destination_iff entry left).mpr same))
    · intro parent member
      obtain ⟨entry, entryEq, destinationEq⟩ := checked.no_phantom parent member
      exact ⟨frame.before entry, (frame.before_obligation entry).trans entryEq, (frame.destination_iff entry left).mp destinationEq⟩
  · intro checked
    refine {
      sourceEvent_eq := checked.sourceEvent_eq.trans (world_sourceEvent p law point)
      target_eq := checked.target_eq.trans (frame.destination_obligation left)
      left_member := Eq.mp (members left) checked.left_member
      right_member := Eq.mp (members right) checked.right_member
      covers_source := fun entry same => Eq.mp (members entry) (checked.covers_source (frame.before entry) ((frame.destination_iff entry left).mp same))
      no_phantom := ?_ }
    intro parent member
    obtain ⟨entry, entryEq, destinationEq⟩ := checked.no_phantom parent member
    obtain ⟨entry, rfl⟩ := frame.before.surjective entry
    exact ⟨entry, (frame.before_obligation entry).symm.trans entryEq, (frame.destination_iff entry left).mpr destinationEq⟩

def WorldFrame.mergeCoverageEquiv {same : (whole.destination left).1 = (whole.destination right).1} :
    SourceNativeMergeCoverageAt law point.2 whole left right same ≃
      SourceNativeMergeCoverageAt (worldLaw p law) (pointEquiv p point).2 image (frame.before left) (frame.before right)
        ((frame.destination_iff left right).mp same) :=
  (mergeCoverageBodyEquiv law).trans
    ((Equiv.subtypeEquiv (Equiv.refl _) (frame.merge_check_iff left right)).trans (mergeCoverageBodyEquiv (worldLaw p law)).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

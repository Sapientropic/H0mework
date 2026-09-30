import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.SplitAcross

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {generated : Sorts} {outputFamilies : Families generated} (ops : Operations generated outputFamilies)
    (sorts : ∀ i, sortsOf law.vocabulary.base i ≃ generated i)
    (families : FamilyMap sorts (familiesOf law.vocabulary) outputFamilies)
    (p : OperationsAcross sorts families (operationsOf law.vocabulary) ops)
    {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {before after : CompleteLiveLedgerAt N} {evolution : LedgerWriteEvolutionAt N before after}
    {left right : before.Entry}

theorem merge_check_iff (receipt : MergeReceipt law.vocabulary) :
    MergeCheck (law := law) (event := event) (evolution := evolution) (left := left) (right := right) receipt ↔
      MergeCheck (law := sourceLaw law ops sorts families p) (event := event) (evolution := evolution) (left := left) (right := right)
        (mergeReceiptEquiv sorts families p receipt) := by
  constructor
  · intro checked
    refine {
      sourceEvent_eq := congrArg (sorts 0) checked.sourceEvent_eq
      target_eq := congrArg (obligationEquiv sorts families p) checked.target_eq
      left_member := (mapped_member_iff (obligationEquiv sorts families p) receipt.parents _).mp checked.left_member
      right_member := (mapped_member_iff (obligationEquiv sorts families p) receipt.parents _).mp checked.right_member
      covers_source := fun entry same => (mapped_member_iff (obligationEquiv sorts families p) receipt.parents _).mp (checked.covers_source entry same)
      no_phantom := ?_ }
    intro parent member
    obtain ⟨old, member, same⟩ := List.mem_map.mp member
    obtain ⟨entry, entryEq, destinationEq⟩ := checked.no_phantom old member
    exact ⟨entry, (congrArg (obligationEquiv sorts families p) entryEq).trans same, destinationEq⟩
  · intro checked
    refine {
      sourceEvent_eq := (sorts 0).injective checked.sourceEvent_eq
      target_eq := (obligationEquiv sorts families p).injective checked.target_eq
      left_member := (mapped_member_iff (obligationEquiv sorts families p) receipt.parents _).mpr checked.left_member
      right_member := (mapped_member_iff (obligationEquiv sorts families p) receipt.parents _).mpr checked.right_member
      covers_source := fun entry same => (mapped_member_iff (obligationEquiv sorts families p) receipt.parents _).mpr (checked.covers_source entry same)
      no_phantom := ?_ }
    intro parent member
    obtain ⟨entry, entryEq, destinationEq⟩ := checked.no_phantom (obligationEquiv sorts families p parent)
      ((mapped_member_iff (obligationEquiv sorts families p) receipt.parents parent).mp member)
    exact ⟨entry, (obligationEquiv sorts families p).injective entryEq, destinationEq⟩

def mergeCoverageBodyEquiv {same : (evolution.destination left).1 = (evolution.destination right).1} :
    SourceNativeMergeCoverageAt law event evolution left right same ≃
      {receipt : MergeReceipt law.vocabulary //
        MergeCheck (law := law) (event := event) (evolution := evolution) (left := left) (right := right) receipt} where
  toFun := fun value => ⟨value.receipt, merge_checked value⟩
  invFun := fun value => mergeFromReceipt value.val value.property
  left_inv := merge_recovers
  right_inv := fun value => by cases value; rfl

def nativeMergeCoverageEquiv {same : (evolution.destination left).1 = (evolution.destination right).1} :
    SourceNativeMergeCoverageAt law event evolution left right same ≃
      SourceNativeMergeCoverageAt (sourceLaw law ops sorts families p) event evolution left right same :=
  (mergeCoverageBodyEquiv law).trans
    ((Equiv.subtypeEquiv (mergeReceiptEquiv sorts families p) (merge_check_iff law ops sorts families p)).trans
      (mergeCoverageBodyEquiv (sourceLaw law ops sorts families p)).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

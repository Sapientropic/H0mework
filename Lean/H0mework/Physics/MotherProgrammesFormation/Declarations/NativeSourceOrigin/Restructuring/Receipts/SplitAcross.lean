import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.ReceiptsAcross

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherRestructuringOrigin MotherObligationOrigin ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

theorem mapped_member_iff {A C : Type} (e : A ≃ C) (values : List A) (value : A) :
    value ∈ values ↔ e value ∈ listEquiv e values := by
  constructor
  · exact fun member => List.mem_map.mpr ⟨value, member, rfl⟩
  · intro member
    obtain ⟨other, member, same⟩ := List.mem_map.mp member
    exact e.injective same ▸ member

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {generated : Sorts} {outputFamilies : Families generated} (ops : Operations generated outputFamilies)
    (sorts : ∀ i, sortsOf law.vocabulary.base i ≃ generated i)
    (families : FamilyMap sorts (familiesOf law.vocabulary) outputFamilies)
    (p : OperationsAcross sorts families (operationsOf law.vocabulary) ops)
    {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {before after : CompleteLiveLedgerAt N} {evolution : LedgerWriteEvolutionAt N before after}
    {left right : after.Entry}

theorem split_check_iff (receipt : SplitReceipt law.vocabulary (law.obligationAt event (evolution.origin left).1)) :
    SplitCheck (right := right) receipt ↔
      SplitCheck (law := sourceLaw law ops sorts families p) (event := event) (evolution := evolution) (left := left) (right := right)
        (splitReceiptEquiv sorts families p (law.obligationAt event (evolution.origin left).1) receipt) := by
  constructor
  · intro checked
    refine {
      sourceEvent_eq := congrArg (sorts 0) checked.sourceEvent_eq
      left_member := (mapped_member_iff (obligationEquiv sorts families p) receipt.children _).mp checked.left_member
      right_member := (mapped_member_iff (obligationEquiv sorts families p) receipt.children _).mp checked.right_member
      covers_target := fun entry same => (mapped_member_iff (obligationEquiv sorts families p) receipt.children _).mp (checked.covers_target entry same)
      budget := checked.budget
      no_phantom := ?_ }
    intro child member
    obtain ⟨old, member, same⟩ := List.mem_map.mp member
    obtain ⟨entry, entryEq, originEq⟩ := checked.no_phantom old member
    exact ⟨entry, (congrArg (obligationEquiv sorts families p) entryEq).trans same, originEq⟩
  · intro checked
    refine {
      sourceEvent_eq := (sorts 0).injective checked.sourceEvent_eq
      left_member := (mapped_member_iff (obligationEquiv sorts families p) receipt.children _).mpr checked.left_member
      right_member := (mapped_member_iff (obligationEquiv sorts families p) receipt.children _).mpr checked.right_member
      covers_target := fun entry same => (mapped_member_iff (obligationEquiv sorts families p) receipt.children _).mpr (checked.covers_target entry same)
      budget := checked.budget
      no_phantom := ?_ }
    intro child member
    obtain ⟨entry, entryEq, originEq⟩ := checked.no_phantom (obligationEquiv sorts families p child)
      ((mapped_member_iff (obligationEquiv sorts families p) receipt.children child).mp member)
    exact ⟨entry, (obligationEquiv sorts families p).injective entryEq, originEq⟩

def splitCoverageBodyEquiv {same : (evolution.origin left).1 = (evolution.origin right).1} :
    SourceNativeSplitCoverageAt law event evolution left right same ≃
      {receipt : SplitReceipt law.vocabulary (law.obligationAt event (evolution.origin left).1) // SplitCheck (right := right) receipt} where
  toFun := fun value => ⟨value.receipt, split_checked value⟩
  invFun := fun value => splitFromReceipt value.val value.property
  left_inv := split_recovers
  right_inv := fun value => by cases value; rfl

def nativeSplitCoverageEquiv {same : (evolution.origin left).1 = (evolution.origin right).1} :
    SourceNativeSplitCoverageAt law event evolution left right same ≃
      SourceNativeSplitCoverageAt (sourceLaw law ops sorts families p) event evolution left right same :=
  (splitCoverageBodyEquiv law).trans
    ((Equiv.subtypeEquiv (splitReceiptEquiv sorts families p (law.obligationAt event (evolution.origin left).1))
      (split_check_iff law ops sorts families p)).trans (splitCoverageBodyEquiv (sourceLaw law ops sorts families p)).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

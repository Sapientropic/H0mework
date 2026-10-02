import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {before after : CompleteLiveLedgerAt N} {evolution : LedgerWriteEvolutionAt N before after}

theorem split_receipt_injective {left right : after.Entry}
    {same : (evolution.origin left).1 = (evolution.origin right).1} :
    Function.Injective (fun value : SourceNativeSplitCoverageAt law event evolution left right same => value.receipt) := by
  intro first second receipts
  rcases first with ⟨receipt, sourceEq, leftIn, rightIn, covers, budget, noPhantom⟩
  rcases second with ⟨other, sourceEq', leftIn', rightIn', covers', budget', noPhantom'⟩
  dsimp only at receipts
  cases receipts
  have functions : noPhantom = noPhantom' := by
    funext child member
    apply Subtype.ext
    exact law.obligationAt_injective event
      ((noPhantom child member).property.1.trans (noPhantom' child member).property.1.symm)
  cases functions
  rfl

structure SplitCheck {left right : after.Entry}
    (receipt : SplitReceipt law.vocabulary (law.obligationAt event (evolution.origin left).1)) : Prop where
  sourceEvent_eq : receipt.sourceEvent = law.sourceEventAt event
  left_member : law.obligationAt event left ∈ receipt.children
  right_member : law.obligationAt event right ∈ receipt.children
  covers_target : ∀ entry : after.Entry, (evolution.origin entry).1 = (evolution.origin left).1 →
    law.obligationAt event entry ∈ receipt.children
  budget : ∀ entry : after.Entry, (evolution.origin entry).1 = (evolution.origin left).1 →
    entry.progressBudget < (evolution.origin left).1.progressBudget
  no_phantom : ∀ child, child ∈ receipt.children → ∃ entry : after.Entry,
    law.obligationAt event entry = child ∧ (evolution.origin entry).1 = (evolution.origin left).1

def splitFromReceipt {left right : after.Entry}
    {same : (evolution.origin left).1 = (evolution.origin right).1}
    (receipt : SplitReceipt law.vocabulary (law.obligationAt event (evolution.origin left).1))
    (checked : SplitCheck (right := right) receipt) : SourceNativeSplitCoverageAt law event evolution left right same :=
  .ofReceipt receipt checked.sourceEvent_eq checked.left_member checked.right_member checked.covers_target checked.budget
    (fun child member => ⟨Classical.choose (checked.no_phantom child member), Classical.choose_spec (checked.no_phantom child member)⟩)

theorem split_checked {left right : after.Entry}
    {same : (evolution.origin left).1 = (evolution.origin right).1}
    (value : SourceNativeSplitCoverageAt law event evolution left right same) : SplitCheck (right := right) value.receipt where
  sourceEvent_eq := value.sourceEvent_eq
  left_member := value.left_member
  right_member := value.right_member
  covers_target := value.covers_target
  budget := value.childProgressBudget_strictlyDebited
  no_phantom := fun child member => ⟨(value.no_phantom_child child member).val, (value.no_phantom_child child member).property⟩

/-- The whole sealed coverage, including its Type-valued inverse section,
is recovered from its receipt: the original obligation injection determines
every inverse target entry. -/
theorem split_recovers {left right : after.Entry}
    {same : (evolution.origin left).1 = (evolution.origin right).1}
    (value : SourceNativeSplitCoverageAt law event evolution left right same) :
    splitFromReceipt value.receipt (split_checked value) = value :=
  split_receipt_injective rfl

theorem merge_receipt_injective {left right : before.Entry}
    {same : (evolution.destination left).1 = (evolution.destination right).1} :
    Function.Injective (fun value : SourceNativeMergeCoverageAt law event evolution left right same => value.receipt) := by
  intro first second receipts
  rcases first with ⟨receipt, sourceEq, targetEq, leftIn, rightIn, covers, noPhantom⟩
  rcases second with ⟨other, sourceEq', targetEq', leftIn', rightIn', covers', noPhantom'⟩
  dsimp only at receipts
  cases receipts
  have functions : noPhantom = noPhantom' := by
    funext parent member
    apply Subtype.ext
    exact law.obligationAt_injective event
      ((noPhantom parent member).property.1.trans (noPhantom' parent member).property.1.symm)
  cases functions
  rfl

structure MergeCheck {left right : before.Entry} (receipt : MergeReceipt law.vocabulary) : Prop where
  sourceEvent_eq : receipt.sourceEvent = law.sourceEventAt event
  target_eq : receipt.target = law.obligationAt event (evolution.destination left).1
  left_member : law.obligationAt event left ∈ receipt.parents
  right_member : law.obligationAt event right ∈ receipt.parents
  covers_source : ∀ entry : before.Entry, (evolution.destination entry).1 = (evolution.destination left).1 →
    law.obligationAt event entry ∈ receipt.parents
  no_phantom : ∀ parent, parent ∈ receipt.parents → ∃ entry : before.Entry,
    law.obligationAt event entry = parent ∧ (evolution.destination entry).1 = (evolution.destination left).1

def mergeFromReceipt {left right : before.Entry}
    {same : (evolution.destination left).1 = (evolution.destination right).1}
    (receipt : MergeReceipt law.vocabulary) (checked : MergeCheck (law := law) (event := event) (evolution := evolution) (left := left) (right := right) receipt) :
    SourceNativeMergeCoverageAt law event evolution left right same :=
  .ofReceipt receipt checked.sourceEvent_eq checked.target_eq checked.left_member checked.right_member checked.covers_source
    (fun parent member => ⟨Classical.choose (checked.no_phantom parent member), Classical.choose_spec (checked.no_phantom parent member)⟩)

theorem merge_checked {left right : before.Entry}
    {same : (evolution.destination left).1 = (evolution.destination right).1}
    (value : SourceNativeMergeCoverageAt law event evolution left right same) :
    MergeCheck (law := law) (event := event) (evolution := evolution) (left := left) (right := right) value.receipt where
  sourceEvent_eq := value.sourceEvent_eq
  target_eq := value.target_eq
  left_member := value.left_member
  right_member := value.right_member
  covers_source := value.covers_source
  no_phantom := fun parent member => ⟨(value.no_phantom_parent parent member).val, (value.no_phantom_parent parent member).property⟩

theorem merge_recovers {left right : before.Entry}
    {same : (evolution.destination left).1 = (evolution.destination right).1}
    (value : SourceNativeMergeCoverageAt law event evolution left right same) :
    mergeFromReceipt value.receipt (merge_checked value) = value :=
  merge_receipt_injective rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

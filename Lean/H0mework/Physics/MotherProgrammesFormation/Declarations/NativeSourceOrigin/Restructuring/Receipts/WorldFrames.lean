import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.VocabularyCompiler

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherFullCompiler MotherSourcePrograms MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (law : SourceNativeLedgerRestructuringLaw original) (point : Point original)

/-- The original registration law is read on the same complete world-ledger
image used by the original compiler/patch transport. These fields carry no
restructuring certificate or receipt. -/
structure WorldFrame {before after : CompleteLiveLedgerAt N} {newBefore newAfter : CompleteLiveLedgerAt G}
    (whole : LedgerWriteEvolutionAt N before after) (image : LedgerWriteEvolutionAt G newBefore newAfter) where
  before : before.Entry ≃ newBefore.Entry
  after : after.Entry ≃ newAfter.Entry
  before_obligation : ∀ entry, (worldLaw p law).obligationAt (pointEquiv p point).2 (before entry) = law.obligationAt point.2 entry
  after_obligation : ∀ entry, (worldLaw p law).obligationAt (pointEquiv p point).2 (after entry) = law.obligationAt point.2 entry
  origin : ∀ entry, (image.origin (after entry)).1 = before (whole.origin entry).1
  destination : ∀ entry, (image.destination (before entry)).1 = after (whole.destination entry).1
  before_budget : ∀ entry, (before entry).progressBudget = entry.progressBudget
  after_budget : ∀ entry, (after entry).progressBudget = entry.progressBudget

def normalizedFrame {before after : CompleteLiveLedgerAt N} (whole : LedgerWriteEvolutionAt N before after) :
    WorldFrame p law point whole (n.wholeLedgerEquiv before.support after.support whole) where
  before := n.ledger before.support
  after := n.ledger after.support
  before_obligation := world_obligation p law point before.support
  after_obligation := world_obligation p law point after.support
  origin := fun entry => congrArg Sigma.fst (n.whole_origin whole entry)
  destination := fun entry => congrArg Sigma.fst (n.whole_destination whole entry)
  before_budget := n.ledger_budget before.support
  after_budget := n.ledger_budget after.support

namespace WorldFrame
variable {p law point} {before after : CompleteLiveLedgerAt N} {newBefore newAfter : CompleteLiveLedgerAt G}
    {whole : LedgerWriteEvolutionAt N before after} {image : LedgerWriteEvolutionAt G newBefore newAfter}
    (frame : WorldFrame p law point whole image)

theorem origin_iff (left right : after.Entry) :
    (whole.origin left).1 = (whole.origin right).1 ↔ (image.origin (frame.after left)).1 = (image.origin (frame.after right)).1 :=
  ⟨fun same => (frame.origin left).trans ((congrArg frame.before same).trans (frame.origin right).symm),
    fun same => frame.before.injective ((frame.origin left).symm.trans (same.trans (frame.origin right)))⟩

theorem destination_iff (left right : before.Entry) :
    (whole.destination left).1 = (whole.destination right).1 ↔
      (image.destination (frame.before left)).1 = (image.destination (frame.before right)).1 :=
  ⟨fun same => (frame.destination left).trans ((congrArg frame.after same).trans (frame.destination right).symm),
    fun same => frame.after.injective ((frame.destination left).symm.trans (same.trans (frame.destination right)))⟩

theorem origin_obligation (entry : after.Entry) :
    (worldLaw p law).obligationAt (pointEquiv p point).2 (image.origin (frame.after entry)).1 = law.obligationAt point.2 (whole.origin entry).1 :=
  (congrArg ((worldLaw p law).obligationAt (pointEquiv p point).2) (frame.origin entry)).trans
    (frame.before_obligation (whole.origin entry).1)

theorem origin_budget (entry : after.Entry) :
    (image.origin (frame.after entry)).1.progressBudget = (whole.origin entry).1.progressBudget :=
  (congrArg OpenResponsibilityAt.progressBudget (frame.origin entry)).trans (frame.before_budget (whole.origin entry).1)

theorem destination_obligation (entry : before.Entry) :
    (worldLaw p law).obligationAt (pointEquiv p point).2 (image.destination (frame.before entry)).1 = law.obligationAt point.2 (whole.destination entry).1 :=
  (congrArg ((worldLaw p law).obligationAt (pointEquiv p point).2) (frame.destination entry)).trans
    (frame.after_obligation (whole.destination entry).1)
end WorldFrame

def splitReceiptCast {R : RestructuringVocabulary.{0}} {parent target : R.Obligation} (same : parent = target) :
    SplitReceipt R parent ≃ SplitReceipt R target := Equiv.cast (congrArg (SplitReceipt R) same)

theorem splitCast_source {R : RestructuringVocabulary.{0}} {parent target : R.Obligation} (same : parent = target)
    (receipt : SplitReceipt R parent) : (splitReceiptCast same receipt).sourceEvent = receipt.sourceEvent := by cases same; rfl

theorem splitCast_children {R : RestructuringVocabulary.{0}} {parent target : R.Obligation} (same : parent = target)
    (receipt : SplitReceipt R parent) : (splitReceiptCast same receipt).children = receipt.children := by cases same; rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

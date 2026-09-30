import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.Merge
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
open MotherArenaNetwork ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
open MotherObligationOrigin
open MotherRestructuringReceipts
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {before after : CompleteLiveLedgerAt N} {evolution : LedgerWriteEvolutionAt N before after}
    {I : Type} (coordinates : ReceiptCoordinates (rank := rank) law.vocabulary) (index : I ↪ MotherArenaHigher.Base rank)

def formSplitCoverageSection (left right : I → after.Entry)
    (same : ∀ i, (evolution.origin (left i)).1 = (evolution.origin (right i)).1) (material : M) :
    Option ((i : I) → SourceNativeSplitCoverageAt law event evolution (left i) (right i) (same i)) :=
  (formSplitSection coordinates index (fun i => law.obligationAt event (evolution.origin (left i)).1) material).bind (fun receipts =>
    if checked : ∀ i, SplitCheck (law := law) (event := event) (evolution := evolution) (left := left i) (right := right i) (receipts i) then
      some (fun i => splitFromReceipt (receipts i) (checked i))
    else none)

theorem every_split_coverage_section (left right : I → after.Entry)
    (same : ∀ i, (evolution.origin (left i)).1 = (evolution.origin (right i)).1)
    (original : (i : I) → SourceNativeSplitCoverageAt law event evolution (left i) (right i) (same i)) :
    ∃ material : M, formSplitCoverageSection coordinates index left right same material = some original := by
  obtain ⟨material, formed⟩ := every_split_section coordinates index
    (fun i => law.obligationAt event (evolution.origin (left i)).1) (fun i => (original i).receipt)
  have checked : ∀ i, SplitCheck (law := law) (event := event) (evolution := evolution) (left := left i) (right := right i)
      (original i).receipt := fun i => split_checked (original i)
  refine ⟨material, ?_⟩
  simp only [formSplitCoverageSection, formed, Option.bind_some, dif_pos checked]
  exact congrArg some (funext fun i => split_recovers (original i))

def formMergeCoverageSection (left right : I → before.Entry)
    (same : ∀ i, (evolution.destination (left i)).1 = (evolution.destination (right i)).1) (material : M) :
    Option ((i : I) → SourceNativeMergeCoverageAt law event evolution (left i) (right i) (same i)) :=
  (formMergeSection coordinates index material).bind (fun receipts =>
    if checked : ∀ i, MergeCheck (law := law) (event := event) (evolution := evolution) (left := left i) (right := right i) (receipts i) then
      some (fun i => mergeFromReceipt (receipts i) (checked i))
    else none)

theorem every_merge_coverage_section (left right : I → before.Entry)
    (same : ∀ i, (evolution.destination (left i)).1 = (evolution.destination (right i)).1)
    (original : (i : I) → SourceNativeMergeCoverageAt law event evolution (left i) (right i) (same i)) :
    ∃ material : M, formMergeCoverageSection coordinates index left right same material = some original := by
  obtain ⟨material, formed⟩ := every_merge_section coordinates index (fun i => (original i).receipt)
  have checked : ∀ i, MergeCheck (law := law) (event := event) (evolution := evolution) (left := left i) (right := right i)
      (original i).receipt := fun i => merge_checked (original i)
  refine ⟨material, ?_⟩
  simp only [formMergeCoverageSection, formed, Option.bind_some, dif_pos checked]
  exact congrArg some (funext fun i => merge_recovers (original i))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts

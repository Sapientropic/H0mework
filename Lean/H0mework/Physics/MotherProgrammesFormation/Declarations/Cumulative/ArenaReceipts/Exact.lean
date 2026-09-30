import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.MergeClassification
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Exact

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
open MotherArenaNetwork MotherObligationOrigin MotherFullCompiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherObligationOrigin
open MotherRestructuringReceipts
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {before after : CompleteLiveLedgerAt N} (evolution : LedgerWriteEvolutionAt N before after)

def splitContextAddress (world : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) : SplitContext evolution ↪ B :=
  subtypeAddress (MotherArenaObligation.productEmbedding (world.entry after.support) (world.entry after.support)) _

def mergeContextAddress (world : MotherArenaCompiler.LedgerCoordinates (rank := rank) N) : MergeContext evolution ↪ B :=
  subtypeAddress (MotherArenaObligation.productEmbedding (world.entry before.support) (world.entry before.support)) _

variable (coordinates : ReceiptCoordinates (rank := rank) law.vocabulary) (world : MotherArenaCompiler.LedgerCoordinates (rank := rank) N)

def formExactParts (splitSelector splitMaterial mergeSelector mergeMaterial : M) :
    Option (ExactLedgerRestructuringCertificationAt law event evolution) :=
  (formSplitClassification (event := event) coordinates (splitContextAddress evolution world)
    (fun pair => pair.val.1) (fun pair => pair.val.2) (fun pair => pair.property) splitSelector splitMaterial).bind (fun split =>
      (formMergeClassification (event := event) coordinates (mergeContextAddress evolution world)
        (fun pair => pair.val.1) (fun pair => pair.val.2) (fun pair => pair.property) mergeSelector mergeMaterial).map
        (exactOfSections evolution split))

def formExact (material : M) : Option (ExactLedgerRestructuringCertificationAt law event evolution) :=
  let first := (MotherArenaHigher.split rank) material
  let second := (MotherArenaHigher.split rank) first.2
  let third := (MotherArenaHigher.split rank) second.2
  formExactParts evolution coordinates world first.1 second.1 third.1 third.2

theorem every_exact (original : ExactLedgerRestructuringCertificationAt law event evolution) :
    ∃ material : M, formExact evolution coordinates world material = some original := by
  obtain ⟨splitSelector, splitMaterial, splitFormed⟩ := every_split_classification coordinates (splitContextAddress evolution world)
    (fun pair => pair.val.1) (fun pair => pair.val.2) (fun pair => pair.property)
    (fun pair => original.split pair.val.1 pair.val.2 pair.property)
  obtain ⟨mergeSelector, mergeMaterial, mergeFormed⟩ := every_merge_classification coordinates (mergeContextAddress evolution world)
    (fun pair => pair.val.1) (fun pair => pair.val.2) (fun pair => pair.property)
    (fun pair => original.merge pair.val.1 pair.val.2 pair.property)
  refine ⟨(MotherArenaHigher.pack rank) (splitSelector, (MotherArenaHigher.pack rank)
    (splitMaterial, (MotherArenaHigher.pack rank) (mergeSelector, mergeMaterial))), ?_⟩
  simp only [formExact, MotherArenaHigher.split_pack, formExactParts, splitFormed, Option.bind_some, mergeFormed, Option.map_some]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts

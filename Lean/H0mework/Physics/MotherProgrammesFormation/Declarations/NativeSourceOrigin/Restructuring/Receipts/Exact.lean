import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.MergeClassification

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory MotherObligationOrigin MotherFullCompiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {before after : CompleteLiveLedgerAt N} (evolution : LedgerWriteEvolutionAt N before after)

abbrev SplitContext := {pair : after.Entry × after.Entry // (evolution.origin pair.1).1 = (evolution.origin pair.2).1}
abbrev MergeContext := {pair : before.Entry × before.Entry // (evolution.destination pair.1).1 = (evolution.destination pair.2).1}

def splitContextAddress (world : LedgerCoordinates N) : SplitContext evolution ↪ B :=
  subtypeAddress (productEmbedding (world.entry after.support) (world.entry after.support)) _

def mergeContextAddress (world : LedgerCoordinates N) : MergeContext evolution ↪ B :=
  subtypeAddress (productEmbedding (world.entry before.support) (world.entry before.support)) _

abbrev SplitClassificationSection := (pair : SplitContext evolution) →
  SourceNativeSplitClassificationAt law event evolution pair.val.1 pair.val.2 pair.property

abbrev MergeClassificationSection := (pair : MergeContext evolution) →
  SourceNativeMergeClassificationAt law event evolution pair.val.1 pair.val.2 pair.property

def exactOfSections (split : SplitClassificationSection (law := law) (event := event) evolution)
    (merge : MergeClassificationSection (law := law) (event := event) evolution) :
    ExactLedgerRestructuringCertificationAt law event evolution where
  split := fun left right same => split ⟨(left, right), same⟩
  merge := fun left right same => merge ⟨(left, right), same⟩

variable (coordinates : ReceiptCoordinates law.vocabulary) (world : LedgerCoordinates N)

def formExactParts (splitSelector splitMaterial mergeSelector mergeMaterial : M) :
    Option (ExactLedgerRestructuringCertificationAt law event evolution) :=
  (formSplitClassification (event := event) coordinates (splitContextAddress evolution world)
    (fun pair => pair.val.1) (fun pair => pair.val.2) (fun pair => pair.property) splitSelector splitMaterial).bind (fun split =>
      (formMergeClassification (event := event) coordinates (mergeContextAddress evolution world)
        (fun pair => pair.val.1) (fun pair => pair.val.2) (fun pair => pair.property) mergeSelector mergeMaterial).map
        (exactOfSections evolution split))

def formExact (material : M) : Option (ExactLedgerRestructuringCertificationAt law event evolution) :=
  let first := MotherHigherLawValue.split material
  let second := MotherHigherLawValue.split first.2
  let third := MotherHigherLawValue.split second.2
  formExactParts evolution coordinates world first.1 second.1 third.1 third.2

theorem every_exact (original : ExactLedgerRestructuringCertificationAt law event evolution) :
    ∃ material : M, formExact evolution coordinates world material = some original := by
  obtain ⟨splitSelector, splitMaterial, splitFormed⟩ := every_split_classification coordinates (splitContextAddress evolution world)
    (fun pair => pair.val.1) (fun pair => pair.val.2) (fun pair => pair.property)
    (fun pair => original.split pair.val.1 pair.val.2 pair.property)
  obtain ⟨mergeSelector, mergeMaterial, mergeFormed⟩ := every_merge_classification coordinates (mergeContextAddress evolution world)
    (fun pair => pair.val.1) (fun pair => pair.val.2) (fun pair => pair.property)
    (fun pair => original.merge pair.val.1 pair.val.2 pair.property)
  refine ⟨MotherHigherLawValue.pack (splitSelector, MotherHigherLawValue.pack
    (splitMaterial, MotherHigherLawValue.pack (mergeSelector, mergeMaterial))), ?_⟩
  simp only [formExact, MotherHigherLawValue.split_pack, formExactParts, splitFormed, Option.bind_some, mergeFormed, Option.map_some]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

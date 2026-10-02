import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Selection

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {law : SourceNativeLedgerRestructuringLaw source}
    {current : V.Current} {event : source.toRootSource.actual.OccurrenceAt current}
    {before after : CompleteLiveLedgerAt N} {evolution : LedgerWriteEvolutionAt N before after}
    {I : Type} (coordinates : ReceiptCoordinates law.vocabulary) (index : I ↪ B)
    (left right : I → after.Entry)
    (same : ∀ i, (evolution.origin (left i)).1 = (evolution.origin (right i)).1)

def formSplitClassification (selector material : M) :
    Option ((i : I) → SourceNativeSplitClassificationAt law event evolution (left i) (right i) (same i)) :=
  if identities : ∀ i, ¬ bit selector 0 (index i) → left i = right i then
    (formSplitCoverageSection (event := event) coordinates (subtypeAddress index (fun i => bit selector 0 (index i)))
      (fun i => left i.val) (fun i => right i.val) (fun i => same i.val) material).map
        (fun coverage i => if selected : bit selector 0 (index i) then .split (coverage ⟨i, selected⟩)
          else .identity (identities i selected))
  else none

theorem every_split_classification
    (original : (i : I) → SourceNativeSplitClassificationAt law event evolution (left i) (right i) (same i)) :
    ∃ selector material : M, formSplitClassification coordinates index left right same selector material = some original := by
  obtain ⟨selector, selected⟩ := every_selection index (fun i => ∃ coverage, original i = .split coverage)
  let selectedCoverage : (i : {i // bit selector 0 (index i)}) →
      SourceNativeSplitCoverageAt law event evolution (left i.val) (right i.val) (same i.val) :=
    fun i => Classical.choose ((selected i.val).mp i.property)
  have identities : ∀ i, ¬ bit selector 0 (index i) → left i = right i := by
    intro i absent
    cases result : original i with
    | identity equality => exact equality
    | split coverage => exact (absent ((selected i).mpr ⟨coverage, result⟩)).elim
  obtain ⟨material, formed⟩ := every_split_coverage_section coordinates
    (subtypeAddress index (fun i => bit selector 0 (index i))) (fun i => left i.val) (fun i => right i.val)
    (fun i => same i.val) selectedCoverage
  refine ⟨selector, material, ?_⟩
  simp only [formSplitClassification, dif_pos identities, formed, Option.map_some]
  congr 1
  funext i
  by_cases h : bit selector 0 (index i)
  · simp only [dif_pos h]
    exact (Classical.choose_spec ((selected i).mp h)).symm
  · simp only [dif_neg h]
    cases result : original i with
    | identity equality => rfl
    | split coverage => exact (h ((selected i).mpr ⟨coverage, result⟩)).elim

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

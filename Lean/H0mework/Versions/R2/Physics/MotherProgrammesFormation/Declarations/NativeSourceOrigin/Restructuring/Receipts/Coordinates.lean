import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Anchors

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts
open MotherNetworkFactory MotherRestructuringOrigin MotherObligationOrigin MotherFullCompiler
open MotherLedgerRoot MotherProjectionOrigin ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

structure ReceiptCoordinates (R : RestructuringVocabulary.{0}) extends VocabularyCoordinates R where
  descendant : ∀ source (parent child : R.Obligation),
    R.DescendantAt source parent.sourceIncidence parent.content child.sourceIncidence child.content ↪ B
  split : ∀ source (parent : R.Obligation) (children : List R.Obligation),
    R.SplitCoverageAt source parent.content (children.map AdmittedObligation.content) ↪ B
  merge : ∀ source (parents : List R.Obligation) (target : R.Obligation),
    R.MergeCoverageAt source (parents.map AdmittedObligation.content) target.content ↪ B
  discharge : ∀ source (parent child : R.Obligation), R.LocalDischargePreservedAt source parent.content child.content ↪ B

private def canonicalReceiptCoordinates (base families : M)
    (ops : Operations (formedSorts base) (formedFamilies base families)) :
    ReceiptCoordinates (restructuring (formedSorts base) (formedFamilies base families) ops) where
  event := fieldEmbedding base 0
  obligation := obligationEmbedding base families ops
  observation := fieldEmbedding base 8
  incidence := fieldEmbedding base 7
  lineage := fieldEmbedding base 6
  descendant := fun _ _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  split := fun _ _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  merge := fun _ _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  discharge := fun _ _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def receiptCoordinates (material : M) (R : RestructuringVocabulary.{0})
    (formed : formVocabulary material = some R) : ReceiptCoordinates R := by
  unfold formVocabulary formVocabularyParts at formed
  dsimp only at formed
  split at formed
  · rename_i checked
    split at formed
    · rename_i laws
      exact Eq.mp (congrArg ReceiptCoordinates (Option.some.inj formed))
        (canonicalReceiptCoordinates _ _ (operations checked laws))
    · cases formed
  · cases formed

theorem fixed_law_vocabulary {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {R : RestructuringVocabulary.{0}}
    (coordinates : Coordinates source) (world : WorldCoordinates N) (vocabulary : VocabularyCoordinates R)
    (material : M) (law : SourceNativeLedgerRestructuringLaw source)
    (formed : formFixedLaw coordinates world vocabulary material = some law) : law.vocabulary = R := by
  unfold formFixedLaw at formed
  split at formed
  · dsimp only at formed
    split at formed
    · exact congrArg SourceNativeLedgerRestructuringLaw.vocabulary (Option.some.inj formed).symm
    · cases formed
  · cases formed

def vocabularyMaterial (material : M) : M := (MotherHigherLawValue.split (MotherHigherLawValue.split material).2).1

theorem law_vocabulary_formed (material : M) (value : LawValue) (formed : formLaw material = some value) :
    formVocabulary (vocabularyMaterial material) = some value.2.vocabulary := by
  unfold formLaw formLawParts at formed
  dsimp only at formed
  obtain ⟨projection, parentFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  obtain ⟨R, vocabularyFormed, selected⟩ := Option.pbind_eq_some_iff.mp selected
  obtain ⟨law, lawFormed, same⟩ := Option.map_eq_some_iff.mp selected
  have vocabularyEq := fixed_law_vocabulary _ _ _ _ law lawFormed
  exact vocabularyFormed.trans (congrArg some (vocabularyEq.symm.trans
    (congrArg (fun output : LawValue => output.2.vocabulary) same)))

def coordinatesOfLaw (material : M) (value : LawValue) (formed : formLaw material = some value) :
    ReceiptCoordinates value.2.vocabulary :=
  receiptCoordinates (vocabularyMaterial material) value.2.vocabulary (law_vocabulary_formed material value formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringReceipts

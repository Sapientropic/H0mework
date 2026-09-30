import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaReceipts.Anchors
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts
open MotherArenaNetwork MotherRestructuringOrigin MotherObligationOrigin MotherFullCompiler
open MotherLedgerRoot MotherProjectionOrigin ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherObligationOrigin
open MotherRestructuringReceipts
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure ReceiptCoordinates (R : RestructuringVocabulary.{0}) extends MotherArenaObligation.VocabularyCoordinates (rank := rank) R where
  descendant : ∀ source (parent child : R.Obligation),
    R.DescendantAt source parent.sourceIncidence parent.content child.sourceIncidence child.content ↪ B
  split : ∀ source (parent : R.Obligation) (children : List R.Obligation),
    R.SplitCoverageAt source parent.content (children.map AdmittedObligation.content) ↪ B
  merge : ∀ source (parents : List R.Obligation) (target : R.Obligation),
    R.MergeCoverageAt source (parents.map AdmittedObligation.content) target.content ↪ B
  discharge : ∀ source (parent child : R.Obligation), R.LocalDischargePreservedAt source parent.content child.content ↪ B

private def canonicalReceiptCoordinates (base families : M)
    (ops : Operations (MotherArenaRestructuringVocabulary.formedSorts base) (MotherArenaRestructuringVocabulary.formedFamilies base families)) :
    ReceiptCoordinates (rank := rank) (restructuring (MotherArenaRestructuringVocabulary.formedSorts base) (MotherArenaRestructuringVocabulary.formedFamilies base families) ops) where
  event := MotherArenaObligation.fieldEmbedding base 0
  obligation := MotherArenaObligation.obligationEmbedding base families ops
  observation := MotherArenaObligation.fieldEmbedding base 8
  incidence := MotherArenaObligation.fieldEmbedding base 7
  lineage := MotherArenaObligation.fieldEmbedding base 6
  descendant := fun _ _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  split := fun _ _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  merge := fun _ _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  discharge := fun _ _ _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def receiptCoordinates (material : M) (R : RestructuringVocabulary.{0})
    (formed : MotherArenaRestructuringVocabulary.formVocabulary material = some R) : ReceiptCoordinates (rank := rank) R := by
  unfold MotherArenaRestructuringVocabulary.formVocabulary MotherArenaRestructuringVocabulary.formVocabularyParts at formed
  dsimp only at formed
  split at formed
  · rename_i checked
    split at formed
    · rename_i laws
      exact Eq.mp (congrArg (ReceiptCoordinates (rank := rank)) (Option.some.inj formed))
        (canonicalReceiptCoordinates _ _ (MotherArenaRestructuringVocabulary.operations checked laws))
    · cases formed
  · cases formed

theorem fixed_law_vocabulary {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {source : SourceNativeSource N V} {R : RestructuringVocabulary.{0}}
    (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (world : MotherArenaObligation.WorldCoordinates (rank := rank) N) (vocabulary : MotherArenaObligation.VocabularyCoordinates (rank := rank) R)
    (material : M) (law : SourceNativeLedgerRestructuringLaw source)
    (formed : MotherArenaObligation.formFixedLaw coordinates world vocabulary material = some law) : law.vocabulary = R := by
  unfold MotherArenaObligation.formFixedLaw at formed
  split at formed
  · dsimp only at formed
    split at formed
    · exact congrArg SourceNativeLedgerRestructuringLaw.vocabulary (Option.some.inj formed).symm
    · cases formed
  · cases formed

def vocabularyMaterial (material : M) : M := ((MotherArenaHigher.split rank) ((MotherArenaHigher.split rank) material).2).1

theorem law_vocabulary_formed (material : M) (value : LawValue) (formed : MotherArenaObligation.formLaw material = some value) :
    MotherArenaRestructuringVocabulary.formVocabulary (vocabularyMaterial material) = some value.2.vocabulary := by
  unfold MotherArenaObligation.formLaw MotherArenaObligation.formLawParts at formed
  dsimp only at formed
  obtain ⟨projection, parentFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  obtain ⟨R, vocabularyFormed, selected⟩ := Option.pbind_eq_some_iff.mp selected
  obtain ⟨law, lawFormed, same⟩ := Option.map_eq_some_iff.mp selected
  have vocabularyEq := fixed_law_vocabulary _ _ _ _ law lawFormed
  exact vocabularyFormed.trans (congrArg some (vocabularyEq.symm.trans
    (congrArg (fun output : LawValue => output.2.vocabulary) same)))

def coordinatesOfLaw (material : M) (value : LawValue) (formed : MotherArenaObligation.formLaw material = some value) :
    ReceiptCoordinates (rank := rank) value.2.vocabulary :=
  receiptCoordinates (vocabularyMaterial material) value.2.vocabulary (law_vocabulary_formed material value formed)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaReceipts

import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaAdmission.Presentations
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission
open MotherArenaNetwork MotherFullCompiler MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherInventoryAdmission
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure VocabularyCoordinates (V : ConstructiveRoot.Vocabulary.{0}) where
  evolution : ∀ current, EvolutionAt V current ↪ B
  cofinal : V.cofinal.Event ↪ B

private def subtypeCode {P : B → Prop} : {value : B // P value} ↪ B := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

private def canonicalVocabularyCoordinates (base : M) (checked : MotherArenaVocabulary.Check base) :
    VocabularyCoordinates (rank := rank) (MotherArenaActual.V base checked) where
  evolution := fun current => (evolutionBodyEquiv (MotherArenaActual.V base checked) current).toEmbedding.trans
    (MotherArenaObligation.sumEmbedding subtypeCode (MotherArenaObligation.sumEmbedding subtypeCode (MotherArenaObligation.sumEmbedding subtypeCode (MotherArenaObligation.sumEmbedding subtypeCode subtypeCode))))
  cofinal := subtypeCode

def vocabularyCoordinatesOfSource (material : M) (value : MotherArenaCompiler.SourceValue)
    (formed : MotherArenaSource.formSource material = some value) : VocabularyCoordinates (rank := rank) value.2.1 := by
  unfold MotherArenaSource.formSource MotherArenaSource.formComponents at formed
  dsimp only at formed
  split at formed
  · split at formed
    · rename_i hv
      split at formed
      · split at formed
        · split at formed
          · exact Eq.mp (congrArg (fun value : MotherArenaCompiler.SourceValue => VocabularyCoordinates (rank := rank) value.2.1) (Option.some.inj formed))
              (canonicalVocabularyCoordinates _ hv)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

structure SourceCoordinates {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) extends MotherArenaCompiler.Coordinates (rank := rank) source where
  vocabulary : VocabularyCoordinates (rank := rank) V

def coordinatesOfNativeSource (material : M) (value : MotherArenaCompiler.SourceValue)
    (formed : MotherArenaSource.formSource material = some value) : SourceCoordinates (rank := rank) value.2.2 where
  toCoordinates := MotherArenaCompiler.coordinatesOfFormation material value formed
  vocabulary := vocabularyCoordinatesOfSource material value formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaAdmission

import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.Presentations

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory MotherFullCompiler MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

def evolutionBodyEquiv (V : ConstructiveRoot.Vocabulary.{0}) (current : V.Current) :
    EvolutionAt V current ≃ V.NativeWriteAt current ⊕ V.RelationWriteAt current ⊕
      V.ContinuedTransportAt current ⊕ V.BorromeanRedirectAt current ⊕ V.FaithfulTerminalAt current where
  toFun := fun value => match value with
    | .nativeWrite value => .inl value
    | .relationWrite value => .inr (.inl value)
    | .continuedTransport value => .inr (.inr (.inl value))
    | .borromeanRedirect value => .inr (.inr (.inr (.inl value)))
    | .faithfulTerminal value => .inr (.inr (.inr (.inr value)))
  invFun := fun value => match value with
    | .inl value => .nativeWrite value
    | .inr (.inl value) => .relationWrite value
    | .inr (.inr (.inl value)) => .continuedTransport value
    | .inr (.inr (.inr (.inl value))) => .borromeanRedirect value
    | .inr (.inr (.inr (.inr value))) => .faithfulTerminal value
  left_inv := fun value => by cases value <;> rfl
  right_inv := fun value => by rcases value with value | value | value | value | value <;> rfl

structure VocabularyCoordinates (V : ConstructiveRoot.Vocabulary.{0}) where
  evolution : ∀ current, EvolutionAt V current ↪ B
  cofinal : V.cofinal.Event ↪ B

private def subtypeCode {P : B → Prop} : {value : B // P value} ↪ B := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

private def canonicalVocabularyCoordinates (base : M) (checked : MotherVocabularyOrigin.Check base) :
    VocabularyCoordinates (MotherActualOrigin.V base checked) where
  evolution := fun current => (evolutionBodyEquiv (MotherActualOrigin.V base checked) current).toEmbedding.trans
    (sumEmbedding subtypeCode (sumEmbedding subtypeCode (sumEmbedding subtypeCode (sumEmbedding subtypeCode subtypeCode))))
  cofinal := subtypeCode

def vocabularyCoordinatesOfSource (material : M) (value : SourceValue)
    (formed : MotherNativeSourceOrigin.formSource material = some value) : VocabularyCoordinates value.2.1 := by
  unfold MotherNativeSourceOrigin.formSource MotherNativeSourceOrigin.formComponents at formed
  dsimp only at formed
  split at formed
  · split at formed
    · rename_i hv
      split at formed
      · split at formed
        · split at formed
          · exact Eq.mp (congrArg (fun value : SourceValue => VocabularyCoordinates value.2.1) (Option.some.inj formed))
              (canonicalVocabularyCoordinates _ hv)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

structure SourceCoordinates {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) extends MotherFullCompiler.Coordinates source where
  vocabulary : VocabularyCoordinates V

def coordinatesOfNativeSource (material : M) (value : SourceValue)
    (formed : MotherNativeSourceOrigin.formSource material = some value) : SourceCoordinates value.2.2 where
  toCoordinates := coordinatesOfFormation material value formed
  vocabulary := vocabularyCoordinatesOfSource material value formed

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission

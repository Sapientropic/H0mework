import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Codes
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open MotherNetworkFactory MotherRestructuringOrigin MotherFullCompiler MotherSourcePrograms
open MotherExactPrograms MotherPatchInventory MotherLedgerRoot MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

structure VocabularyCoordinates (R : RestructuringVocabulary.{0}) where
  event : R.base.SourceEvent ↪ B
  obligation : R.Obligation ↪ B
  observation : R.base.SourceObservation.Carrier ↪ B
  incidence : R.base.Incidence ↪ B
  lineage : R.base.Lineage ↪ B

def vocabularyCoordinates (material : M) (R : RestructuringVocabulary.{0})
    (formed : formVocabulary material = some R) : VocabularyCoordinates R := by
  unfold formVocabulary formVocabularyParts at formed
  dsimp only at formed
  split at formed
  · rename_i checked
    split at formed
    · rename_i laws
      exact Eq.mp (congrArg VocabularyCoordinates (Option.some.inj formed))
        { event := fieldEmbedding _ 0
          obligation := obligationEmbedding _ _ (operations checked laws)
          observation := fieldEmbedding _ 8
          incidence := fieldEmbedding _ 7
          lineage := fieldEmbedding _ 6 }
    · cases formed
  · cases formed

structure WorldCoordinates (N : WorldRelationNetwork.{0}) extends LedgerCoordinates N where
  responsibility : N.Responsibility ↪ B
  anchor : N.Anchor ↪ B
  incidence : N.Incidence ↪ B
  lineage : N.Lineage ↪ B

private def canonicalWorldCoordinates (material : M) (checked : MotherNetworkFactory.Check material) :
    WorldCoordinates (MotherNativeSourceOrigin.network material checked) where
  support := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  entry := fun _ => sigmaEmbedding
    ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
    (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
  transfer := fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  settlement := fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  responsibility := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  anchor := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  incidence := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩
  lineage := ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩

def worldCoordinatesOfFormation (material : M) (value : SourceValue)
    (formed : MotherNativeSourceOrigin.formSource material = some value) : WorldCoordinates value.1 := by
  unfold MotherNativeSourceOrigin.formSource MotherNativeSourceOrigin.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · split at formed
      · split at formed
        · split at formed
          · exact Eq.mp (congrArg (fun source : SourceValue => WorldCoordinates source.1) (Option.some.inj formed))
              (canonicalWorldCoordinates _ hn)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

def compilerWorldCoordinates (material : M) (value : CompilerValue)
    (formed : formCompiler material = some value) : WorldCoordinates value.1.1.1 :=
  worldCoordinatesOfFormation (sourceMaterial (compilationMaterial (programmeParent material))) value.1.1
    (compilation_source_formed _ _ value.1.2.1
      (programme_compilation_formed _ _ (compiler_programmes_formed material value formed)))

def rootWorldCoordinates (material : M) (value : RootValue) (formed : formRoot material = some value) :
    WorldCoordinates value.1 := by
  unfold formRoot formRootParts at formed
  dsimp only at formed
  cases compilerFormed : formCompiler (MotherHigherLawValue.split material).1 with
  | none => simp only [compilerFormed, Option.pbind_none, reduceCtorEq] at formed
  | some compiler =>
      simp only [compilerFormed, Option.pbind_some] at formed
      split at formed
      · split at formed
        · exact Eq.mp (congrArg (fun result : RootValue => WorldCoordinates result.1) (Option.some.inj formed))
            (compilerWorldCoordinates (MotherHigherLawValue.split material).1 compiler compilerFormed)
        · cases formed
      · cases formed

theorem projection_root_formed (material : M) (value : ProjectionValue)
    (formed : formProjection material = some value) :
    formRoot (MotherHigherLawValue.split material).1 = some value.1 := by
  unfold formProjection formProjectionParts at formed
  dsimp only at formed
  obtain ⟨root, rootFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · exact rootFormed.trans (congrArg (fun result : ProjectionValue => some result.1) (Option.some.inj selected))
  · cases selected

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin

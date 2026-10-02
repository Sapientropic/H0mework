import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaObligation.Codes
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
open MotherArenaNetwork MotherRestructuringOrigin MotherFullCompiler MotherSourcePrograms
open MotherExactPrograms MotherPatchInventory MotherLedgerRoot MotherProjectionOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open MotherObligationOrigin
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

structure VocabularyCoordinates (R : RestructuringVocabulary.{0}) where
  event : R.base.SourceEvent ↪ B
  obligation : R.Obligation ↪ B
  observation : R.base.SourceObservation.Carrier ↪ B
  incidence : R.base.Incidence ↪ B
  lineage : R.base.Lineage ↪ B

def vocabularyCoordinates (material : M) (R : RestructuringVocabulary.{0})
    (formed : MotherArenaRestructuringVocabulary.formVocabulary material = some R) : VocabularyCoordinates (rank := rank) R := by
  unfold MotherArenaRestructuringVocabulary.formVocabulary MotherArenaRestructuringVocabulary.formVocabularyParts at formed
  dsimp only at formed
  split at formed
  · rename_i checked
    split at formed
    · rename_i laws
      exact Eq.mp (congrArg (VocabularyCoordinates (rank := rank)) (Option.some.inj formed))
        { event := fieldEmbedding _ 0
          obligation := obligationEmbedding _ _ (MotherArenaRestructuringVocabulary.operations checked laws)
          observation := fieldEmbedding _ 8
          incidence := fieldEmbedding _ 7
          lineage := fieldEmbedding _ 6 }
    · cases formed
  · cases formed

structure WorldCoordinates (N : WorldRelationNetwork.{0}) extends MotherArenaCompiler.LedgerCoordinates (rank := rank) N where
  responsibility : N.Responsibility ↪ B
  anchor : N.Anchor ↪ B
  incidence : N.Incidence ↪ B
  lineage : N.Lineage ↪ B

private def canonicalWorldCoordinates (material : M) (checked : MotherArenaNetwork.Check material) :
    WorldCoordinates (rank := rank) (MotherArenaSource.network material checked) where
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

def worldCoordinatesOfFormation (material : M) (value : MotherArenaCompiler.SourceValue)
    (formed : MotherArenaSource.formSource material = some value) : WorldCoordinates (rank := rank) value.1 := by
  unfold MotherArenaSource.formSource MotherArenaSource.formComponents at formed
  dsimp only at formed
  split at formed
  · rename_i hn
    split at formed
    · split at formed
      · split at formed
        · split at formed
          · exact Eq.mp (congrArg (fun source : MotherArenaCompiler.SourceValue => WorldCoordinates (rank := rank) source.1) (Option.some.inj formed))
              (canonicalWorldCoordinates _ hn)
          · cases formed
        · cases formed
      · cases formed
    · cases formed
  · cases formed

def compilerWorldCoordinates (material : M) (value : CompilerValue)
    (formed : MotherArenaPatches.formCompiler material = some value) : WorldCoordinates (rank := rank) value.1.1.1 :=
  worldCoordinatesOfFormation (MotherArenaPrograms.sourceMaterial (MotherArenaPatches.compilationMaterial (MotherArenaRoot.programmeParent material))) value.1.1
    (MotherArenaPrograms.compilation_source_formed _ _ value.1.2.1
      (MotherArenaPatches.programme_compilation_formed _ _ (MotherArenaRoot.compiler_programmes_formed material value formed)))

def rootWorldCoordinates (material : M) (value : RootValue) (formed : MotherArenaRoot.formRoot material = some value) :
    WorldCoordinates (rank := rank) value.1 := by
  unfold MotherArenaRoot.formRoot MotherArenaRoot.formRootParts at formed
  dsimp only at formed
  cases compilerFormed : MotherArenaPatches.formCompiler ((MotherArenaHigher.split rank) material).1 with
  | none => simp only [compilerFormed, Option.pbind_none, reduceCtorEq] at formed
  | some compiler =>
      simp only [compilerFormed, Option.pbind_some] at formed
      split at formed
      · split at formed
        · exact Eq.mp (congrArg (fun result : RootValue => WorldCoordinates (rank := rank) result.1) (Option.some.inj formed))
            (compilerWorldCoordinates ((MotherArenaHigher.split rank) material).1 compiler compilerFormed)
        · cases formed
      · cases formed

theorem projection_root_formed (material : M) (value : ProjectionValue)
    (formed : MotherArenaProjection.formProjection material = some value) :
    MotherArenaRoot.formRoot ((MotherArenaHigher.split rank) material).1 = some value.1 := by
  unfold MotherArenaProjection.formProjection MotherArenaProjection.formProjectionParts at formed
  dsimp only at formed
  obtain ⟨root, rootFormed, selected⟩ := Option.pbind_eq_some_iff.mp formed
  split at selected
  · exact rootFormed.trans (congrArg (fun result : ProjectionValue => some result.1) (Option.some.inj selected))
  · cases selected

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation

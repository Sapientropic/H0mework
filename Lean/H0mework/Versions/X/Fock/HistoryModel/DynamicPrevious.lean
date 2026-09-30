import H0mework.Versions.X.Fock.HistoryModel.DynamicSource
import H0mework.Probability.Source.FamilyField

/-! Existing index projections and cofinal naturality retain the whole old word inventory at the actual next alphabet. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic

open SourceGeneratedActionObservationHistory SourceOwnedObservationHistory SourceOwnedObservationHistory.Installed
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open SourceGeneratedScalarCofinalNaturality CategoryTheory

noncomputable section

abbrev wordData (depth : Nat) := data (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth))
abbrev wordLaws (depth : Nat) := compatible (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth))

def readPrevious (depth : Nat) :
    (List (Fock.Letter (depth + 1)) → FamilyModel.Fock.Index (depth + 1) → ParentCarrier) →ₗ[ℤ]
      (List (Fock.Letter depth) → FamilyModel.Fock.Index depth → ParentCarrier) :=
  LinearMap.pi fun word => (FamilyField.indexMap (B := fun _ => ParentCarrier) (FamilyModel.Fock.oldIndex depth)).comp
    (LinearMap.proj (word.map (oldLetter depth)))

def morphism (depth : Nat) : Morphism (wordData (depth + 1)) (wordData depth) where
  generatorMap := LinearMap.id
  stageMap stage := LinearMap.pi fun index => (readPrevious depth).comp (LinearMap.proj index)
  transition_naturality _ := rfl
  evaluator_naturality stage := by
    apply LinearMap.ext
    intro source
    funext time word index
    exact old_inventory_read depth ((Fock.actions depth (.inl ()) ^ time.val) source) word index

def previous (depth : Nat) : Complete.Carrier (depth + 1) →ₗ[ℤ] Complete.Carrier depth :=
  ((morphism depth).completionMorphism (wordLaws (depth + 1)) (wordLaws depth)).hom

theorem previous_source (depth : Nat) (source : SourceOwnedObservationHistory.Carrier Current) :
    previous depth (sourceMap (Fock.actions (depth + 1) (.inl ()))
      (inventory (Fock.actions (depth + 1)) (Fock.observer (depth + 1))) source) =
      sourceMap (Fock.actions depth (.inl ())) (inventory (Fock.actions depth) (Fock.observer depth)) source :=
  ConcreteCategory.congr_hom ((morphism depth).completionMorphism_source_naturality (wordLaws (depth + 1)) (wordLaws depth)) source

theorem previous_point (depth : Nat) (state : Current) :
    previous depth (Complete.point (depth + 1) state) = Complete.point depth state :=
  previous_source depth (sourcePoint state)

theorem previous_surjective (depth : Nat) : Function.Surjective (previous depth) := by
  intro value
  obtain ⟨source, same⟩ := full_source_surjective (Fock.actions depth) (Fock.observer depth) (.inl ()) value
  exact ⟨sourceMap (Fock.actions (depth + 1) (.inl ())) (inventory (Fock.actions (depth + 1)) (Fock.observer (depth + 1))) source,
    (previous_source depth source).trans same⟩

end
end SourceGeneratedActionWords.Fock.Dynamic
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Bounds.Source

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025.BasinRefinement.SourceSignedEvaluator
open scoped BigOperators
noncomputable section

theorem finset_sum_holds {α : Type*} [DecidableEq α] (S : Finset α)
    (bounds : α → Pair) (value : α → ℝ)
    (each : ∀ a ∈ S, Holds (bounds a) (value a)) :
    Holds (∑ a ∈ S, bounds a) (∑ a ∈ S, value a) := by
  induction S using Finset.induction_on with
  | empty => simp [Holds]
  | @insert a S ha ih =>
    have tail : ∀ b ∈ S, Holds (bounds b) (value b) := by
      intro b hb
      exact each b (Finset.mem_insert_of_mem hb)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have eqPair : add (bounds a) (∑ b ∈ S, bounds b) =
        bounds a + ∑ b ∈ S, bounds b := rfl
    rw [← eqPair]
    exact add_holds (bounds a) (∑ b ∈ S, bounds b)
        (value a) (∑ b ∈ S, value b)
        (each a (Finset.mem_insert_self a S)) (ih tail)

theorem list_sum_holds {α : Type*} (items : List α)
    (bounds : α → Pair) (value : α → ℝ)
    (each : ∀ a ∈ items, Holds (bounds a) (value a)) :
    Holds (items.map bounds).sum (items.map value).sum := by
  induction items with
  | nil => simp [Holds]
  | cons a rest ih =>
    have tail : ∀ b ∈ rest, Holds (bounds b) (value b) := by
      intro b hb
      exact each b (by simp [hb])
    simp only [List.map_cons, List.sum_cons]
    have eqPair : add (bounds a) (rest.map bounds).sum =
        bounds a + (rest.map bounds).sum := rfl
    rw [← eqPair]
    exact add_holds _ _ _ _ (each a (by simp)) (ih tail)

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

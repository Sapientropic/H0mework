import H0mework.Chemistry.LAlanineContinuousChecks.GroupAssembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields

open SourceGaussianModel SourceSignedEvaluator SourceFiniteData SourceRectangle SourceRectangleChecks

abbrev LowJet := Fin 10
def fullJet (j : LowJet) : Jet := ⟨j.val, Nat.lt_trans j.isLt (by decide)⟩

theorem low_order (j : LowJet) (axis : Fin 3) : (sourceOrder (fullJet j) axis).val < 3 := by
  fin_cases j <;> fin_cases axis <;> decide +kernel

theorem groupTerm_commutes_at (f : Field)
    (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (expComputed : ∀ g, expCache g = exponential (radialPair (groupTerm g) (actualBox f))
      (groupSteps f g).1 (groupSteps f g).2)
    (polyComputed : ∀ g axis p d, polyCache g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) (actualBox f) axis))
    (basis : Basis) (j : Jet) (t : {t // t ∈ source_terms basis}) :
    groupCachedTerm expCache polyCache basis j t =
      termPair t.val (multiindex j) (actualBox f) (steps f t.val).1 (steps f t.val).2 := by
  unfold groupCachedTerm
  apply cachedTerm_commutes
  · rw [expComputed, source_radial_same_group f basis t.val t.property]
    rfl
  · intro axis
    rw [polyComputed]
    have conditions := registered_group_components basis t.val t.property
    simp only [sourcePower, sourceOrder]
    rw [conditions.1, relative_same_group t.val (groupTerm (sourceGroup basis t.val t.property))
      (actualBox f) conditions.2 axis]

theorem groupOrbital_commutes_at (f : Field)
    (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (expComputed : ∀ g, expCache g = exponential (radialPair (groupTerm g) (actualBox f))
      (groupSteps f g).1 (groupSteps f g).2)
    (polyComputed : ∀ g axis p d, polyCache g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) (actualBox f) axis))
    (basis : Basis) (j : Jet) :
    groupCachedOrbital expCache polyCache basis j =
      orbitalPair (source_terms basis) (multiindex j) (actualBox f) (steps f) := by
  unfold groupCachedOrbital orbitalPair
  congr 1
  have h : (source_terms basis).attach.map (groupCachedTerm expCache polyCache basis j) =
      (source_terms basis).attach.map
        (fun t => termPair t.val (multiindex j) (actualBox f) (steps f t.val).1 (steps f t.val).2) := by
    apply List.map_congr_left
    intro t _
    exact groupTerm_commutes_at f expCache polyCache expComputed polyComputed basis j t
  rw [h]
  exact List.attach_map_val (f := fun t : Term =>
    termPair t (multiindex j) (actualBox f) (steps f t).1 (steps f t).2)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields

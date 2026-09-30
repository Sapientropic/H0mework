import H0mework.Chemistry.LAlanineSourceMatrix.Assembly

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeCellSource

open SourceGaussianModel SourceSignedEvaluator SourceFiniteData SourceRectangle SourceRectangleChecks

noncomputable section

def sourceStepsAt (reductions : Group → ℕ × ℕ) (term : Term) : ℕ × ℕ :=
  reductions (lookupGroup term)

theorem source_reduction_at (box : Rectangle) (reductions : Group → ℕ × ℕ)
    (valid : ∀ g, TermReductionValid (groupTerm g) box (reductions g).1 (reductions g).2)
    (basis : Basis) (term : Term) (member : term ∈ source_terms basis) :
    TermReductionValid term box (sourceStepsAt reductions term).1 (sourceStepsAt reductions term).2 := by
  have components := registered_group_components basis term member
  have radial := radial_same_group term (groupTerm (sourceGroup basis term member)) box components.2 components.1
  unfold sourceStepsAt TermReductionValid
  rw [lookupGroup_registered basis term member, radial]
  exact valid (sourceGroup basis term member)

theorem source_group_term_at (box : Rectangle) (reductions : Group → ℕ × ℕ)
    (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (expComputed : ∀ g, expCache g = exponential (radialPair (groupTerm g) box)
      (reductions g).1 (reductions g).2)
    (polyComputed : ∀ g axis p d, polyCache g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) box axis))
    (basis : Basis) (j : Jet) (term : {t // t ∈ source_terms basis}) :
    groupCachedTerm expCache polyCache basis j term =
      termPair term.val (multiindex j) box (sourceStepsAt reductions term.val).1
        (sourceStepsAt reductions term.val).2 := by
  have components := registered_group_components basis term.val term.property
  unfold groupCachedTerm
  apply cachedTerm_commutes
  · rw [expComputed, ← radial_same_group term.val
      (groupTerm (sourceGroup basis term.val term.property)) box components.2 components.1]
    simp only [sourceStepsAt, lookupGroup_registered basis term.val term.property]
  · intro axis
    rw [polyComputed]
    simp only [sourcePower, sourceOrder]
    rw [components.1, relative_same_group term.val
      (groupTerm (sourceGroup basis term.val term.property)) box components.2 axis]

theorem source_group_orbital_at (box : Rectangle) (reductions : Group → ℕ × ℕ)
    (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (expComputed : ∀ g, expCache g = exponential (radialPair (groupTerm g) box)
      (reductions g).1 (reductions g).2)
    (polyComputed : ∀ g axis p d, polyCache g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) box axis))
    (basis : Basis) (j : Jet) :
    groupCachedOrbital expCache polyCache basis j =
      orbitalPair (source_terms basis) (multiindex j) box (sourceStepsAt reductions) := by
  unfold groupCachedOrbital orbitalPair
  congr 1
  have same : (source_terms basis).attach.map (groupCachedTerm expCache polyCache basis j) =
      (source_terms basis).attach.map (fun term => termPair term.val (multiindex j) box
        (sourceStepsAt reductions term.val).1 (sourceStepsAt reductions term.val).2) := by
    apply List.map_congr_left
    intro term _
    exact source_group_term_at box reductions expCache polyCache expComputed polyComputed basis j term
  rw [same]
  exact List.attach_map_val (f := fun term : Term => termPair term (multiindex j) box
    (sourceStepsAt reductions term).1 (sourceStepsAt reductions term).2)

theorem source_group_orbital_contains (box : Rectangle) (reductions : Group → ℕ × ℕ)
    (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (expComputed : ∀ g, expCache g = exponential (radialPair (groupTerm g) box)
      (reductions g).1 (reductions g).2)
    (polyComputed : ∀ g axis p d, polyCache g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) box axis))
    (valid : ∀ g, TermReductionValid (groupTerm g) box (reductions g).1 (reductions g).2)
    (basis : Basis) (j : Jet) (x : Point) (inside : InRectangle box x) :
    Holds (groupCachedOrbital expCache polyCache basis j) (orbital (source_terms basis) (multiindex j) x) := by
  rw [source_group_orbital_at box reductions expCache polyCache expComputed polyComputed basis j]
  exact orbitalPair_contains (source_terms basis) (multiindex j) box (sourceStepsAt reductions)
    (fun term member => source_reduction_at box reductions valid basis term member) x inside

end
end LAlanine40K2025.BasinRefinement.WholeCellSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

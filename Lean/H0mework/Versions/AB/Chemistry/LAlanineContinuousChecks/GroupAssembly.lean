import H0mework.Chemistry.LAlanineContinuousChecks.Cached
import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.SourceIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks

open SourceGaussianModel SourceSignedEvaluator SourceFiniteData SourceRectangle

def powersRegistered (basis : Basis) : Prop :=
  (source_terms basis).all (fun t => decide (∀ axis : Fin 3, t.powers axis < 3)) = true

theorem all_powers_registered : ∀ basis : Basis, powersRegistered basis := by
  unfold powersRegistered
  decide +kernel

theorem source_power_lt (basis : Basis) (term : Term) (member : term ∈ source_terms basis) (axis : Fin 3) :
    term.powers axis < 3 := by
  have h := List.all_eq_true.mp (all_powers_registered basis) term member
  exact of_decide_eq_true h axis

theorem all_jet_orders_registered : ∀ j : Jet, ∀ axis : Fin 3, multiindex j axis < 4 := by
  decide +kernel

noncomputable section

def sourcePower (basis : Basis) (term : Term) (member : term ∈ source_terms basis) (axis : Fin 3) : Fin 3 :=
  ⟨term.powers axis, source_power_lt basis term member axis⟩

def sourceOrder (j : Jet) (axis : Fin 3) : Fin 4 := ⟨multiindex j axis, all_jet_orders_registered j axis⟩

def groupCachedTerm (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (basis : Basis) (j : Jet) (t : {t // t ∈ source_terms basis}) : Pair :=
  let g := sourceGroup basis t.val t.property
  cachedTerm t.val.weight (expCache g)
    (fun axis => polyCache g axis (sourcePower basis t.val t.property axis) (sourceOrder j axis))

def groupCachedOrbital (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (basis : Basis) (j : Jet) : Pair :=
  ((source_terms basis).attach.map (groupCachedTerm expCache polyCache basis j)).foldr add (point 0)

theorem registered_group_components (basis : Basis) (term : Term) (member : term ∈ source_terms basis) :
    term.exponent = (groupTerm (sourceGroup basis term member)).exponent ∧
      term.centre = (groupTerm (sourceGroup basis term member)).centre := by
  have h := of_decide_eq_true (List.all_eq_true.mp (actual_radial_agreement basis) term member)
  rw [lookupGroup_registered basis term member] at h
  refine ⟨h.1, ?_⟩
  funext axis
  fin_cases axis
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem groupCachedTerm_commutes
    (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (expComputed : ∀ g, expCache g = exponential (radialPair (groupTerm g) (actualBox 0))
      (groupSteps 0 g).1 (groupSteps 0 g).2)
    (polyComputed : ∀ g axis p d, polyCache g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) (actualBox 0) axis))
    (basis : Basis) (j : Jet) (t : {t // t ∈ source_terms basis}) :
    groupCachedTerm expCache polyCache basis j t =
      termPair t.val (multiindex j) (actualBox 0) (steps 0 t.val).1 (steps 0 t.val).2 := by
  unfold groupCachedTerm
  apply cachedTerm_commutes
  · rw [expComputed, source_radial_same_group 0 basis t.val t.property]
    rfl
  · intro axis
    rw [polyComputed]
    have conditions := registered_group_components basis t.val t.property
    simp only [sourcePower, sourceOrder]
    rw [conditions.1, relative_same_group t.val (groupTerm (sourceGroup basis t.val t.property))
      (actualBox 0) conditions.2 axis]

theorem groupCachedOrbital_commutes
    (expCache : Group → Pair) (polyCache : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (expComputed : ∀ g, expCache g = exponential (radialPair (groupTerm g) (actualBox 0))
      (groupSteps 0 g).1 (groupSteps 0 g).2)
    (polyComputed : ∀ g axis p d, polyCache g axis p d =
      jetHorner (groupTerm g).exponent p.val d.val (relative (groupTerm g) (actualBox 0) axis))
    (basis : Basis) (j : Jet) :
    groupCachedOrbital expCache polyCache basis j =
      orbitalPair (source_terms basis) (multiindex j) (actualBox 0) (steps 0) := by
  unfold groupCachedOrbital orbitalPair
  congr 1
  have h : (source_terms basis).attach.map (groupCachedTerm expCache polyCache basis j) =
      (source_terms basis).attach.map
        (fun t => termPair t.val (multiindex j) (actualBox 0) (steps 0 t.val).1 (steps 0 t.val).2) := by
    apply List.map_congr_left
    intro t _
    exact groupCachedTerm_commutes expCache polyCache expComputed polyComputed basis j t
  rw [h]
  exact List.attach_map_val (f := fun t : Term =>
    termPair t (multiindex j) (actualBox 0) (steps 0 t).1 (steps 0 t).2)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks

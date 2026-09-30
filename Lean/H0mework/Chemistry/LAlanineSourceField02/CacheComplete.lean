import H0mework.Chemistry.LAlanineSourceField02.CacheGroupRows
import H0mework.Chemistry.LAlanineSourceField02.CacheAORows

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field2

open Lean Elab Tactic SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData

theorem relative_eq_source (g : Group) : ∀ axis : Fin 3,
    cachedRelative g axis = relative (groupTerm g) (actualBox 2) axis := by
  change ∀ axis, cachedRelative g axis = sourceRelative g axis
  fin_cases g
  closeGeneratedLowGroups "relativeRow"

theorem radial_eq_source (g : Group) : cachedRadial g = radialPair (groupTerm g) (actualBox 2) := by
  change cachedRadial g = sourceRadial g
  fin_cases g
  closeGeneratedLowGroups "Checks.radial_"

theorem exp_from_radial (g : Group) : cachedExp g = sourceExpFromRadial g := by
  fin_cases g
  closeGeneratedLowGroups "Checks.exp_"

theorem exp_eq_source (g : Group) :
    cachedExp g = exponential (radialPair (groupTerm g) (actualBox 2)) (groupSteps 2 g).1 (groupSteps 2 g).2 := by
  rw [exp_from_radial]
  unfold sourceExpFromRadial
  rw [radial_eq_source]

theorem polynomial_from_relative (g : Group) : ∀ axis power order : Fin 3,
    cachedPoly g axis power order = sourcePolyFromRelative g axis power order := by
  fin_cases g
  closeGeneratedLowGroups "polynomialRow"

theorem polynomial_eq_source (g : Group) (axis power order : Fin 3) :
    cachedPoly g axis power order =
      jetHorner (groupTerm g).exponent power.val order.val (relative (groupTerm g) (actualBox 2) axis) := by
  have h := polynomial_from_relative g axis power order
  unfold sourcePolyFromRelative at h
  rw [relative_eq_source, ← (actual_group_terms g).2.1] at h
  exact h

theorem assemblyPoly_eq_source (g : Group) (axis power : Fin 3) (order : Fin 4) :
    assemblyPoly g axis power order =
      jetHorner (groupTerm g).exponent power.val order.val (relative (groupTerm g) (actualBox 2) axis) := by
  unfold assemblyPoly
  split_ifs with h
  · exact polynomial_eq_source g axis power ⟨order.val,h⟩
  · rfl

theorem all_cached_reductions (g : Group) : reductionValid g := by
  fin_cases g
  closeGeneratedLowGroups "Checks.reduction_"

theorem all_group_reductions (g : Group) :
    TermReductionValid (groupTerm g) (actualBox 2) (groupSteps 2 g).1 (groupSteps 2 g).2 := by
  have h := all_cached_reductions g
  unfold reductionValid at h
  rw [radial_eq_source] at h
  exact h

theorem calculatedAO_eq_source (j : LowJet) (basis : Basis) : calculatedAO j basis = sourceAO j basis := by
  fin_cases basis
  closeGeneratedLowAOs j

theorem calculatedAO_eq_orbitalPair (j : LowJet) (basis : Basis) :
    calculatedAO j basis = orbitalPair (source_terms basis) (multiindex (fullJet j)) (actualBox 2) (steps 2) := by
  rw [calculatedAO_eq_source]
  exact groupOrbital_commutes_at 2 cachedExp assemblyPoly exp_eq_source assemblyPoly_eq_source basis (fullJet j)

theorem calculatedAO_contains (j : LowJet) (basis : Basis) (x : Point) (inside : InRectangle (actualBox 2) x) :
    Holds (calculatedAO j basis) (orbital (source_terms basis) (multiindex (fullJet j)) x) := by
  rw [calculatedAO_eq_orbitalPair]
  exact orbitalPair_contains (source_terms basis) (multiindex (fullJet j)) (actualBox 2) (steps 2)
    (reduction_from_groups 2 all_group_reductions basis) x inside

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field2

import H0mework.Chemistry.LAlanineSourceField01.CacheGroupRows
import H0mework.Chemistry.LAlanineSourceField01.CacheAORows

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field1

open Lean Elab Tactic SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData

elab "closeLowFieldGroups " stem:str : tactic => do
  let goals ← getGoals
  unless goals.length == 94 do throwError "complete original group census"
  let base := (← getCurrNamespace).toString
  for (goal,g) in goals.zipIdx do
    goal.assign (Lean.mkConst (base ++ "." ++ stem.getString ++ toString g).toName)
  setGoals []

elab "closeLowFieldAOs " jet:term : tactic => withMainContext do
  let goals ← getGoals
  unless goals.length == 98 do throwError "complete original AO census"
  let j ← Term.elabTerm jet none
  let base := (← getCurrNamespace).toString
  for (goal,b) in goals.zipIdx do
    goal.assign (mkApp (Lean.mkConst (base ++ ".aoRowComputed" ++ toString b).toName) j)
  setGoals []

theorem relative_eq_source (g : Group) : ∀ axis : Fin 3,
    cachedRelative g axis = relative (groupTerm g) (actualBox 1) axis := by
  change ∀ axis, cachedRelative g axis = sourceRelative g axis
  fin_cases g
  closeLowFieldGroups "relativeRow"

theorem radial_eq_source (g : Group) : cachedRadial g = radialPair (groupTerm g) (actualBox 1) := by
  change cachedRadial g = sourceRadial g
  fin_cases g
  closeLowFieldGroups "Checks.radial_"

theorem exp_from_radial (g : Group) : cachedExp g = sourceExpFromRadial g := by
  fin_cases g
  closeLowFieldGroups "Checks.exp_"

theorem exp_eq_source (g : Group) :
    cachedExp g = exponential (radialPair (groupTerm g) (actualBox 1)) (groupSteps 1 g).1 (groupSteps 1 g).2 := by
  rw [exp_from_radial]
  unfold sourceExpFromRadial
  rw [radial_eq_source]

theorem polynomial_from_relative (g : Group) : ∀ axis power order : Fin 3,
    cachedPoly g axis power order = sourcePolyFromRelative g axis power order := by
  fin_cases g
  closeLowFieldGroups "polynomialRow"

theorem polynomial_eq_source (g : Group) (axis power order : Fin 3) :
    cachedPoly g axis power order =
      jetHorner (groupTerm g).exponent power.val order.val (relative (groupTerm g) (actualBox 1) axis) := by
  have h := polynomial_from_relative g axis power order
  unfold sourcePolyFromRelative at h
  rw [relative_eq_source, ← (actual_group_terms g).2.1] at h
  exact h

theorem assemblyPoly_eq_source (g : Group) (axis power : Fin 3) (order : Fin 4) :
    assemblyPoly g axis power order =
      jetHorner (groupTerm g).exponent power.val order.val (relative (groupTerm g) (actualBox 1) axis) := by
  unfold assemblyPoly
  split_ifs with h
  · exact polynomial_eq_source g axis power ⟨order.val,h⟩
  · rfl

theorem all_cached_reductions (g : Group) : reductionValid g := by
  fin_cases g
  closeLowFieldGroups "Checks.reduction_"

theorem all_group_reductions (g : Group) :
    TermReductionValid (groupTerm g) (actualBox 1) (groupSteps 1 g).1 (groupSteps 1 g).2 := by
  have h := all_cached_reductions g
  unfold reductionValid at h
  rw [radial_eq_source] at h
  exact h

theorem calculatedAO_eq_source (j : LowJet) (basis : Basis) : calculatedAO j basis = sourceAO j basis := by
  fin_cases basis
  closeLowFieldAOs j

theorem calculatedAO_eq_orbitalPair (j : LowJet) (basis : Basis) :
    calculatedAO j basis = orbitalPair (source_terms basis) (multiindex (fullJet j)) (actualBox 1) (steps 1) := by
  rw [calculatedAO_eq_source]
  exact groupOrbital_commutes_at 1 cachedExp assemblyPoly exp_eq_source assemblyPoly_eq_source basis (fullJet j)

theorem calculatedAO_contains (j : LowJet) (basis : Basis) (x : Point) (inside : InRectangle (actualBox 1) x) :
    Holds (calculatedAO j basis) (orbital (source_terms basis) (multiindex (fullJet j)) x) := by
  rw [calculatedAO_eq_orbitalPair]
  exact orbitalPair_contains (source_terms basis) (multiindex (fullJet j)) (actualBox 1) (steps 1)
    (reduction_from_groups 1 all_group_reductions basis) x inside

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field1

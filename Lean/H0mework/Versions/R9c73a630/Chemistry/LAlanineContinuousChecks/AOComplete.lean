import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AORows
import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.Reductions

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks

open Lean Elab Tactic SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceGroupCache

elab "closeCalculatedAOs " stem:ident " at " jet:term : tactic => withMainContext do
  let goals ← getGoals
  unless goals.length == 98 do throwError "complete original AO census required"
  let j ← Term.elabTerm jet none
  let base := (← getCurrNamespace)
  for (goal, i) in goals.zipIdx do
    goal.assign (mkApp (Lean.mkConst (base ++ Name.mkSimple s!"{stem.getId.toString}{i}")) j)
  setGoals []

theorem calculatedAO_eq_groupCached (j : Jet) (basis : Basis) :
    calculatedAO j basis = groupCachedOrbital cachedExp cachedPoly basis j := by
  fin_cases basis
  closeCalculatedAOs cachedAORow at j

theorem calculatedAO_eq_reported (j : Jet) (basis : Basis) :
    calculatedAO j basis = reportedAO j basis := by
  fin_cases basis
  closeCalculatedAOs reportedAORow at j

theorem calculatedAO_eq_orbitalPair (j : Jet) (basis : Basis) :
    calculatedAO j basis = orbitalPair (source_terms basis) (multiindex j) (actualBox 0) (steps 0) :=
  (calculatedAO_eq_groupCached j basis).trans
    (groupCachedOrbital_commutes cachedExp cachedPoly exp_eq_source poly_eq_source basis j)

theorem calculatedAO_contains (j : Jet) (basis : Basis) (x : Point)
    (inside : InRectangle (actualBox 0) x) :
    Holds (calculatedAO j basis) (orbital (source_terms basis) (multiindex j) x) := by
  rw [calculatedAO_eq_orbitalPair]
  exact orbitalPair_contains (source_terms basis) (multiindex j) (actualBox 0) (steps 0)
    (all_source_reductions basis) x inside

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceRectangleChecks

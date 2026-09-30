import H0mework.Chemistry.LAlanineTrueTubeCache.Certificate

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeCache

open Lean Elab Command

private def command (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error error => throwError error
  | .ok commandSyntax => elabCommand commandSyntax

/-- A field keeps its own literal rows; all fields share this source accessor factory. -/
elab "generateTrueTubeFieldAccessors " index:num : command => do
  let f := index.getNat
  unless 0 < f && f < 3 do throwError "registered field accessors"
  command "noncomputable section"
  command "def cachedRelative (g : Group) (axis : Fin 3) : Pair := integerInterval ((groupRows[g.val]!).relative[axis.val]!)"
  command "def cachedRadial (g : Group) : Pair := integerInterval (groupRows[g.val]!).radial"
  command "def cachedExp (g : Group) : Pair := integerInterval (groupRows[g.val]!).exponential"
  command "def cachedPoly (g : Group) (axis power order : Fin 3) : Pair := integerInterval ((((groupRows[g.val]!).polynomial[axis.val]!)[power.val]!)[order.val]!)"
  command "def calculatedAO (j : LowJet) (basis : Basis) : Pair := integerInterval ((aoRows[basis.val]!)[j.val]!)"
  command s!"def assemblyPoly (g : Group) (axis power : Fin 3) (order : Fin 4) : Pair :=
    if h : order.val < 3 then cachedPoly g axis power ⟨order.val,h⟩
    else jetHorner (groupTerm g).exponent power.val order.val (relative (groupTerm g) (TrueTubeSource.box {f}) axis)"
  command s!"def sourceRelative (g : Group) (axis : Fin 3) : Pair := relative (groupTerm g) (TrueTubeSource.box {f}) axis"
  command s!"def sourceRadial (g : Group) : Pair := radialPair (groupTerm g) (TrueTubeSource.box {f})"
  command s!"def sourceExpFromRadial (g : Group) : Pair := exponential (cachedRadial g) (TrueTubeSource.reductions {f} g).1 (TrueTubeSource.reductions {f} g).2"
  command "def sourcePolyFromRelative (g : Group) (axis power order : Fin 3) : Pair := jetHorner (groupExponent g) power.val order.val (cachedRelative g axis)"
  command "def sourceAO (j : LowJet) (basis : Basis) : Pair := groupCachedOrbital cachedExp assemblyPoly basis (fullJet j)"
  command s!"def reductionValid (g : Group) : Prop :=
    |SourceExponential.reducedArgument (cachedRadial g).1 (TrueTubeSource.reductions {f} g).1| ≤ 1/2 ∧
    |SourceExponential.reducedArgument (cachedRadial g).2 (TrueTubeSource.reductions {f} g).2| ≤ 1/2"
  command "end"

/-- Reuse the original group/orbital proof once per registered field; no numerical computation here. -/
elab "assembleTrueTubeField " index:num : command => do
  let f := index.getNat
  unless 0 < f && f < 3 do throwError "registered field assembly"
  command s!"theorem relative_eq_source (g : Group) : ∀ axis : Fin 3,
      cachedRelative g axis = relative (groupTerm g) (TrueTubeSource.box {f}) axis := by
    change ∀ axis, cachedRelative g axis = sourceRelative g axis
    fin_cases g
    closeGeneratedLowGroups \"relativeRow\""
  command s!"theorem radial_eq_source (g : Group) :
      cachedRadial g = radialPair (groupTerm g) (TrueTubeSource.box {f}) := by
    change cachedRadial g = sourceRadial g
    fin_cases g
    closeGeneratedLowGroups \"Checks.radial_\""
  command "theorem exp_from_radial (g : Group) : cachedExp g = sourceExpFromRadial g := by
    fin_cases g
    closeGeneratedLowGroups \"Checks.exp_\""
  command s!"theorem exp_eq_source (g : Group) : cachedExp g =
      exponential (radialPair (groupTerm g) (TrueTubeSource.box {f}))
        (TrueTubeSource.reductions {f} g).1 (TrueTubeSource.reductions {f} g).2 := by
    rw [exp_from_radial]
    unfold sourceExpFromRadial
    rw [radial_eq_source]"
  command "theorem polynomial_from_relative (g : Group) : ∀ axis power order : Fin 3,
      cachedPoly g axis power order = sourcePolyFromRelative g axis power order := by
    fin_cases g
    closeGeneratedLowGroups \"polynomialRow\""
  command s!"theorem polynomial_eq_source (g : Group) (axis power order : Fin 3) :
      cachedPoly g axis power order = jetHorner (groupTerm g).exponent power.val order.val
        (relative (groupTerm g) (TrueTubeSource.box {f}) axis) := by
    have h := polynomial_from_relative g axis power order
    unfold sourcePolyFromRelative at h
    rw [relative_eq_source, ← (actual_group_terms g).2.1] at h
    exact h"
  command s!"theorem assemblyPoly_eq_source (g : Group) (axis power : Fin 3) (order : Fin 4) :
      assemblyPoly g axis power order = jetHorner (groupTerm g).exponent power.val order.val
        (relative (groupTerm g) (TrueTubeSource.box {f}) axis) := by
    unfold assemblyPoly
    split_ifs with h
    · exact polynomial_eq_source g axis power ⟨order.val,h⟩
    · rfl"
  command "theorem all_cached_reductions (g : Group) : reductionValid g := by
    fin_cases g
    closeGeneratedLowGroups \"Checks.reduction_\""
  command s!"theorem all_group_reductions (g : Group) :
      TermReductionValid (groupTerm g) (TrueTubeSource.box {f})
        (TrueTubeSource.reductions {f} g).1 (TrueTubeSource.reductions {f} g).2 := by
    have h := all_cached_reductions g
    unfold reductionValid at h
    rw [radial_eq_source] at h
    exact h"
  command "theorem calculatedAO_eq_source (j : LowJet) (basis : Basis) :
      calculatedAO j basis = sourceAO j basis := by
    fin_cases basis
    closeGeneratedLowAOs j"
  command s!"theorem calculatedAO_eq_orbitalPair (j : LowJet) (basis : Basis) :
      calculatedAO j basis = orbitalPair (source_terms basis) (multiindex (fullJet j))
        (TrueTubeSource.box {f}) (WholeCellSource.sourceStepsAt (TrueTubeSource.reductions {f})) := by
    rw [calculatedAO_eq_source]
    exact WholeCellSource.source_group_orbital_at (TrueTubeSource.box {f}) (TrueTubeSource.reductions {f})
      cachedExp assemblyPoly exp_eq_source assemblyPoly_eq_source basis (fullJet j)"
  command s!"theorem calculatedAO_contains (j : LowJet) (basis : Basis) (x : Point)
      (inside : InRectangle (TrueTubeSource.box {f}) x) :
      Holds (calculatedAO j basis) (orbital (source_terms basis) (multiindex (fullJet j)) x) := by
    rw [calculatedAO_eq_source]
    exact WholeCellSource.source_group_orbital_contains (TrueTubeSource.box {f}) (TrueTubeSource.reductions {f})
      cachedExp assemblyPoly exp_eq_source assemblyPoly_eq_source all_group_reductions basis (fullJet j) x inside"

end LAlanine40K2025.BasinRefinement.TrueTubeCache
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandCalculation.Fold

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation

open SourceSignedEvaluator SourceIntegerGrid SourceRectangleChecks SourceRectangle SourceFiniteData SourceFields
noncomputable section

/-- Preserve the source's multiplication and summation order on the exact integer grid. -/
def orbitalIntegers (exps : Group → Pair) (polys : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (b : Basis) (j : LowJet) : Interval :=
  ((source_terms b).attach.map (fun term => encode (groupCachedTerm exps polys b (fullJet j) term))).foldr
    addInteger (0,0)

 theorem orbital_integers_commute (exps : Group → Pair) (polys : Group → Fin 3 → Fin 3 → Fin 4 → Pair)
    (b : Basis) (j : LowJet) :
    grid (orbitalIntegers exps polys b j) = groupCachedOrbital exps polys b (fullJet j) :=
  grid_mapped_fold (source_terms b).attach (groupCachedTerm exps polys b (fullJet j))
    (fun term => encode_cachedTerm term.val.weight
      (exps (sourceGroup b term.val term.property))
      (fun axis => polys (sourceGroup b term.val term.property) axis
        (sourcePower b term.val term.property axis) (sourceOrder (fullJet j) axis)))


end
end LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

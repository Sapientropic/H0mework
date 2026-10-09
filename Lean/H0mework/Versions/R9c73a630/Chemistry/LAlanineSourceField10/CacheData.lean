import H0mework.Versions.R9c73a630.Chemistry.LAlanineSourceMatrix.Reifier

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field10

open SourceRectangle SourceSignedEvaluator SourceGaussianModel SourceFiniteData SourceRectangleChecks

generateLowFieldCache 10

noncomputable section

def cachedRelative (g : Group) (axis : Fin 3) : Pair := integerInterval ((groupRows[g.val]!).relative[axis.val]!)
def cachedRadial (g : Group) : Pair := integerInterval (groupRows[g.val]!).radial
def cachedExp (g : Group) : Pair := integerInterval (groupRows[g.val]!).exponential
def cachedPoly (g : Group) (axis power order : Fin 3) : Pair :=
  integerInterval ((((groupRows[g.val]!).polynomial[axis.val]!)[power.val]!)[order.val]!)
def calculatedAO (j : LowJet) (basis : Basis) : Pair := integerInterval ((aoRows[basis.val]!)[j.val]!)

/-- Uncached higher orders retain the original computation; low jets never enter this branch. -/
def assemblyPoly (g : Group) (axis power : Fin 3) (order : Fin 4) : Pair :=
  if h : order.val < 3 then cachedPoly g axis power ⟨order.val,h⟩
  else jetHorner (groupTerm g).exponent power.val order.val (relative (groupTerm g) (actualBox 10) axis)

def sourceRelative (g : Group) (axis : Fin 3) : Pair := relative (groupTerm g) (actualBox 10) axis
def sourceRadial (g : Group) : Pair := radialPair (groupTerm g) (actualBox 10)
def sourceExpFromRadial (g : Group) : Pair :=
  exponential (cachedRadial g) (groupSteps 10 g).1 (groupSteps 10 g).2
def sourcePolyFromRelative (g : Group) (axis power order : Fin 3) : Pair :=
  jetHorner (groupExponent g) power.val order.val (cachedRelative g axis)
def sourceAO (j : LowJet) (basis : Basis) : Pair :=
  groupCachedOrbital cachedExp assemblyPoly basis (fullJet j)

def reductionValid (g : Group) : Prop :=
  |SourceExponential.reducedArgument (cachedRadial g).1 (groupSteps 10 g).1| ≤ 1/2 ∧
    |SourceExponential.reducedArgument (cachedRadial g).2 (groupSteps 10 g).2| ≤ 1/2

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFields.Field10

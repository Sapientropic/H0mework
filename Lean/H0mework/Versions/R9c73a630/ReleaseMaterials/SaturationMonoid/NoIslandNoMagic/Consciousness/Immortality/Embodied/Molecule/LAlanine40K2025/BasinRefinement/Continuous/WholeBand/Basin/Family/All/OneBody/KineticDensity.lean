import H0mework.Versions.AB.Chemistry.LAlanineGradient.Model
set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody
open SourceGaussianModel SourceFiniteData ContinuousGradient
open scoped BigOperators
noncomputable section

def gradientKinetic (x : Point) : ℝ :=
  (1/2 : ℝ) * ∑ a : Fin 3, bilinear sourceTerms densityMatrix (raise zeroJet a) (raise zeroJet a) x

def laplacianKinetic (x : Point) : ℝ :=
  -(1/4 : ℝ) * ∑ a : Fin 3,
    (bilinear sourceTerms densityMatrix (raise (raise zeroJet a) a) zeroJet x +
      bilinear sourceTerms densityMatrix zeroJet (raise (raise zeroJet a) a) x)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.OneBody

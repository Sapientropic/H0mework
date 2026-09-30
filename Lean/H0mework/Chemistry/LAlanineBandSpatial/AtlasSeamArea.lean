import H0mework.Chemistry.LAlanineBandSpatial.AtlasSeamDerivative
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
open SourceGaussianModel ContinuousGradient WholeCellBoundary Matrix
noncomputable section

def leftArea (s : Seam) (u : FacePoint) : Point :=
  -(leftDerivative s u (Pi.single 0 1) ⨯₃ leftDerivative s u (Pi.single 1 1))
def rightArea (s : Seam) (u : FacePoint) : Point :=
  rightDerivative s u (Pi.single 0 1) ⨯₃ rightDerivative s u (Pi.single 1 1)

theorem actual_area_cancellation (fields : Fields) (bounds : Bounds) (s : Seam)
    (u : FacePoint) (inside : u ∈ domain) : leftArea s u + rightArea s u = 0 := by
  rw [leftArea,rightArea,actual_tangential_derivatives_agree fields bounds s u inside,neg_add_cancel]

def leftFlux (s : Seam) (u : FacePoint) : ℝ := sourceGradient (leftMap s u) ⬝ᵥ leftArea s u
def rightFlux (s : Seam) (u : FacePoint) : ℝ := sourceGradient (rightMap s u) ⬝ᵥ rightArea s u

theorem actual_flux_cancellation (fields : Fields) (bounds : Bounds) (s : Seam)
    (u : FacePoint) (inside : u ∈ domain) : leftFlux s u + rightFlux s u = 0 := by
  have agree : leftMap s u = rightMap s u := original_maps_agree s u inside
  rw [leftFlux,rightFlux,agree,← dotProduct_add,actual_area_cancellation fields bounds s u inside,dotProduct_zero]

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

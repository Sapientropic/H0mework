import H0mework.Chemistry.LAlanineBandSpatial.AtlasSeamSource

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
open SourceGaussianModel WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter WholeCellBoundary WholeCellBoundary.Geometry Set
noncomputable section

def leftMap (s : Seam) : FacePoint → Point := sourceParameterMap (leftCell s) ∘ parameter s
def rightMap (s : Seam) : FacePoint → Point := sourceParameterMap (rightCell s) ∘ parameter s

def leftDerivative (s : Seam) (u : FacePoint) : FacePoint →L[ℝ] Point :=
  (trueJacobian (leftCell s) (parameter s u)).comp (faceInclusion 1)
def rightDerivative (s : Seam) (u : FacePoint) : FacePoint →L[ℝ] Point :=
  (trueJacobian (rightCell s) (parameter s u)).comp (faceInclusion 1)

theorem left_actual_derivative (fields : Fields) (bounds : Bounds) (s : Seam)
    (u : FacePoint) (inside : u ∈ domain) : HasFDerivWithinAt (leftMap s) (leftDerivative s u) domain u :=
  (actualMap_hasFDerivWithinAt (leftCell s) (fields _) (bounds _) _ (parameter_left s u inside)).comp u
    (parameter_hasFDerivAt s u).hasFDerivWithinAt (parameter_left s)

theorem right_actual_derivative (fields : Fields) (bounds : Bounds) (s : Seam)
    (u : FacePoint) (inside : u ∈ domain) : HasFDerivWithinAt (rightMap s) (rightDerivative s u) domain u :=
  (actualMap_hasFDerivWithinAt (rightCell s) (fields _) (bounds _) _ (parameter_right s u inside)).comp u
    (parameter_hasFDerivAt s u).hasFDerivWithinAt (parameter_right s)

/-- Only the common actual two-dimensional restriction determines the seam derivative. -/
theorem actual_tangential_derivatives_agree (fields : Fields) (bounds : Bounds)
    (s : Seam) (u : FacePoint) (inside : u ∈ domain) : leftDerivative s u = rightDerivative s u :=
  domain_uniqueDiff.eq inside (left_actual_derivative fields bounds s u inside)
    ((right_actual_derivative fields bounds s u inside).congr' (original_maps_agree s) inside)

end
end LAlanine40K2025.BasinRefinement.WholeBandAtlas.Seams
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

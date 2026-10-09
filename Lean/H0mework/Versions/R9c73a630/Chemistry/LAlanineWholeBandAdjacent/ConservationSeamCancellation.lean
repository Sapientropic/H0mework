import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationRegularFaces
import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandCell0.BoundaryCapFlux

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentConservation

open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandCell1Actual WholeBandContinuationParameter WholeBandAdjacentGeometry WholeBandCell0Boundary
open WholeCellBoundary WholeCellBoundary.Geometry WholeCellBoundaryArea AdjacentFlow Matrix Set
open scoped Matrix
noncomputable section

def rightSeamParameter (p : FacePoint) : Point := (1 : Fin 3).insertNth (cellV 1 0 : ℝ) p
def rightSeamMap : FacePoint → Point := sourceParameterMap 1 ∘ rightSeamParameter
def rightSeamDerivative (p : FacePoint) : FacePoint →L[ℝ] Point :=
  (trueJacobian 1 (rightSeamParameter p)).comp (faceInclusion 1)
def rightSeamArea (p : FacePoint) : Point :=
  (-1 * axisOrientation (1 : Fin 3) : ℝ) •
    (rightSeamDerivative p (Pi.single 0 1) ⨯₃ rightSeamDerivative p (Pi.single 1 1))
def rightSeamFlux (p : FacePoint) : ℝ := sourceGradient (rightSeamMap p) ⬝ᵥ rightSeamArea p

theorem seamParameters_same (p : FacePoint) : rightSeamParameter p = cell0_faceParameter (1,true) p := by
  change ((1 : Fin 3).insertNth (cellV 1 0 : ℝ) p : Point) =
    ((1 : Fin 3).insertNth (cellV 0 1 : ℝ) p : Point)
  rw [cell0_cell1_literal_seam]

theorem rightSeam_inside (p : FacePoint) (inside : p ∈ cell0_faceDomain 1) : rightSeamParameter p ∈ cellDomain 1 := by
  rw [seamParameters_same]
  have left := cell0_faceParameter_mem (1,true) p inside
  have onSeam := cell0_faceParameter_axis (1,true) p
  exact ((cell0_cell1_domain_intersection _).mpr ⟨left.1,onSeam,left.2.2⟩).2

theorem rightSeamParameter_hasFDerivAt (p : FacePoint) :
    HasFDerivAt rightSeamParameter (faceInclusion 1) p := by
  have same : rightSeamParameter = cell0_faceParameter (1,true) := funext seamParameters_same
  rw [same]
  exact cell0_faceParameter_hasFDerivAt (1,true) p

theorem rightSeamMap_actual_derivative (p : FacePoint) (inside : p ∈ cell0_faceDomain 1) :
    HasFDerivWithinAt rightSeamMap (rightSeamDerivative p) (cell0_faceDomain 1) p :=
  (cell1_actual_parameter_derivative ⟨_,rightSeam_inside p inside⟩).comp p
    (rightSeamParameter_hasFDerivAt p).hasFDerivWithinAt rightSeam_inside

theorem actualSeamMaps_same (p : FacePoint) : rightSeamMap p = cell0_trueFaceMap (1,true) p := by
  change sourceParameterMap 1 (rightSeamParameter p) = _
  rw [seamParameters_same]
  rfl

theorem actualSeamAreas_cancel (p : FacePoint) (inside : p ∈ cell0_faceDomain 1) :
    cell0_trueOrientedArea (1,true) p inside + rightSeamArea p = 0 := by
  have same : rightSeamDerivative p = cell0_trueFaceDerivative (1,true) p inside := by
    unfold rightSeamDerivative
    rw [seamParameters_same]
    rfl
  unfold rightSeamArea
  rw [same]
  change (1 * axisOrientation (1 : Fin 3) : ℝ) • _ + (-1 * axisOrientation (1 : Fin 3) : ℝ) • _ = 0
  simp only [cell0_trueFaceTangent]
  rw [← add_smul]
  simp

theorem actualSeamFluxes_cancel (p : FacePoint) (inside : p ∈ cell0_faceDomain 1) :
    cell0_trueFaceFlux (1,true) p inside + rightSeamFlux p = 0 := by
  rw [cell0_trueFaceFlux,rightSeamFlux,actualSeamMaps_same,← dotProduct_add,actualSeamAreas_cancel p inside,dotProduct_zero]

end
end LAlanine40K2025.BasinRefinement.AdjacentConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

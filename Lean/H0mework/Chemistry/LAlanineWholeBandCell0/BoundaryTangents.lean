import H0mework.Chemistry.LAlanineWholeBandCell0.BoundaryParameterFaces
import H0mework.Chemistry.LAlanineBoundary.GeometryAreaAlgebra

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary

open SourceGaussianModel ContinuousGradient WholeBandActual WholeBandCell0Geometry WholeBandCell0Differential WholeCellBoundary
open WholeCellBoundary.Geometry WholeCellBoundaryArea Matrix Set
open scoped Matrix
noncomputable section

def cell0_trueFaceParameter (face : Face) (p : FacePoint) (inside : p ∈ cell0_faceDomain face.1) : Cell0Point :=
  ⟨cell0_faceParameter face p, cell0_faceParameter_mem face p inside⟩

def cell0_trueFaceMap (face : Face) : FacePoint → Point := cell0ParameterMap ∘ cell0_faceParameter face

def cell0_trueFaceDerivative (face : Face) (p : FacePoint) (inside : p ∈ cell0_faceDomain face.1) :
    FacePoint →L[ℝ] Point :=
  (cell0_trueJacobian (cell0_trueFaceParameter face p inside)).comp (faceInclusion face.1)

theorem cell0_trueFaceMap_hasFDerivWithinAt (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) :
    HasFDerivWithinAt (cell0_trueFaceMap face) (cell0_trueFaceDerivative face p inside)
      (cell0_faceDomain face.1) p :=
  (cell0_actualMap_hasFDerivWithinAt (cell0_trueFaceParameter face p inside)).comp p
    (cell0_faceParameter_hasFDerivAt face p).hasFDerivWithinAt (cell0_faceParameter_mem face)

def cell0_trueFaceTangent (face : Face) (p : FacePoint) (inside : p ∈ cell0_faceDomain face.1)
    (k : Fin 2) : Point := cell0_trueFaceDerivative face p inside (Pi.single k 1)

theorem cell0_trueFaceTangent_eq_column (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) (k : Fin 2) :
    cell0_trueFaceTangent face p inside k =
      cell0_trueJacobian (cell0_trueFaceParameter face p inside) (Pi.single (face.1.succAbove k) 1) := by
  simp only [cell0_trueFaceTangent, cell0_trueFaceDerivative, ContinuousLinearMap.comp_apply,
    faceInclusion_single]

/-- Actual face tangents generate the oriented area, with the original missing-axis parity. -/
def cell0_trueOrientedArea (face : Face) (p : FacePoint) (inside : p ∈ cell0_faceDomain face.1) : Point :=
  ((if face.2 then 1 else -1 : ℝ) * axisOrientation face.1) •
    (cell0_trueFaceTangent face p inside 0 ⨯₃ cell0_trueFaceTangent face p inside 1)

def cell0_trueFaceFlux (face : Face) (p : FacePoint) (inside : p ∈ cell0_faceDomain face.1) : ℝ :=
  sourceGradient (cell0_trueFaceMap face p) ⬝ᵥ cell0_trueOrientedArea face p inside

theorem cell0_trueSideTangent_is_gradient (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) (side : face.1 ≠ 2) :
    cell0_trueFaceTangent face p inside 1 = sourceGradient (cell0_trueFaceMap face p) := by
  have timeAxis : face.1.succAbove (1 : Fin 2) = 2 := by
    rcases face with ⟨axis, upper⟩
    fin_cases axis
    · rfl
    · rfl
    · exact False.elim (side rfl)
  rw [cell0_trueFaceTangent_eq_column, timeAxis]
  exact cell0_trueJacobian_time_column (cell0_trueFaceParameter face p inside)

/-- Both alpha sides and both v sides have zero pointwise flux for the original gradient. -/
theorem cell0_trueSideFlux_zero (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) (side : face.1 ≠ 2) :
    cell0_trueFaceFlux face p inside = 0 := by
  rw [cell0_trueFaceFlux, cell0_trueOrientedArea, ← cell0_trueSideTangent_is_gradient face p inside side,
    dotProduct_smul, dot_cross_self, smul_zero]

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

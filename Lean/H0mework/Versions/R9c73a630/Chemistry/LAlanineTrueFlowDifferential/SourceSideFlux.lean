import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceTimeColumn
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBoundary.GeometryTangents
import H0mework.Chemistry.LAlanineBoundary.GeometryAreaAlgebra

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowDifferential

open SourceGaussianModel ContinuousGradient TrueTubeWholeActual WholeCellBoundary
open WholeCellBoundary.Geometry WholeCellBoundaryArea Matrix Set
open scoped Matrix
noncomputable section

def trueFaceParameter (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) : BandPoint :=
  ⟨faceParameter face p, faceParameter_mem face p inside⟩

def trueFaceMap (face : Face) : FacePoint → Point := trueParameterMap ∘ faceParameter face

def trueFaceDerivative (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    FacePoint →L[ℝ] Point :=
  (trueJacobian (trueFaceParameter face p inside)).comp (faceInclusion face.1)

theorem trueFaceMap_hasFDerivWithinAt (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) :
    HasFDerivWithinAt (trueFaceMap face) (trueFaceDerivative face p inside)
      (faceDomain face.1) p :=
  (actualMap_hasFDerivWithinAt (trueFaceParameter face p inside)).comp p
    (faceParameter_hasFDerivAt face p).hasFDerivWithinAt (faceParameter_mem face)

def trueFaceTangent (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1)
    (k : Fin 2) : Point := trueFaceDerivative face p inside (Pi.single k 1)

theorem trueFaceTangent_eq_column (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (k : Fin 2) :
    trueFaceTangent face p inside k =
      trueJacobian (trueFaceParameter face p inside) (Pi.single (face.1.succAbove k) 1) := by
  simp only [trueFaceTangent, trueFaceDerivative, ContinuousLinearMap.comp_apply,
    faceInclusion_single]

/-- Actual face tangents generate the oriented area, with the original missing-axis parity. -/
def trueOrientedArea (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) : Point :=
  ((if face.2 then 1 else -1 : ℝ) * axisOrientation face.1) •
    (trueFaceTangent face p inside 0 ⨯₃ trueFaceTangent face p inside 1)

def trueFaceFlux (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) : ℝ :=
  sourceGradient (trueFaceMap face p) ⬝ᵥ trueOrientedArea face p inside

theorem trueSideTangent_is_gradient (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (side : face.1 ≠ 2) :
    trueFaceTangent face p inside 1 = sourceGradient (trueFaceMap face p) := by
  have timeAxis : face.1.succAbove (1 : Fin 2) = 2 := by
    rcases face with ⟨axis, upper⟩
    fin_cases axis
    · rfl
    · rfl
    · exact False.elim (side rfl)
  rw [trueFaceTangent_eq_column, timeAxis]
  exact trueJacobian_time_column (trueFaceParameter face p inside)

/-- Both alpha sides and both v sides have zero pointwise flux for the original gradient. -/
theorem trueSideFlux_zero (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (side : face.1 ≠ 2) :
    trueFaceFlux face p inside = 0 := by
  rw [trueFaceFlux, trueOrientedArea, ← trueSideTangent_is_gradient face p inside side,
    dotProduct_smul, dot_cross_self, smul_zero]

end
end LAlanine40K2025.BasinRefinement.TrueFlowDifferential
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowDifferential.SourceSideFlux
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowGeometry.ResponseNondegenerate
import Mathlib.LinearAlgebra.StdBasis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundary

open SourceGaussianModel TrueFlowDifferential TrueFlowGeometry WholeCellBoundary
open WholeCellBoundary.Geometry WholeCellBoundaryArea Matrix Set
open scoped Matrix
noncomputable section

private theorem faceInclusion_injective (axis : Fin 3) : Function.Injective (faceInclusion axis) := by
  intro u v same
  have inserted : (axis.insertNth (0 : ℝ) u : Point) = axis.insertNth (0 : ℝ) v := by
    rw [insertNth_eq_affine, insertNth_eq_affine, same]
  exact (Fin.insertNth_inj.mp inserted).2

theorem trueFaceDerivative_injective (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) : Function.Injective (trueFaceDerivative face p inside) :=
  (trueJacobian_injective (trueFaceParameter face p inside)).comp (faceInclusion_injective face.1)

theorem trueFaceTangents_linearIndependent (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) : LinearIndependent ℝ (trueFaceTangent face p inside) := by
  change LinearIndependent ℝ (fun k => trueFaceDerivative face p inside (Pi.single k 1))
  have mapped := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map_injOn
    (trueFaceDerivative face p inside).toLinearMap
    (trueFaceDerivative_injective face p inside).injOn
  simpa only [Function.comp_def, Pi.basisFun_apply, ContinuousLinearMap.coe_coe] using mapped

theorem trueFaceTangents_cross_ne_zero (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) :
    trueFaceTangent face p inside 0 ⨯₃ trueFaceTangent face p inside 1 ≠ 0 := by
  apply crossProduct_ne_zero_iff_linearIndependent.mpr
  have pair : ![trueFaceTangent face p inside 0, trueFaceTangent face p inside 1] =
      trueFaceTangent face p inside := by
    funext k
    fin_cases k <;> rfl
  rw [pair]
  exact trueFaceTangents_linearIndependent face p inside

/-- Every actual face has a nonzero oriented area, including both time caps. -/
theorem trueOrientedArea_ne_zero (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) : trueOrientedArea face p inside ≠ 0 := by
  apply smul_ne_zero _ (trueFaceTangents_cross_ne_zero face p inside)
  apply mul_ne_zero _ (axisOrientation_nonzero face.1)
  cases face.2 <;> norm_num

theorem trueSideFlux_zero_with_area (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (side : face.1 ≠ 2) :
    trueFaceFlux face p inside = 0 ∧ trueOrientedArea face p inside ≠ 0 :=
  ⟨trueSideFlux_zero face p inside side, trueOrientedArea_ne_zero face p inside⟩

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

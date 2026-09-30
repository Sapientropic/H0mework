import H0mework.Chemistry.LAlanineWholeBandCell0.BoundaryTangents
import Mathlib.LinearAlgebra.StdBasis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary

open SourceGaussianModel WholeBandCell0Geometry WholeBandCell0Differential WholeCellBoundary
open WholeCellBoundary.Geometry WholeCellBoundaryArea Matrix Set
open scoped Matrix
noncomputable section

private theorem faceInclusion_injective (axis : Fin 3) : Function.Injective (faceInclusion axis) := by
  intro u v same
  have inserted : (axis.insertNth (0 : ℝ) u : Point) = axis.insertNth (0 : ℝ) v := by
    rw [insertNth_eq_affine, insertNth_eq_affine, same]
  exact (Fin.insertNth_inj.mp inserted).2

theorem cell0_trueFaceDerivative_injective (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) : Function.Injective (cell0_trueFaceDerivative face p inside) :=
  (cell0_trueJacobian_injective (cell0_trueFaceParameter face p inside)).comp (faceInclusion_injective face.1)

theorem cell0_trueFaceDerivative_rank_two (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) :
    Module.finrank ℝ (LinearMap.range (cell0_trueFaceDerivative face p inside).toLinearMap) = 2 := by
  rw [LinearMap.finrank_range_of_inj (cell0_trueFaceDerivative_injective face p inside)]
  simp [FacePoint]

theorem cell0_trueFaceTangents_linearIndependent (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) : LinearIndependent ℝ (cell0_trueFaceTangent face p inside) := by
  change LinearIndependent ℝ (fun k => cell0_trueFaceDerivative face p inside (Pi.single k 1))
  have mapped := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map_injOn
    (cell0_trueFaceDerivative face p inside).toLinearMap
    (cell0_trueFaceDerivative_injective face p inside).injOn
  simpa only [Function.comp_def, Pi.basisFun_apply, ContinuousLinearMap.coe_coe] using mapped

theorem cell0_trueFaceTangents_cross_ne_zero (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) :
    cell0_trueFaceTangent face p inside 0 ⨯₃ cell0_trueFaceTangent face p inside 1 ≠ 0 := by
  apply crossProduct_ne_zero_iff_linearIndependent.mpr
  have pair : ![cell0_trueFaceTangent face p inside 0, cell0_trueFaceTangent face p inside 1] =
      cell0_trueFaceTangent face p inside := by
    funext k
    fin_cases k <;> rfl
  rw [pair]
  exact cell0_trueFaceTangents_linearIndependent face p inside

/-- Every actual face has a nonzero oriented area, including both time caps. -/
theorem cell0_trueOrientedArea_ne_zero (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) : cell0_trueOrientedArea face p inside ≠ 0 := by
  apply smul_ne_zero _ (cell0_trueFaceTangents_cross_ne_zero face p inside)
  apply mul_ne_zero _ (axisOrientation_nonzero face.1)
  cases face.2 <;> norm_num

theorem cell0_trueSideFlux_zero_with_area (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) (side : face.1 ≠ 2) :
    cell0_trueFaceFlux face p inside = 0 ∧ cell0_trueOrientedArea face p inside ≠ 0 :=
  ⟨cell0_trueSideFlux_zero face p inside side, cell0_trueOrientedArea_ne_zero face p inside⟩

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

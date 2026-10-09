import H0mework.Versions.R9c73a630.Chemistry.LAlanineWholeBandAdjacent.ConservationBoundary
import Mathlib.LinearAlgebra.StdBasis

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.AdjacentConservation

open SourceGaussianModel WholeCellBoundary WholeCellBoundary.Geometry WholeCellBoundaryArea AdjacentFlow Matrix Set
open scoped Matrix
noncomputable section

private theorem jacobian_injective (p : Point) (inside : p ∈ jointDomain) : Function.Injective (jointJacobian p) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra failed
  exact jointJacobian_det_ne_zero p inside (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr failed)

private theorem faceInclusion_injective (axis : Fin 3) : Function.Injective (faceInclusion axis) := by
  intro u v same
  have inserted : (axis.insertNth (0 : ℝ) u : Point) = axis.insertNth (0 : ℝ) v := by
    rw [insertNth_eq_affine,insertNth_eq_affine,same]
  exact (Fin.insertNth_inj.mp inserted).2

theorem actualFaceDerivative_injective (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    Function.Injective (actualFaceDerivative face p) :=
  (jacobian_injective _ (faceParameter_mem face p inside)).comp (faceInclusion_injective face.1)

theorem actualFaceDerivative_rank_two (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    Module.finrank ℝ (LinearMap.range (actualFaceDerivative face p).toLinearMap) = 2 := by
  rw [LinearMap.finrank_range_of_inj (actualFaceDerivative_injective face p inside)]
  simp [FacePoint]

theorem actualFaceTangents_linearIndependent (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    LinearIndependent ℝ (actualFaceTangent face p) := by
  change LinearIndependent ℝ (fun k => actualFaceDerivative face p (Pi.single k 1))
  have mapped := (Pi.basisFun ℝ (Fin 2)).linearIndependent.map_injOn
    (actualFaceDerivative face p).toLinearMap (actualFaceDerivative_injective face p inside).injOn
  simpa only [Function.comp_def,Pi.basisFun_apply,ContinuousLinearMap.coe_coe] using mapped

theorem actualFaceTangents_cross_ne_zero (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    actualFaceTangent face p 0 ⨯₃ actualFaceTangent face p 1 ≠ 0 := by
  apply crossProduct_ne_zero_iff_linearIndependent.mpr
  have pair : ![actualFaceTangent face p 0,actualFaceTangent face p 1] = actualFaceTangent face p := by
    funext k
    fin_cases k <;> rfl
  rw [pair]
  exact actualFaceTangents_linearIndependent face p inside

theorem actualOrientedArea_ne_zero (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) :
    actualOrientedArea face p ≠ 0 := by
  apply smul_ne_zero _ (actualFaceTangents_cross_ne_zero face p inside)
  apply mul_ne_zero _ (axisOrientation_nonzero face.1)
  cases face.2 <;> norm_num

theorem actual_side_boundary_flux (face : Face) (p : FacePoint) (inside : p ∈ faceDomain face.1) (side : face.1 ≠ 2) :
    actualFaceMap face p ∈ frontier jointImage ∧ actualFaceFlux face p = 0 ∧ actualOrientedArea face p ≠ 0 :=
  ⟨actualFaceMap_mem_boundary face p inside,actualSideFlux_zero face p inside side,actualOrientedArea_ne_zero face p inside⟩

end
end LAlanine40K2025.BasinRefinement.AdjacentConservation
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

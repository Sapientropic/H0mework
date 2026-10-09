import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueFlowBoundary.SourceRegularFaces

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueFlowBoundary

open SourceGaussianModel ContinuousGradient TrueFlowDifferential TrueFlowGeometry WholeCellBoundary
open WholeCellBoundaryArea Matrix Set
open scoped Matrix
noncomputable section

/-- The same actual tangent area is the cofactor row of its actual Jacobian. -/
theorem trueOrientedArea_eq_adjugate (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) :
    trueOrientedArea face p inside = (if face.2 then 1 else -1 : ℝ) •
      (LinearMap.toMatrix' (trueJacobian (trueFaceParameter face p inside)).toLinearMap).adjugate face.1 := by
  let m := LinearMap.toMatrix' (trueJacobian (trueFaceParameter face p inside)).toLinearMap
  have first : m.col (face.1.succAbove 0) = trueFaceTangent face p inside 0 := by
    rw [trueFaceTangent_eq_column]
    rfl
  have second : m.col (face.1.succAbove 1) = trueFaceTangent face p inside 1 := by
    rw [trueFaceTangent_eq_column]
    rfl
  change trueOrientedArea face p inside = (if face.2 then 1 else -1 : ℝ) • m.adjugate face.1
  rw [adjugate_row_cross, first, second, smul_smul]
  rfl

/-- Each time cap reads its own oriented actual determinant. -/
theorem trueCapFlux_eq_oriented_det (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (cap : face.1 = 2) :
    trueFaceFlux face p inside = (if face.2 then 1 else -1 : ℝ) *
      LinearMap.det (trueJacobian (trueFaceParameter face p inside)).toLinearMap := by
  let m := LinearMap.toMatrix' (trueJacobian (trueFaceParameter face p inside)).toLinearMap
  have gradient : sourceGradient (trueFaceMap face p) = m.col face.1 := by
    rw [cap]
    exact (trueJacobian_time_column (trueFaceParameter face p inside)).symm
  calc
    trueFaceFlux face p inside = (if face.2 then 1 else -1 : ℝ) * m.det := by
      rw [trueFaceFlux, trueOrientedArea_eq_adjugate, gradient]
      change m.col face.1 ⬝ᵥ ((if face.2 then 1 else -1 : ℝ) • m.adjugate face.1) = _
      rw [dotProduct_smul, transverse_dot_adjugate]
      rfl
    _ = _ := congrArg (fun r : ℝ => (if face.2 then 1 else -1 : ℝ) * r)
      (LinearMap.det_toMatrix' (trueJacobian (trueFaceParameter face p inside)).toLinearMap)

theorem trueCapFlux_ne_zero (face : Face) (p : FacePoint)
    (inside : p ∈ faceDomain face.1) (cap : face.1 = 2) : trueFaceFlux face p inside ≠ 0 := by
  rw [trueCapFlux_eq_oriented_det face p inside cap]
  apply mul_ne_zero _ (trueJacobian_det_ne_zero (trueFaceParameter face p inside))
  cases face.2 <;> norm_num

end
end LAlanine40K2025.BasinRefinement.TrueFlowBoundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

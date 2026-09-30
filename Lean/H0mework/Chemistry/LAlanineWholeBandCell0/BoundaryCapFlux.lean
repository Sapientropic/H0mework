import H0mework.Chemistry.LAlanineWholeBandCell0.BoundaryRegularFaces

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary

open SourceGaussianModel ContinuousGradient WholeBandCell0Geometry WholeBandCell0Differential WholeCellBoundary
open WholeCellBoundaryArea Matrix Set
open scoped Matrix
noncomputable section

/-- The same actual tangent area is the cofactor row of its actual Jacobian. -/
theorem cell0_trueOrientedArea_eq_adjugate (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) :
    cell0_trueOrientedArea face p inside = (if face.2 then 1 else -1 : ℝ) •
      (LinearMap.toMatrix' (cell0_trueJacobian (cell0_trueFaceParameter face p inside)).toLinearMap).adjugate face.1 := by
  let m := LinearMap.toMatrix' (cell0_trueJacobian (cell0_trueFaceParameter face p inside)).toLinearMap
  have first : m.col (face.1.succAbove 0) = cell0_trueFaceTangent face p inside 0 := by
    rw [cell0_trueFaceTangent_eq_column]
    rfl
  have second : m.col (face.1.succAbove 1) = cell0_trueFaceTangent face p inside 1 := by
    rw [cell0_trueFaceTangent_eq_column]
    rfl
  change cell0_trueOrientedArea face p inside = (if face.2 then 1 else -1 : ℝ) • m.adjugate face.1
  rw [adjugate_row_cross, first, second, smul_smul]
  rfl

/-- Each time cap reads its own oriented actual determinant. -/
theorem cell0_trueCapFlux_eq_oriented_det (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) (cap : face.1 = 2) :
    cell0_trueFaceFlux face p inside = (if face.2 then 1 else -1 : ℝ) *
      LinearMap.det (cell0_trueJacobian (cell0_trueFaceParameter face p inside)).toLinearMap := by
  let m := LinearMap.toMatrix' (cell0_trueJacobian (cell0_trueFaceParameter face p inside)).toLinearMap
  have gradient : sourceGradient (cell0_trueFaceMap face p) = m.col face.1 := by
    rw [cap]
    exact (cell0_trueJacobian_time_column (cell0_trueFaceParameter face p inside)).symm
  calc
    cell0_trueFaceFlux face p inside = (if face.2 then 1 else -1 : ℝ) * m.det := by
      rw [cell0_trueFaceFlux, cell0_trueOrientedArea_eq_adjugate, gradient]
      change m.col face.1 ⬝ᵥ ((if face.2 then 1 else -1 : ℝ) • m.adjugate face.1) = _
      rw [dotProduct_smul, transverse_dot_adjugate]
      rfl
    _ = _ := congrArg (fun r : ℝ => (if face.2 then 1 else -1 : ℝ) * r)
      (LinearMap.det_toMatrix' (cell0_trueJacobian (cell0_trueFaceParameter face p inside)).toLinearMap)

theorem cell0_trueCapFlux_ne_zero (face : Face) (p : FacePoint)
    (inside : p ∈ cell0_faceDomain face.1) (cap : face.1 = 2) : cell0_trueFaceFlux face p inside ≠ 0 := by
  rw [cell0_trueCapFlux_eq_oriented_det face p inside cap]
  apply mul_ne_zero _ (cell0_trueJacobian_det_ne_zero (cell0_trueFaceParameter face p inside))
  cases face.2 <;> norm_num

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Boundary
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule

import H0mework.Physics.LowEnergyEvolution.Cartan
import H0mework.Physics.Homogeneous.CoframeDifferential
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-! The original scalar density differentiated in every frozen coframe direction. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum StageNineCoframeVariation
open StageNineScalarLocalSpinDensity StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation Stage9C.Dynamics.Homogeneous Response.Radial
open Set Filter
open scoped Topology Matrix.Norms.Elementwise
noncomputable section

private theorem scalar_radial_pair (velocity : ℝ) (mu nu : LorentzianIndex) :
    scalarCoordinatePairingRe (if mu = 0 then velocity • direction else 0)
      (if nu = 0 then velocity • direction else 0) =
      if mu = 0 ∧ nu = 0 then velocity^2 * Contact.Stress.weight else 0 := by
  by_cases hm : mu = 0 <;> by_cases hn : nu = 0
  · simp only [hm, hn, if_true, and_self]
    rw [scalarCoordinatePairingRe_real_smul_left, scalarCoordinatePairingRe_real_smul_right]
    have self : scalarCoordinatePairingRe direction direction = Contact.Stress.weight :=
      scalarCoordinateRealPairing_self direction
    rw [self]
    ring
  all_goals simp [hm, hn, scalarCoordinatePairingRe]

private theorem scalar_radial_norm (amplitude : ℝ) :
    scalarCoordinateSquaredNorm (amplitude • direction) = amplitude^2 * Contact.Stress.weight := by
  rw [← scalarCoordinateRealPairing_self]
  change scalarCoordinatePairingRe (amplitude • direction) (amplitude • direction) = _
  rw [scalarCoordinatePairingRe_real_smul_left, scalarCoordinatePairingRe_real_smul_right]
  have self : scalarCoordinatePairingRe direction direction = Contact.Stress.weight :=
    scalarCoordinateRealPairing_self direction
  rw [self]
  ring

theorem Solution.scalar_frozen_density {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Ioo (-flow.radius) flow.radius)
    (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField flow.configuration point) candidate) =
      |candidate.det| * Contact.Stress.weight *
        ((1/2 : ℝ) * (lorentzianMetricOfCoframe candidate)⁻¹ 0 0 *
          (clock (flow.pointState point) * flow.pointState point 5)^2 - (flow.pointState point 4)^2) := by
  have derivative : holonomicScalarCovariantDerivative flow.configuration point =
      fun mu => if mu = 0 then (clock (flow.pointState point)*flow.pointState point 5) • direction else 0 := by
    funext mu
    rw [flow.scalar_covariant point inside]
    split_ifs <;> simp
  unfold generatedDensitizedContinuumScalarDensity generatedScalarKineticDensity generatedScalarPotential
  simp only [generatedVolumeDensity, withCoframe, toContinuumPointField,
    scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart, derivative]
  change _ * ((1/2:ℝ) * ∑ mu, ∑ nu,
    (lorentzianMetricOfCoframe candidate)⁻¹ mu nu *
      scalarCoordinatePairingRe
        (if mu = 0 then (clock (flow.pointState point)*flow.pointState point 5) • direction else 0)
        (if nu = 0 then (clock (flow.pointState point)*flow.pointState point 5) • direction else 0) -
      scalarCoordinateSquaredNorm (direction + flow.pointState point 4 • direction - direction)) = _
  rw [add_sub_cancel_left, scalar_radial_norm]
  simp only [scalar_radial_pair]
  simp [ite_and, mul_ite]
  ring

private theorem det_one_derivative (variation : LorentzianCoframe) :
    HasDerivAt (fun t : ℝ => Matrix.det (1+t • variation)) variation.trace 0 := by
  let remainder : Polynomial ℝ :=
    (Matrix.det (1+(Polynomial.X : Polynomial ℝ) • variation.map Polynomial.C)).divX.divX
  have remainderTerm : HasDerivAt (fun t : ℝ => remainder.eval t*t^2) 0 0 := by
    convert! (remainder.hasDerivAt 0).mul ((hasDerivAt_id (x := (0 : ℝ))).pow 2) using 1
    all_goals norm_num
  have polynomial : HasDerivAt (fun t : ℝ => 1+variation.trace*t+remainder.eval t*t^2)
      variation.trace 0 := by
    convert! (((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add
      ((hasDerivAt_id (x := (0 : ℝ))).const_mul variation.trace)).add remainderTerm) using 1
    all_goals norm_num
  apply polynomial.congr_of_eventuallyEq
  filter_upwards [] with t
  exact Matrix.det_one_add_smul t variation

theorem diagonal_volume_derivative (n a : ℝ) (hn : 0 < n) (ha : 0 < a)
    (variation : LorentzianCoframe) :
    HasDerivAt (fun t : ℝ => |Matrix.det (diagonalCoframe n a+t • variation)|)
      (a^3*variation 0 0+n*a^2*(variation 1 1+variation 2 2+variation 3 3)) 0 := by
  have nondegenerate : (diagonalCoframe n a).det ≠ 0 := by
    rw [diagonalCoframe_det]
    exact mul_ne_zero (ne_of_gt hn) (pow_ne_zero _ (ne_of_gt ha))
  have factor (t : ℝ) : diagonalCoframe n a+t • variation =
      diagonalCoframe n a * (1+t • ((diagonalCoframe n a)⁻¹*variation)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr nondegenerate), Matrix.one_mul]
  have determinant : HasDerivAt (fun t : ℝ => Matrix.det (diagonalCoframe n a+t • variation))
      ((diagonalCoframe n a).det * ((diagonalCoframe n a)⁻¹*variation).trace) 0 := by
    simp_rw [factor, Matrix.det_mul]
    exact (det_one_derivative ((diagonalCoframe n a)⁻¹*variation)).const_mul _
  have positive : 0 < Matrix.det (diagonalCoframe n a+(0:ℝ) • variation) := by
    simpa only [zero_smul, add_zero, diagonalCoframe_det] using mul_pos hn (pow_pos ha 3)
  have volume := (HasFDerivAt.abs_of_pos determinant positive).hasDerivAt
  convert! volume using 1
  rw [diagonalCoframe_det, diagonalCoframe_inv n a (ne_of_gt hn) (ne_of_gt ha)]
  simp [Matrix.trace, Matrix.mul_apply, diagonalCoframe, Fin.sum_univ_four]
  field_simp [ne_of_gt hn, ne_of_gt ha]
  ring

private theorem inverseMetric_time (coframe : LorentzianCoframe) :
    (lorentzianMetricOfCoframe coframe)⁻¹ 0 0 =
      -(coframe⁻¹ 0 0)^2+(coframe⁻¹ 0 1)^2+(coframe⁻¹ 0 2)^2+(coframe⁻¹ 0 3)^2 := by
  have minkowskiInverse : minkowskiInternalMetric⁻¹ = minkowskiInternalMetric := by
    apply Matrix.inv_eq_left_inv
    rw [minkowskiInternalMetric, Matrix.diagonal_mul_diagonal]
    ext row col
    fin_cases row <;> fin_cases col <;> norm_num
  rw [lorentzianMetricOfCoframe, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
    ← Matrix.transpose_nonsing_inv, minkowskiInverse]
  simp [Matrix.mul_apply, Fin.sum_univ_four, minkowskiInternalMetric]
  ring

theorem diagonal_inverseMetric_derivative (n a : ℝ) (hn : n ≠ 0) (ha : a ≠ 0)
    (variation : LorentzianCoframe) :
    HasDerivAt (fun t : ℝ => (lorentzianMetricOfCoframe (diagonalCoframe n a+t • variation))⁻¹ 0 0)
      (2*variation 0 0/n^3) 0 := by
  have nondegenerate : (diagonalCoframe n a).det ≠ 0 := by
    rw [diagonalCoframe_det]
    exact mul_ne_zero hn (pow_ne_zero _ ha)
  have inverse := coframeInverse_line_hasDerivAt (diagonalCoframe n a) variation nondegenerate
  have entry (col : LorentzianIndex) := hasDerivAt_pi.mp (hasDerivAt_pi.mp inverse 0) col
  have computed := (((((entry 0).pow 2).neg).add ((entry 1).pow 2)).add ((entry 2).pow 2)).add ((entry 3).pow 2)
  simp_rw [inverseMetric_time]
  convert! computed using 1
  simp only [zero_smul, add_zero, diagonalCoframe_inv n a hn ha]
  simp [diagonalCoframe, Matrix.mul_apply, Fin.sum_univ_four]
  field_simp [hn]

theorem diagonal_scalar_density_derivative (n a f w q : ℝ) (hn : 0 < n) (ha : 0 < a)
    (variation : LorentzianCoframe) :
    HasDerivAt (fun t : ℝ => |(diagonalCoframe n a+t • variation).det| * q *
      ((1/2:ℝ) * (lorentzianMetricOfCoframe (diagonalCoframe n a+t • variation))⁻¹ 0 0 *
        (n*w)^2-f^2))
      (q*a^3*(w^2/2-f^2)*variation 0 0 -
        n*q*a^2*(f^2+w^2/2)*(variation 1 1+variation 2 2+variation 3 3)) 0 := by
  have volume := (diagonal_volume_derivative n a hn ha variation).mul_const q
  have kinetic := (((diagonal_inverseMetric_derivative n a (ne_of_gt hn) (ne_of_gt ha)
    variation).const_mul (1/2:ℝ)).mul_const ((n*w)^2)).sub_const (f^2)
  have computed := volume.mul kinetic
  convert! computed using 1
  simp only [zero_smul, add_zero, diagonalCoframe_det,
    diagonalCoframe_metric_inverse n a (ne_of_gt hn) (ne_of_gt ha),
    Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
    abs_of_pos (mul_pos hn (pow_pos ha 3))]
  field_simp [ne_of_gt hn]
  ring

def scalarCoframeForce (x : State) (variation : LorentzianCoframe) : ℝ :=
  Contact.Stress.weight * (x 0)^3 * ((x 5)^2/2-(x 4)^2)*variation 0 0 -
    clock x * Contact.Stress.weight * (x 0)^2 * ((x 4)^2+(x 5)^2/2) *
      (variation 1 1+variation 2 2+variation 3 3)

theorem Solution.scalar_density_coframe_derivative {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Ioo (-flow.radius) flow.radius)
    (variation : LorentzianCoframe) :
    HasDerivAt (fun t : ℝ => generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 point
      (withCoframe (toContinuumPointField flow.configuration point)
        (flow.configuration.coframe point+t • variation)))
      (scalarCoframeForce (flow.pointState point) variation) 0 := by
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  simp_rw [flow.scalar_frozen_density point inside, flow.coframe]
  exact diagonal_scalar_density_derivative _ _ _ _ _ (clock_positive _ admissible) admissible.1 variation

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution

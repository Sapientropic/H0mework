import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceHamiltonianVolume
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! Coframe homogeneity of the original coefficients, before differential assembly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceKineticScale
open GaussNativeEnergy GaussNativePotential GaussHistoryHilbert SourceCoframeVolume
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open scoped ContDiff Matrix

private theorem scale_curve (z : SourceCoordinateSlice) :
    HasDerivAt (fun r => scale r z) (euler z) 1 := by
  have h := ((hasDerivAt_id (1 : ℝ)).smul_const z.1).prodMk (hasDerivAt_const 1 z.2)
  simpa only [scale, euler, id_eq, one_smul] using! h

private theorem scale_one (z : SourceCoordinateSlice) : scale 1 z=z := by simp [scale]

theorem euler_of_scale (a : SourceCoordinateSlice → ℝ) (k : ℤ) (z : physicalChart)
    (smooth : ContDiffAt ℝ ∞ a z.val)
    (homogeneous : ∀ r : ℝ, r≠0 → a (scale r z.val)=r^k*a z.val) :
    fderiv ℝ a z.val (euler z.val)=(k : ℝ)*a z.val := by
  have chain := (smooth.differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scale_curve z.val) (scale_one z.val).symm
  have power := (hasDerivAt_zpow k (1 : ℝ) (Or.inl (by norm_num))).mul_const (a z.val)
  have hp : HasDerivAt (fun r => a (scale r z.val)) ((k : ℝ)*a z.val) 1 := by
    apply (show HasDerivAt (fun r : ℝ => r^k*a z.val) _ 1 by
      simpa only [one_zpow, mul_one] using power).congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds (show (1 : ℝ)≠0 by norm_num)] with r hr
    exact homogeneous r hr
  exact chain.unique hp

theorem inverse_coframe_scale (r : ℝ) (z : SourceCoordinateSlice) :
    GaussLiveMomentum.inverseL (scale r z)=GaussLiveMomentum.inverseL z := rfl

theorem inverse_coframe_euler (z : physicalChart) :
    fderiv ℝ GaussLiveMomentum.inverseL z.val (euler z.val)=0 := by
  have chain := ((GaussLiveMomentum.inverse_smooth z).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt_of_eq 1 (scale_curve z.val) (scale_one z.val).symm
  have hc : HasDerivAt (fun r => GaussLiveMomentum.inverseL (scale r z.val)) 0 1 := by
    simpa only [inverse_coframe_scale] using hasDerivAt_const (1 : ℝ) (GaussLiveMomentum.inverseL z.val)
  exact chain.unique hc

theorem triad_inverse_scale (r : ℝ) (z : SourceCoordinateSlice) (i j : Fin 3) :
    triadInverse (scale r z).1 i j = r⁻¹ * triadInverse z.1 i j := by
  fin_cases i <;> fin_cases j <;>
    simp [triadInverse, scale, mul_inv_rev, field]

theorem inverse_spatial_scale (r : ℝ) (z : SourceCoordinateSlice) (i j : Fin 3) :
    inverseSpatial (scale r z) i j = r⁻¹^2 * inverseSpatial z i j := by
  unfold inverseSpatial
  simp only [Matrix.mul_apply, Matrix.transpose_apply, triad_inverse_scale r]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem scalar_weight_scale (r : ℝ) (z : SourceCoordinateSlice) :
    scalarWeight (scale r z) = r⁻¹^3 * scalarWeight z := by
  rw [scalarWeight, volume_scale, scalarWeight]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem gauge_weight_scale (r : ℝ) (hr : r≠0) (z : SourceCoordinateSlice) (i j : Fin 3) :
    gaugeWeight (scale r z) i j = r * gaugeWeight z i j := by
  unfold gaugeWeight
  rw [volume_scale, inverse_spatial_scale r]
  field_simp [hr]

theorem polynomial_scale (r : ℝ) (z : SourceCoordinateSlice) (i j : Fin 6) :
    GaussCoframeKinetic.polynomial (scale r z).1 i j =
      r^2*GaussCoframeKinetic.polynomial z.1 i j := by
  fin_cases i <;> fin_cases j <;>
    simp [GaussCoframeKinetic.polynomial, scale] <;> ring

theorem coframe_coefficient_scale (r : ℝ) (hr : r≠0) (z : SourceCoordinateSlice) (i j : Fin 6) :
    GaussCoframeKinetic.coefficient i j (scale r z) =
      r⁻¹*GaussCoframeKinetic.coefficient i j z := by
  unfold GaussCoframeKinetic.coefficient
  rw [volume_scale, polynomial_scale]
  field_simp [hr]

theorem inverse_volume_scale (r : ℝ) (z : SourceCoordinateSlice) :
    GaussCoframeForm.inverseVolume (scale r z) = r⁻¹^3*GaussCoframeForm.inverseVolume z := by
  unfold GaussCoframeForm.inverseVolume
  rw [volume_scale]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  ring

theorem current_coefficient_scale (r : ℝ) (hr : r≠0) (z : SourceCoordinateSlice) (i : Fin 6) :
    GaussCoframeForm.currentCoefficient i (scale r z) =
      r⁻¹^2*GaussCoframeForm.currentCoefficient i z := by
  unfold GaussCoframeForm.currentCoefficient
  rw [inverse_volume_scale]
  change r⁻¹^3*GaussCoframeForm.inverseVolume z*(r*z.1 i)=_
  field_simp [hr]

theorem scalar_weight_euler (z : physicalChart) :
    fderiv ℝ scalarWeight z.val (euler z.val)= -3*scalarWeight z.val := by
  have h := euler_of_scale scalarWeight (-3) z (scalarWeight_smooth z) (fun r _ => by
    simpa only [zpow_neg, zpow_natCast, inv_pow] using! scalar_weight_scale r z.val)
  simpa using h

theorem gauge_weight_euler (z : physicalChart) (i j : Fin 3) :
    fderiv ℝ (fun w => gaugeWeight w i j) z.val (euler z.val)=gaugeWeight z.val i j := by
  have h := euler_of_scale (fun w => gaugeWeight w i j) 1 z (gaugeWeight_smooth i j z)
    (fun r hr => by simpa only [zpow_one] using gauge_weight_scale r hr z.val i j)
  simpa using h

theorem coframe_coefficient_euler (z : physicalChart) (i j : Fin 6) :
    fderiv ℝ (GaussCoframeKinetic.coefficient i j) z.val (euler z.val)=
      -GaussCoframeKinetic.coefficient i j z.val := by
  have h := euler_of_scale (GaussCoframeKinetic.coefficient i j) (-1) z
    (GaussCoframeKinetic.coefficient_smooth i j z) (fun r hr => by
      simpa only [zpow_neg_one] using coframe_coefficient_scale r hr z.val i j)
  simpa using h

theorem current_coefficient_euler (z : physicalChart) (i : Fin 6) :
    fderiv ℝ (GaussCoframeForm.currentCoefficient i) z.val (euler z.val)=
      -2*GaussCoframeForm.currentCoefficient i z.val := by
  have h := euler_of_scale (GaussCoframeForm.currentCoefficient i) (-2) z
    (GaussCoframeForm.currentCoefficient_smooth i z) (fun r hr => by
      simpa only [zpow_neg, zpow_natCast, inv_pow] using! current_coefficient_scale r hr z.val i)
  simpa using h

theorem inverse_volume_euler (z : physicalChart) :
    fderiv ℝ GaussCoframeForm.inverseVolume z.val (euler z.val)=
      -3*GaussCoframeForm.inverseVolume z.val := by
  have h := euler_of_scale GaussCoframeForm.inverseVolume (-3) z
    (GaussCoframeForm.inverseVolume_smooth z) (fun r _ => by
      simpa only [zpow_neg, zpow_natCast, inv_pow] using! inverse_volume_scale r z.val)
  simpa using h

end LowEnergy.SourceKineticScale

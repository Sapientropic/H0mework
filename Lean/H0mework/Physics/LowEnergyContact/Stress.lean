import H0mework.Physics.LowEnergyContact.Profile

/-! Exact coframe load at the original scalar-contact point. The field
is holonomic; the velocity slot is supplied by Profile.pointField_origin. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Contact.Stress
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineGlobalIntegratedAction StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource Stage9C.Material.SpinPair
open StageNineCoframeVariation Stage9C.Dynamics.Homogeneous
open StageNineScalarLocalSpinDensity StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation Response.Radial
noncomputable section

def weight : ℝ := scalarCoordinateSquaredNorm direction

theorem weight_positive : 0 < weight := by
  have nonnegative := scalarCoordinateSquaredNorm_nonneg direction
  have nonzero : scalarCoordinateSquaredNorm direction ≠ 0 := by
    intro zero
    exact direction_nonzero ((scalarCoordinateSquaredNorm_eq_zero_iff direction).mp zero)
  exact lt_of_le_of_ne nonnegative (Ne.symm nonzero)

private theorem pairing_self : scalarCoordinatePairingRe direction direction = weight :=
  scalarCoordinateRealPairing_self direction

def field (parameter : ℝ) : StageNineContinuumPointField :=
  toContinuumPointField (Profile.testField parameter) 0

private theorem impulse_pair (a : ℝ) (i j : LorentzianIndex) :
    scalarCoordinatePairingRe (if i = 0 then a • direction else 0)
      (if j = 0 then a • direction else 0) =
        if i = 0 ∧ j = 0 then a^2 * weight else 0 := by
  by_cases hi : i = 0 <;> by_cases hj : j = 0
  · simp only [hi, hj, if_true, and_self]
    rw [scalarCoordinatePairingRe_real_smul_left,
      scalarCoordinatePairingRe_real_smul_right, pairing_self]
    ring
  all_goals simp [hi, hj, scalarCoordinatePairingRe]

theorem scalar_density (parameter : ℝ) (candidate : LorentzianCoframe) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 0
      (withCoframe (field parameter) candidate) =
      abs candidate.det * ((1/2 : ℝ) *
        (lorentzianMetricOfCoframe candidate)⁻¹ 0 0 *
        (parameter * growthRate)^2 * weight) := by
  unfold field
  rw [Profile.pointField_origin]
  simp only [generatedDensitizedContinuumScalarDensity, generatedVolumeDensity,
    withCoframe, generatedScalarKineticDensity, scalarFrameRelativeCovariantDerivative,
    scalarFrameRelativeCoordinates_zeroChart, generatedScalarPotential,
    toContinuumPointField, actual_scalar]
  change _ * ((1/2 : ℝ) * ∑ first, ∑ second,
    (lorentzianMetricOfCoframe candidate)⁻¹ first second *
      scalarCoordinatePairingRe
        (if first = 0 then (parameter * growthRate) • direction else 0)
        (if second = 0 then (parameter * growthRate) • direction else 0) -
          scalarCoordinateSquaredNorm (direction - direction)) = _
  simp only [sub_self, scalarCoordinateSquaredNorm_zero, sub_zero, impulse_pair]
  simp [ite_and, mul_ite, mul_assoc]


/-- Only scalar kinetic changes in the complete repaired local density. -/
theorem root_difference (parameter : ℝ) (candidate : LorentzianCoframe) :
    diracDualFormNativeCoframeLocalDensity positiveSmoothUnifiedSource 0 (field parameter) candidate =
      diracDualFormNativeCoframeLocalDensity positiveSmoothUnifiedSource 0
        (toContinuumPointField actual 0) candidate +
      abs candidate.det * ((1/2 : ℝ) * (lorentzianMetricOfCoframe candidate)⁻¹ 0 0 *
        (parameter * growthRate)^2 * weight) := by
  have baseline : generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 0
      (withCoframe (toContinuumPointField actual 0) candidate) = 0 := by
    simp [generatedDensitizedContinuumScalarDensity, generatedScalarKineticDensity,
      generatedScalarPotential, toContinuumPointField, withCoframe,
      actual_scalarCovariantDerivative_zero, actual_scalar,
      scalarFrameRelativeCovariantDerivative, scalarCoordinatePairingRe]
  simp only [diracDualFormNativeCoframeLocalDensity,
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity,
    generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary,
    generatedDiracDualFormNativeMatterDensity]
  rw [scalar_density, baseline]
  simp only [field, Profile.pointField_origin]
  let original := withCoframe (toContinuumPointField actual 0) candidate
  conv_lhs =>
    change StageNineFormNativeMotherAction.generatedFormNativeGravityBFDensity original +
      StageNineFormNativeMotherAction.generatedFormNativeGravityConstraintDensity original +
      StageNineFormNativeMotherAction.generatedFormNativeGaugeDensityAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) original +
      (_ + generatedDensitizedContinuumDiracDualMatterDensity positiveSmoothUnifiedSource 0 0 original)
  ring

/-- The actual lapse slice, without interpreting it as a new background. -/
theorem lapse_slice (parameter n : ℝ) (positive : 0 < n) :
    abs (homogeneousCoframe n).det * ((1/2 : ℝ) *
      (lorentzianMetricOfCoframe (homogeneousCoframe n))⁻¹ 0 0 *
        (parameter * growthRate)^2 * weight) =
      -(parameter * growthRate)^2 * weight / (2*n) := by
  have metric : lorentzianMetricOfCoframe (homogeneousCoframe n) =
      Matrix.diagonal ![-n^2, 1, 1, 1] := by
    ext row col
    fin_cases row <;> fin_cases col <;>
      simp [lorentzianMetricOfCoframe, homogeneousCoframe, minkowskiInternalMetric,
        Matrix.mul_apply, Matrix.diagonal_apply, pow_two]
  have inverse : (Matrix.diagonal ![-n^2, (1:ℝ), 1, 1])⁻¹ =
      Matrix.diagonal ![-(n⁻¹)^2, 1, 1, 1] := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext row col
    fin_cases row <;> fin_cases col <;> simp [ne_of_gt positive]
  rw [homogeneousCoframe_det, abs_of_pos positive, metric, inverse]
  simp only [Matrix.diagonal_apply_eq, Matrix.cons_val_zero]
  field_simp [ne_of_gt positive]

end
end SaturationMonoid.PhysicsCore.LowEnergy.Contact.Stress

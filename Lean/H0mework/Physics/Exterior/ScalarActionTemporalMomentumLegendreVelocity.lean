import H0mework.Physics.ScalarJets.ScalarActionSecondJetLocalActualLift

/-!
# Scalar-action temporal Legendre velocity

At an identity-coframe occurrence, the scalar mother action identifies the
temporal differential momentum with the negative real Riesz pairing against
the actual covariant scalar velocity.  The finite real basis of the existing
complex scalar representation therefore gives a canonical, unique inverse:

```text
source + current + occurrence
-> scalar temporal differential momentum
-> unique covariant scalar velocity.
```

This is an action-side producer for the covariant velocity.  It consumes no
Euler residual, support coordinate, target state, branch, or supplied inverse
witness.  A downstream raw first-jet write must still subtract the connection
action of the actual on which that first jet is installed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineScalarActionTemporalMomentumLegendreVelocity

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineScalarActionSecondJetLocalActualLift
open StageNineScalarPointwiseEquation

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

private theorem scalarCoordinatePairingRe_comm_local
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second =
      scalarCoordinatePairingRe second first := by
  unfold scalarCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re, mul_comm]

private theorem scalarCoordinatePairingRe_zero_left_local
    (value : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe 0 value = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem scalarCoordinatePairingRe_zero_right_local
    (value : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe value 0 = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem scalarCoordinatePairingRe_realBasis_local
    (index : ScalarBasisIndex)
    (value : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe (scalarRealBasis index) value =
      (value index).re := by
  classical
  unfold scalarCoordinatePairingRe scalarRealBasis
  simp only [RCLike.star_def, PiLp.single_apply]
  rw [Finset.sum_eq_single index]
  · simp
  · intro candidate _ candidateNe
    simp [candidateNe]
  · simp

private theorem scalarCoordinatePairingRe_imaginaryBasis_local
    (index : ScalarBasisIndex)
    (value : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe (scalarImaginaryBasis index) value =
      (value index).im := by
  classical
  unfold scalarCoordinatePairingRe scalarImaginaryBasis
  simp only [RCLike.star_def, PiLp.single_apply]
  rw [Finset.sum_eq_single index]
  · simp [Complex.mul_re]
  · intro candidate _ candidateNe
    simp [candidateNe]
  · simp

private theorem scalarVariationDifferentialDirection_add_local
    (first second : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarVariationDifferentialDirection (first + second)
        derivativeDirection =
      scalarVariationDifferentialDirection first derivativeDirection +
        scalarVariationDifferentialDirection second derivativeDirection := by
  funext formDirection
  by_cases same : formDirection = derivativeDirection <;>
    simp [scalarVariationDifferentialDirection, same]

private theorem scalarVariationDifferentialDirection_real_smul_local
    (parameter : ℝ)
    (direction : ScalarCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    scalarVariationDifferentialDirection (parameter • direction)
        derivativeDirection =
      parameter •
        scalarVariationDifferentialDirection direction derivativeDirection := by
  funext formDirection
  simp [scalarVariationDifferentialDirection]

private theorem lorentzianMetricOfCoframe_one_inv_local :
    (lorentzianMetricOfCoframe (1 : LorentzianCoframe))⁻¹ =
      minkowskiInternalMetric := by
  apply Matrix.inv_eq_left_inv
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [lorentzianMetricOfCoframe, minkowskiInternalMetric,
      Matrix.mul_apply, Fin.sum_univ_four]

/-- Scalar temporal canonical momentum read directly from the mother action
at one actual occurrence. -/
def scalarTemporalMomentumDualAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : Module.Dual ℝ ScalarCoordinateCarrier where
  toFun := fun direction =>
    scalarDifferentialMomentum source current direction
      canonicalLorentzianTimeDirection point
  map_add' := by
    intro first second
    unfold scalarDifferentialMomentum
    rw [scalarVariationDifferentialDirection_add_local,
      scalarKineticFirstVariationDensity_add]
    ring
  map_smul' := by
    intro parameter direction
    unfold scalarDifferentialMomentum
    rw [scalarVariationDifferentialDirection_real_smul_local,
      scalarKineticFirstVariationDensity_real_smul]
    simp only [RingHom.id_apply, smul_eq_mul]
    ring

/-- At an identity coframe the temporal Legendre read is the negative real
Riesz pairing with the current's actual covariant velocity. -/
theorem scalarTemporalMomentumDualAt_apply_identityCoframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEq : current.coframe point = 1)
    (direction : ScalarCoordinateCarrier) :
    scalarTemporalMomentumDualAt source current point direction =
      -scalarCoordinatePairingRe direction
        (holonomicScalarCovariantDerivative current point
          canonicalLorentzianTimeDirection) := by
  change
    scalarDifferentialMomentum source current direction
        canonicalLorentzianTimeDirection point = _
  unfold scalarDifferentialMomentum
    generatedVolumeDensity scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField]
  rw [coframeEq]
  simp only [Matrix.det_one, abs_one, one_mul,
    StageNineP286GaugeConnectionVariationDensity.scalarFrameRelativeCoordinates_zeroChart]
  rw [lorentzianMetricOfCoframe_one_inv_local]
  simp [scalarVariationDifferentialDirection, Fin.sum_univ_four,
    minkowskiInternalMetric, Matrix.diagonal_apply,
    canonicalLorentzianTimeDirection]
  rw [scalarCoordinatePairingRe_comm_local
    (holonomicScalarCovariantDerivative current point 0) direction]
  simp only [scalarCoordinatePairingRe_zero_left_local,
    scalarCoordinatePairingRe_zero_right_local]
  ring

/-- Canonical no-free-parameter covariant velocity selected by the temporal
scalar Legendre read. -/
def scalarTemporalCovariantVelocityOfMomentum
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : ScalarCoordinateCarrier :=
  -scalarActionRealDual (scalarTemporalMomentumDualAt source current point)

theorem scalarTemporalCovariantVelocityOfMomentum_eq
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEq : current.coframe point = 1) :
    scalarTemporalCovariantVelocityOfMomentum source current point =
      holonomicScalarCovariantDerivative current point
        canonicalLorentzianTimeDirection := by
  classical
  apply PiLp.ext
  intro index
  let velocity := holonomicScalarCovariantDerivative current point
    canonicalLorentzianTimeDirection
  have realRead := scalarTemporalMomentumDualAt_apply_identityCoframe
    source current point coframeEq (scalarRealBasis index)
  have imaginaryRead := scalarTemporalMomentumDualAt_apply_identityCoframe
    source current point coframeEq (scalarImaginaryBasis index)
  rw [scalarCoordinatePairingRe_realBasis_local] at realRead
  rw [scalarCoordinatePairingRe_imaginaryBasis_local] at imaginaryRead
  simp [scalarTemporalCovariantVelocityOfMomentum, scalarActionRealDual]
  rw [realRead, imaginaryRead]
  apply Complex.ext <;> simp

/-- The action momentum has exactly one compatible temporal covariant
velocity at an identity-coframe occurrence. -/
theorem scalarTemporalCovariantVelocityOfMomentum_unique
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeEq : current.coframe point = 1)
    (candidate : ScalarCoordinateCarrier)
    (candidateLaw :
      ∀ direction : ScalarCoordinateCarrier,
        scalarTemporalMomentumDualAt source current point direction =
          -scalarCoordinatePairingRe direction candidate) :
    candidate =
      scalarTemporalCovariantVelocityOfMomentum source current point := by
  classical
  rw [scalarTemporalCovariantVelocityOfMomentum_eq source current point
    coframeEq]
  apply PiLp.ext
  intro index
  have realCandidate := candidateLaw (scalarRealBasis index)
  have imaginaryCandidate := candidateLaw (scalarImaginaryBasis index)
  have realVelocity := scalarTemporalMomentumDualAt_apply_identityCoframe
    source current point coframeEq (scalarRealBasis index)
  have imaginaryVelocity :=
    scalarTemporalMomentumDualAt_apply_identityCoframe source current point
      coframeEq (scalarImaginaryBasis index)
  rw [scalarCoordinatePairingRe_realBasis_local] at realCandidate realVelocity
  rw [scalarCoordinatePairingRe_imaginaryBasis_local] at imaginaryCandidate imaginaryVelocity
  apply Complex.ext
  · linear_combination realCandidate - realVelocity
  · linear_combination imaginaryCandidate - imaginaryVelocity

end

end
  SaturationMonoid.PhysicsCore.StageNineScalarActionTemporalMomentumLegendreVelocity

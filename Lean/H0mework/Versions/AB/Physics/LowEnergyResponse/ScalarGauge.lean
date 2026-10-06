import H0mework.Versions.R2.Physics.SpinPair.Scalar
import H0mework.Physics.LowEnergy.Normalization

/-! Actual scalar/gauge affine jets and the complete quadratic, cubic and
quartic scalar density on the source coframe. Gauge perturbations are not
replaced by a constant mass matrix. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Response.ScalarGauge
open ProofFreeRicherAnholonomicSource SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineHolonomicField StageNineDynamicBreakingVacuum StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineScalarLocalSpinDensity
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation Stage9C.Material.SpinPair
noncomputable section

def path (eta : BasePoint → ScalarCoordinateCarrier) (a : P286ConnectionField)
    (parameter : ℝ) : StageNineHolonomicConfiguration :=
  { actual with
    scalar := fun point => actual.scalar point + parameter • eta point
    gaugeConnection := fun point direction =>
      actual.gaugeConnection point direction + parameter • a point direction }

/-- Background covariant derivative of the scalar fluctuation. -/
def backgroundDerivative (eta : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint) (direction : LorentzianIndex) : ScalarCoordinateCarrier :=
  fieldDirectionalDerivative eta point direction +
    scalarMotherLieAction (p286LieBlockEmbed (actual.gaugeConnection point direction)) (eta point)

def linearDerivative (eta : BasePoint → ScalarCoordinateCarrier) (a : P286ConnectionField)
    (point : BasePoint) (direction : LorentzianIndex) : ScalarCoordinateCarrier :=
  backgroundDerivative eta point direction +
    scalarMotherLieAction (p286LieBlockEmbed (a point direction)) (actual.scalar point)

def quadraticDerivative (eta : BasePoint → ScalarCoordinateCarrier) (a : P286ConnectionField)
    (point : BasePoint) (direction : LorentzianIndex) : ScalarCoordinateCarrier :=
  scalarMotherLieAction (p286LieBlockEmbed (a point direction)) (eta point)

theorem derivative_expansion (eta : BasePoint → ScalarCoordinateCarrier)
    (a : P286ConnectionField) (point : BasePoint) (regular : DifferentiableAt ℝ eta point)
    (parameter : ℝ) (direction : LorentzianIndex) :
    holonomicScalarCovariantDerivative (path eta a parameter) point direction =
      parameter • linearDerivative eta a point direction +
        parameter^2 • quadraticDerivative eta a point direction := by
  have raw : fieldDirectionalDerivative (path eta a parameter).scalar point direction =
      parameter • fieldDirectionalDerivative eta point direction := by
    unfold fieldDirectionalDerivative
    change fderiv ℝ (fun p => actual.scalar p + parameter • eta p) point _ = _
    rw [actual_scalar]
    change fderiv ℝ ((fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) +
      parameter • eta) point _ = _
    rw [((hasFDerivAt_const (𝕜 := ℝ)
      (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource) point).add
        (regular.hasFDerivAt.const_smul parameter)).fderiv]
    simp
  have zero : scalarMotherLieAction
      (p286LieBlockEmbed (actual.gaugeConnection point direction)) (actual.scalar point) = 0 := by
    have h := congrFun (actual_scalarCovariantDerivative_zero point) direction
    simpa [holonomicScalarCovariantDerivative, actual_scalar, fieldDirectionalDerivative] using h
  unfold holonomicScalarCovariantDerivative
  rw [raw]
  simp only [path, p286LieBlockEmbed_add, p286LieBlockEmbed_real_smul,
    scalarMotherLieAction_add, scalarMotherLieAction_real_smul,
    scalarMotherLieAction_add_right, scalarMotherLieAction_real_smul_right,
    zero, smul_add, linearDerivative, backgroundDerivative,
    quadraticDerivative]
  module

/-- The original scalar kinetic bilinear; its metric is the actual coframe. -/
def kineticPair (point : BasePoint)
    (u w : LorentzianIndex → ScalarCoordinateCarrier) : ℝ :=
  (1/2 : ℝ) * ∑ first, ∑ second,
    ((lorentzianMetricOfCoframe (actual.coframe point))⁻¹ first second) *
      scalarCoordinatePairingRe (u first) (w second)

theorem kinetic_polynomial (point : BasePoint)
    (u w : LorentzianIndex → ScalarCoordinateCarrier) (parameter : ℝ) :
    kineticPair point (parameter • u + parameter^2 • w)
      (parameter • u + parameter^2 • w) =
      parameter^2 * kineticPair point u u +
      parameter^3 * (kineticPair point u w + kineticPair point w u) +
      parameter^4 * kineticPair point w w := by
  simp only [kineticPair, Pi.add_apply, Pi.smul_apply, scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right, scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

theorem scalar_density_expansion (eta : BasePoint → ScalarCoordinateCarrier)
    (a : P286ConnectionField) (point : BasePoint) (regular : DifferentiableAt ℝ eta point)
    (parameter : ℝ) :
    generatedDensitizedContinuumScalarDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (path eta a parameter) point) =
      generatedVolumeDensity (toContinuumPointField actual point) *
        (parameter^2 *
          (kineticPair point (linearDerivative eta a point) (linearDerivative eta a point) -
            scalarCoordinateSquaredNorm (eta point)) +
         parameter^3 *
          (kineticPair point (linearDerivative eta a point) (quadraticDerivative eta a point) +
           kineticPair point (quadraticDerivative eta a point) (linearDerivative eta a point)) +
         parameter^4 *
          kineticPair point (quadraticDerivative eta a point) (quadraticDerivative eta a point)) := by
  have derivative : holonomicScalarCovariantDerivative (path eta a parameter) point =
      parameter • linearDerivative eta a point + parameter^2 • quadraticDerivative eta a point := by
    funext direction
    exact derivative_expansion eta a point regular parameter direction
  have potential : generatedScalarPotential positiveSmoothUnifiedSource 0 point
      ((path eta a parameter).scalar point) = parameter^2 * scalarCoordinateSquaredNorm (eta point) := by
    change frameRelativeScalarPotential (sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource)
      (scalarFrameRelativeCoordinates positiveSmoothUnifiedSource 0 point
        (actual.scalar point + parameter • eta point)) = _
    rw [scalarFrameRelativeCoordinates_zeroChart, actual_scalar]
    exact LowEnergy.Normalization.potential_quadratic _ _ parameter
  unfold generatedDensitizedContinuumScalarDensity
  change generatedVolumeDensity (toContinuumPointField actual point) *
    (generatedScalarKineticDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (path eta a parameter) point) -
     generatedScalarPotential positiveSmoothUnifiedSource 0 point ((path eta a parameter).scalar point)) = _
  rw [potential]
  have kinetic : generatedScalarKineticDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField (path eta a parameter) point) =
      kineticPair point (parameter • linearDerivative eta a point +
        parameter^2 • quadraticDerivative eta a point)
        (parameter • linearDerivative eta a point + parameter^2 • quadraticDerivative eta a point) := by
    unfold generatedScalarKineticDensity
    simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart]
    change kineticPair point (holonomicScalarCovariantDerivative (path eta a parameter) point)
      (holonomicScalarCovariantDerivative (path eta a parameter) point) = _
    rw [derivative]
  rw [kinetic, kinetic_polynomial]
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Response.ScalarGauge

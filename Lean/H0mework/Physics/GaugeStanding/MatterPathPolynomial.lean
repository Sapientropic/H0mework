import H0mework.Physics.GaugeStanding.MatterDensityCancellation

/-!
# S9-C: linked matter-density path polynomial

The matter vector is evaluated on the simultaneous path

* `H(t) = H + t h`,
* `psi(t) = psi + t eta`,
* `D psi(t) = D psi + t R + t² S`,
* `bar psi(t) = bar psi + t xi`.

The Dirac--Yukawa vector is exactly quadratic and its pairing with the affine
conjugate field is exactly cubic.  All coefficients are explicit readouts of
the same initial point field and tangent.  No difference quotient, target
coefficient, stationarity law, Ward receipt, or residual zero is accepted.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveMatterPathPolynomial

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveMatterDensityCancellation
open StageNineP286LinkedActiveVariation
open StageNineScalarVariation
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterFullVariations

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000

/-- Complex scalar multiplication commutes with the restricted real scalar
action on the matter carrier.  This is only a scalar-normalization lemma. -/
private theorem complex_smul_real_smul_comm
    (coefficient : ℂ) (parameter : ℝ)
    (matter : DiracExteriorMatterCarrier) :
    coefficient • (parameter • matter) =
      parameter • (coefficient • matter) := by
  change coefficient • ((parameter : ℂ) • matter) =
    (parameter : ℂ) • (coefficient • matter)
  module

/-- Normalize the restricted real action on the complex matter carrier. -/
private theorem matter_real_smul_eq_complex_smul
    (parameter : ℝ) (matter : DiracExteriorMatterCarrier) :
    parameter • matter = (parameter : ℂ) • matter :=
  rfl

/-- Evaluation of a complex-linear matter dual on a restricted real
multiple, exposed in the scalar ring used by the density polynomial. -/
private theorem dual_apply_real_smul
    (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) (matter : DiracExteriorMatterCarrier) :
    dual (parameter • matter) = (parameter : ℂ) * dual matter := by
  change dual ((parameter : ℂ) • matter) =
    (parameter : ℂ) * dual matter
  simpa only [smul_eq_mul] using dual.map_smul (parameter : ℂ) matter

/-- Normalize the restricted real action on a complex density value. -/
private theorem complex_real_smul_eq_mul
    (parameter : ℝ) (value : ℂ) :
    parameter • value = (parameter : ℂ) * value :=
  rfl

/-- The kinetic Dirac leg is exactly quadratic in a quadratic covariant-jet
path.  Splitting this linear identity keeps the final producer theorem from
normalizing the complete Dirac--Yukawa expression at once. -/
private theorem matterGaugeKineticVector_quadratic
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (base linear quadratic :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    Complex.I • matterGaugeKineticSum source 0 point field
        (base + parameter • linear + parameter ^ 2 • quadratic) =
      Complex.I • matterGaugeKineticSum source 0 point field base +
        parameter •
          (Complex.I • matterGaugeKineticSum source 0 point field linear) +
        parameter ^ 2 •
          (Complex.I • matterGaugeKineticSum source 0 point field
            quadratic) := by
  rw [matterGaugeKineticSum_add, matterGaugeKineticSum_add,
    matterGaugeKineticSum_real_smul, matterGaugeKineticSum_real_smul]
  simp only [smul_add, complex_smul_real_smul_comm]

/-- The Yukawa leg is exactly bilinear in the scalar and matter entries, so
their simultaneous affine path is exactly quadratic. -/
private theorem chiralExteriorYukawaAction_bilinear_quadratic
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    chiralExteriorYukawaAction
        (scalarCoordinateEquiv.symm
          (field.scalar + parameter • scalarLinear))
        (field.matter + parameter • matterLinear) =
      chiralExteriorYukawaAction
          (scalarCoordinateEquiv.symm field.scalar) field.matter +
        parameter •
          (chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm field.scalar) matterLinear +
            chiralExteriorYukawaAction
              (scalarCoordinateEquiv.symm scalarLinear) field.matter) +
        parameter ^ 2 •
          chiralExteriorYukawaAction
            (scalarCoordinateEquiv.symm scalarLinear) matterLinear := by
  have scalarSmul :
      scalarCoordinateEquiv.symm (parameter • scalarLinear) =
        (parameter : ℂ) • scalarCoordinateEquiv.symm scalarLinear := by
    change scalarCoordinateEquiv.symm ((parameter : ℂ) • scalarLinear) = _
    exact map_smul scalarCoordinateEquiv.symm (parameter : ℂ) scalarLinear
  have scalarAdd :
      scalarCoordinateEquiv.symm
          (field.scalar + parameter • scalarLinear) =
        scalarCoordinateEquiv.symm field.scalar +
          (parameter : ℂ) •
            scalarCoordinateEquiv.symm scalarLinear := by
    rw [map_add, scalarSmul]
  rw [scalarAdd]
  simp only [chiralExteriorYukawaAction_add,
    chiralExteriorYukawaAction_smul,
    LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
    matter_real_smul_eq_complex_smul]
  have parameterSquare :
      ((parameter ^ 2 : ℝ) : ℂ) = (parameter : ℂ) ^ 2 := by
    norm_cast
  rw [parameterSquare]
  module

/-- Point-field helper containing exactly the scalar, matter,
matter-covariant-jet, and conjugate-matter components of the joint path. -/
def withP286LinkedMatterPathData
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (matterDerivativeLinear matterDerivativeQuadratic :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (conjugateLinear : Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) : StageNineContinuumPointField :=
  { field with
    scalar := field.scalar + parameter • scalarLinear
    matter := field.matter + parameter • matterLinear
    matterCovariantDerivative :=
      field.matterCovariantDerivative +
        parameter • matterDerivativeLinear +
        parameter ^ 2 • matterDerivativeQuadratic
    conjugateMatter :=
      field.conjugateMatter + parameter • conjugateLinear }

/-- Linear coefficient of the complete Dirac--Yukawa vector. -/
def p286LinkedMatterVectorFirstCoefficient
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (matterDerivativeLinear :
      LorentzianIndex → DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  matterFieldVariationVector source point field matterLinear
      matterDerivativeLinear +
    scalarYukawaVariationVector field scalarLinear

/-- Quadratic coefficient of the complete Dirac--Yukawa vector.  It retains
both the quadratic covariant-jet response and the scalar--matter cross term. -/
def p286LinkedMatterVectorSecondCoefficient
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (matterDerivativeQuadratic :
      LorentzianIndex → DiracExteriorMatterCarrier) :
    DiracExteriorMatterCarrier :=
  Complex.I • matterGaugeKineticSum source 0 point field
      matterDerivativeQuadratic +
    chiralExteriorYukawaAction
      (scalarCoordinateEquiv.symm scalarLinear) matterLinear

/-- Exact quadratic normal form of the chart-zero Dirac--Yukawa vector. -/
theorem generatedContinuumMatterVector_p286LinkedMatterPath_quadratic
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (matterDerivativeLinear matterDerivativeQuadratic :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (conjugateLinear : Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedContinuumMatterVector source 0 point
        (withP286LinkedMatterPathData field scalarLinear matterLinear
          matterDerivativeLinear matterDerivativeQuadratic conjugateLinear
          parameter) =
      generatedContinuumMatterVector source 0 point field +
        parameter •
          p286LinkedMatterVectorFirstCoefficient source point field
            scalarLinear matterLinear matterDerivativeLinear +
        parameter ^ 2 •
          p286LinkedMatterVectorSecondCoefficient source point field
            scalarLinear matterLinear matterDerivativeQuadratic := by
  unfold generatedContinuumMatterVector
    p286LinkedMatterVectorFirstCoefficient
    p286LinkedMatterVectorSecondCoefficient
    matterFieldVariationVector
    scalarYukawaVariationVector
    withP286LinkedMatterPathData
  simp only [scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart, matterDerivativeFrameRelative_zeroChart,
    Pi.add_apply, Pi.smul_apply]
  simp only [← matterGaugeKineticSum_zeroChart source point field]
  have derivativePath :
      (fun direction =>
        field.matterCovariantDerivative direction +
          parameter • matterDerivativeLinear direction +
          parameter ^ 2 • matterDerivativeQuadratic direction) =
        field.matterCovariantDerivative +
          parameter • matterDerivativeLinear +
          parameter ^ 2 • matterDerivativeQuadratic := by
    rfl
  rw [derivativePath]
  rw [matterGaugeKineticVector_quadratic,
    chiralExteriorYukawaAction_bilinear_quadratic]
  module

/-- First coefficient of the volume-weighted matter density. -/
def p286LinkedMatterDensityFirstCoefficient
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (matterDerivativeLinear :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (conjugateLinear : Module.Dual ℂ DiracExteriorMatterCarrier) : ℝ :=
  generatedVolumeDensity field *
    ((field.conjugateMatter
        (p286LinkedMatterVectorFirstCoefficient source point field
          scalarLinear matterLinear matterDerivativeLinear)).re +
      (conjugateLinear
        (generatedContinuumMatterVector source 0 point field)).re)

/-- Second coefficient of the volume-weighted matter density. -/
def p286LinkedMatterDensitySecondCoefficient
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (matterDerivativeLinear matterDerivativeQuadratic :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (conjugateLinear : Module.Dual ℂ DiracExteriorMatterCarrier) : ℝ :=
  generatedVolumeDensity field *
    ((field.conjugateMatter
        (p286LinkedMatterVectorSecondCoefficient source point field
          scalarLinear matterLinear matterDerivativeQuadratic)).re +
      (conjugateLinear
        (p286LinkedMatterVectorFirstCoefficient source point field
          scalarLinear matterLinear matterDerivativeLinear)).re)

/-- Third coefficient of the volume-weighted matter density. -/
def p286LinkedMatterDensityThirdCoefficient
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (matterDerivativeQuadratic :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (conjugateLinear : Module.Dual ℂ DiracExteriorMatterCarrier) : ℝ :=
  generatedVolumeDensity field *
    (conjugateLinear
      (p286LinkedMatterVectorSecondCoefficient source point field
        scalarLinear matterLinear matterDerivativeQuadratic)).re

/-- Exact cubic normal form of the volume-weighted chart-zero matter
density. -/
theorem generatedContinuumMatterDensity_p286LinkedMatterPath_cubic
    (source : SmoothUnifiedSource)
    (point : BasePoint)
    (field : StageNineContinuumPointField)
    (scalarLinear : ScalarCoordinateCarrier)
    (matterLinear : DiracExteriorMatterCarrier)
    (matterDerivativeLinear matterDerivativeQuadratic :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (conjugateLinear : Module.Dual ℂ DiracExteriorMatterCarrier)
    (parameter : ℝ) :
    generatedVolumeDensity field *
        generatedContinuumMatterDensity source 0 point
          (withP286LinkedMatterPathData field scalarLinear matterLinear
            matterDerivativeLinear matterDerivativeQuadratic conjugateLinear
            parameter) =
      generatedVolumeDensity field *
          generatedContinuumMatterDensity source 0 point field +
        parameter *
          p286LinkedMatterDensityFirstCoefficient source point field
            scalarLinear matterLinear matterDerivativeLinear conjugateLinear +
        parameter ^ 2 *
          p286LinkedMatterDensitySecondCoefficient source point field
            scalarLinear matterLinear matterDerivativeLinear
            matterDerivativeQuadratic conjugateLinear +
        parameter ^ 3 *
          p286LinkedMatterDensityThirdCoefficient source point field
            scalarLinear matterLinear matterDerivativeQuadratic
            conjugateLinear := by
  unfold generatedContinuumMatterDensity
  rw [generatedContinuumMatterVector_p286LinkedMatterPath_quadratic]
  unfold withP286LinkedMatterPathData
    p286LinkedMatterDensityFirstCoefficient
    p286LinkedMatterDensitySecondCoefficient
    p286LinkedMatterDensityThirdCoefficient
  simp only [matterDualFrameRelative_zeroChart]
  simp only [map_add, dual_apply_real_smul, LinearMap.add_apply,
    LinearMap.smul_apply, complex_real_smul_eq_mul,
    Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-! ## Fidelity to the existing linked first coefficient -/

theorem p286LinkedMatterVectorFirstCoefficient_eq_linkedActive
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    p286LinkedMatterVectorFirstCoefficient source point
        (toContinuumPointField configuration point)
        (representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).scalar
        (representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).matter
        (linkedActiveMatterCovariantJetResponse configuration gaugeParameter
          point) =
      linkedActiveMatterVectorFirstVariation source configuration
        gaugeParameter point :=
  rfl

theorem p286LinkedMatterDensityFirstCoefficient_eq_linkedActive
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (point : BasePoint) :
    p286LinkedMatterDensityFirstCoefficient source point
        (toContinuumPointField configuration point)
        (representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).scalar
        (representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).matter
        (linkedActiveMatterCovariantJetResponse configuration gaugeParameter
          point)
        (representationDerivedP286CoupledGaugeTangentSection configuration
          gaugeParameter point).conjugateMatter =
      linkedActiveMatterDensityFirstVariation source configuration
        gaugeParameter point :=
  rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveMatterPathPolynomial

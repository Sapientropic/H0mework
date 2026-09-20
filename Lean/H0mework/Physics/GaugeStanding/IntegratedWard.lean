import H0mework.Physics.GaugeStanding.FullLocalDensityRegularity

/-!
# S9-C: integrated linked-active P286 Ward derivative

The exact local quartic and its internally generated coefficient
integrability are lifted to the actual raw four-dimensional Bochner action.
The derivative at the path origin is then read out as the integral of the
honest frozen-source torque.

This module does not assert that the torque integral vanishes.  A zero
derivative would require a source co-transformation or a separately generated
torque-balance theorem; it is not inserted as a stationarity premise here.
-/

open SaturationMonoid

namespace
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveIntegratedWard

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286FrozenSourceScalarTorque
open StageNineP286InfinitesimalGaugeTransformation
open StageNineP286LinkedActiveFullLocalDensityPolynomial
open StageNineP286LinkedActiveFullLocalDensityRegularity
open StageNineP286LinkedActiveLocalWardCoefficient
open StageNineP286LinkedActiveVariation
open MeasureTheory

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-- Every member of the linked primitive path lies in the declared raw
absolute-action domain once the initial actual does.  This is derived from
the exact local polynomial and the internally generated coefficient
integrability, not stored as a path receipt. -/
theorem p286LinkedActivePrimitivePath_localDensityIntegrable
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ) :
    HolonomicLocalDensityIntegrable source 0
      (p286LinkedActivePrimitivePath configuration gaugeParameter
        parameter) := by
  unfold HolonomicLocalDensityIntegrable
  rw [show
      (fun point : BasePoint =>
        generatedUnifiedLocalDensityAtBoundary source
          (sourceGeneratedUnifiedCouplings source) 0 point
          (toContinuumPointField
            (p286LinkedActivePrimitivePath configuration gaugeParameter
              parameter)
            point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
              (sourceGeneratedUnifiedCouplings source) 0 point
              (toContinuumPointField configuration point) +
            parameter *
              p286LinkedActiveFullLocalFirstCoefficient source configuration
                gaugeParameter point +
          parameter ^ 2 *
            p286LinkedActiveFullLocalSecondCoefficient source configuration
              gaugeParameter point +
        parameter ^ 3 *
          p286LinkedActiveFullLocalThirdCoefficient source configuration
            gaugeParameter point +
      parameter ^ 4 *
        p286LinkedActiveFullLocalFourthCoefficient source configuration
          gaugeParameter point by
    funext point
    exact
      generatedUnifiedLocalDensity_p286LinkedActivePrimitivePath_quartic
        source configuration smooth gaugeParameter parameter point]
  exact
    (((densityIntegrable.add
      ((p286LinkedActiveFullLocalFirstCoefficient_integrable source
        configuration smooth gaugeParameter).const_mul parameter)).add
      ((p286LinkedActiveFullLocalSecondCoefficient_integrable source
        configuration smooth nondegenerate gaugeParameter).const_mul
          (parameter ^ 2))).add
      ((p286LinkedActiveFullLocalThirdCoefficient_integrable source
        configuration smooth nondegenerate gaugeParameter).const_mul
          (parameter ^ 3))).add
      ((p286LinkedActiveFullLocalFourthCoefficient_integrable source
        configuration smooth nondegenerate gaugeParameter).const_mul
          (parameter ^ 4))

/-- The complete raw action is exactly quartic along the one
source/action-generated linked P286 primitive path.  Integrability of every
coefficient is derived by the imported regularity module rather than supplied
by the caller. -/
theorem holonomicIntegratedUnifiedAction_p286LinkedActivePrimitivePath_quartic
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (gaugeParameter : P286InfinitesimalGaugeParameter)
    (parameter : ℝ) :
    holonomicIntegratedUnifiedAction source 0
        (p286LinkedActivePrimitivePath configuration gaugeParameter
          parameter) =
      holonomicIntegratedUnifiedAction source 0 configuration +
        parameter *
          (∫ point : BasePoint,
            p286LinkedActiveFullLocalFirstCoefficient source configuration
              gaugeParameter point) +
        parameter ^ 2 *
          (∫ point : BasePoint,
            p286LinkedActiveFullLocalSecondCoefficient source configuration
              gaugeParameter point) +
        parameter ^ 3 *
          (∫ point : BasePoint,
            p286LinkedActiveFullLocalThirdCoefficient source configuration
              gaugeParameter point) +
        parameter ^ 4 *
          (∫ point : BasePoint,
            p286LinkedActiveFullLocalFourthCoefficient source configuration
              gaugeParameter point) := by
  unfold holonomicIntegratedUnifiedAction
  unfold sourceGeneratedIntegratedUnifiedAction
  unfold integratedUnifiedActionAtBoundary
  simp only [toContinuumFieldSection]
  have pointwise : (fun point : BasePoint =>
      generatedUnifiedLocalDensityAtBoundary source
        (sourceGeneratedUnifiedCouplings source) 0 point
        (toContinuumPointField
          (p286LinkedActivePrimitivePath configuration gaugeParameter
            parameter)
          point)) =
      fun point =>
        generatedUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (toContinuumPointField configuration point) +
          parameter *
            p286LinkedActiveFullLocalFirstCoefficient source configuration
              gaugeParameter point +
          parameter ^ 2 *
            p286LinkedActiveFullLocalSecondCoefficient source configuration
              gaugeParameter point +
          parameter ^ 3 *
            p286LinkedActiveFullLocalThirdCoefficient source configuration
              gaugeParameter point +
          parameter ^ 4 *
            p286LinkedActiveFullLocalFourthCoefficient source configuration
              gaugeParameter point := by
    funext point
    exact
      generatedUnifiedLocalDensity_p286LinkedActivePrimitivePath_quartic
        source configuration smooth gaugeParameter parameter point
  rw [pointwise]
  have firstIntegrable :=
    p286LinkedActiveFullLocalFirstCoefficient_integrable source configuration
      smooth gaugeParameter
  have secondIntegrable :=
    p286LinkedActiveFullLocalSecondCoefficient_integrable source configuration
      smooth nondegenerate gaugeParameter
  have thirdIntegrable :=
    p286LinkedActiveFullLocalThirdCoefficient_integrable source configuration
      smooth nondegenerate gaugeParameter
  have fourthIntegrable :=
    p286LinkedActiveFullLocalFourthCoefficient_integrable source configuration
      smooth nondegenerate gaugeParameter
  calc
    (∫ point : BasePoint,
        generatedUnifiedLocalDensityAtBoundary source
                (sourceGeneratedUnifiedCouplings source) 0 point
                (toContinuumPointField configuration point) +
              parameter *
                p286LinkedActiveFullLocalFirstCoefficient source configuration
                  gaugeParameter point +
            parameter ^ 2 *
              p286LinkedActiveFullLocalSecondCoefficient source configuration
                gaugeParameter point +
          parameter ^ 3 *
            p286LinkedActiveFullLocalThirdCoefficient source configuration
              gaugeParameter point +
        parameter ^ 4 *
          p286LinkedActiveFullLocalFourthCoefficient source configuration
            gaugeParameter point) =
      (∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
                  (sourceGeneratedUnifiedCouplings source) 0 point
                  (toContinuumPointField configuration point) +
                parameter *
                  p286LinkedActiveFullLocalFirstCoefficient source
                    configuration gaugeParameter point +
              parameter ^ 2 *
                p286LinkedActiveFullLocalSecondCoefficient source
                  configuration gaugeParameter point +
            parameter ^ 3 *
              p286LinkedActiveFullLocalThirdCoefficient source configuration
                gaugeParameter point) +
        (∫ point : BasePoint,
          parameter ^ 4 *
            p286LinkedActiveFullLocalFourthCoefficient source configuration
              gaugeParameter point) := by
      exact integral_add
        (((densityIntegrable.add
          (firstIntegrable.const_mul parameter)).add
          (secondIntegrable.const_mul (parameter ^ 2))).add
          (thirdIntegrable.const_mul (parameter ^ 3)))
        (fourthIntegrable.const_mul (parameter ^ 4))
    _ =
      ((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
                  (sourceGeneratedUnifiedCouplings source) 0 point
                  (toContinuumPointField configuration point) +
                parameter *
                  p286LinkedActiveFullLocalFirstCoefficient source
                    configuration gaugeParameter point +
              parameter ^ 2 *
                p286LinkedActiveFullLocalSecondCoefficient source
                  configuration gaugeParameter point) +
        (∫ point : BasePoint,
          parameter ^ 3 *
            p286LinkedActiveFullLocalThirdCoefficient source configuration
              gaugeParameter point)) +
        (∫ point : BasePoint,
          parameter ^ 4 *
            p286LinkedActiveFullLocalFourthCoefficient source configuration
              gaugeParameter point) := by
      exact congrArg
        (fun value : ℝ =>
          value +
            (∫ point : BasePoint,
              parameter ^ 4 *
                p286LinkedActiveFullLocalFourthCoefficient source
                  configuration gaugeParameter point))
        (integral_add
          ((densityIntegrable.add
            (firstIntegrable.const_mul parameter)).add
            (secondIntegrable.const_mul (parameter ^ 2)))
          (thirdIntegrable.const_mul (parameter ^ 3)))
    _ =
      (((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
                (sourceGeneratedUnifiedCouplings source) 0 point
                (toContinuumPointField configuration point) +
              parameter *
                p286LinkedActiveFullLocalFirstCoefficient source configuration
                  gaugeParameter point) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            p286LinkedActiveFullLocalSecondCoefficient source configuration
              gaugeParameter point)) +
        (∫ point : BasePoint,
          parameter ^ 3 *
            p286LinkedActiveFullLocalThirdCoefficient source configuration
              gaugeParameter point)) +
        (∫ point : BasePoint,
          parameter ^ 4 *
            p286LinkedActiveFullLocalFourthCoefficient source configuration
              gaugeParameter point) := by
      exact congrArg
        (fun value : ℝ =>
          (value +
              (∫ point : BasePoint,
                parameter ^ 3 *
                  p286LinkedActiveFullLocalThirdCoefficient source
                    configuration gaugeParameter point)) +
            (∫ point : BasePoint,
              parameter ^ 4 *
                p286LinkedActiveFullLocalFourthCoefficient source
                  configuration gaugeParameter point))
        (integral_add
          (densityIntegrable.add (firstIntegrable.const_mul parameter))
          (secondIntegrable.const_mul (parameter ^ 2)))
    _ =
      ((((∫ point : BasePoint,
          generatedUnifiedLocalDensityAtBoundary source
            (sourceGeneratedUnifiedCouplings source) 0 point
            (toContinuumPointField configuration point)) +
        (∫ point : BasePoint,
          parameter *
            p286LinkedActiveFullLocalFirstCoefficient source configuration
              gaugeParameter point)) +
        (∫ point : BasePoint,
          parameter ^ 2 *
            p286LinkedActiveFullLocalSecondCoefficient source configuration
              gaugeParameter point)) +
        (∫ point : BasePoint,
          parameter ^ 3 *
            p286LinkedActiveFullLocalThirdCoefficient source configuration
              gaugeParameter point)) +
        (∫ point : BasePoint,
          parameter ^ 4 *
            p286LinkedActiveFullLocalFourthCoefficient source configuration
              gaugeParameter point) := by
      exact congrArg
        (fun value : ℝ =>
          ((value +
              (∫ point : BasePoint,
                parameter ^ 2 *
                  p286LinkedActiveFullLocalSecondCoefficient source
                    configuration gaugeParameter point)) +
              (∫ point : BasePoint,
                parameter ^ 3 *
                  p286LinkedActiveFullLocalThirdCoefficient source
                    configuration gaugeParameter point)) +
            (∫ point : BasePoint,
              parameter ^ 4 *
                p286LinkedActiveFullLocalFourthCoefficient source
                  configuration gaugeParameter point))
        (integral_add densityIntegrable
          (firstIntegrable.const_mul parameter))
    _ = _ := by
      rw [integral_const_mul, integral_const_mul, integral_const_mul,
        integral_const_mul]

/-- The raw integrated action has the integral of the generated first
coefficient as its actual derivative at the path origin. -/
theorem holonomicIntegratedUnifiedAction_p286LinkedActivePrimitivePath_hasDerivAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    HasDerivAt
      (fun parameter =>
        holonomicIntegratedUnifiedAction source 0
          (p286LinkedActivePrimitivePath configuration gaugeParameter
            parameter))
      (∫ point : BasePoint,
        p286LinkedActiveFullLocalFirstCoefficient source configuration
          gaugeParameter point)
      0 := by
  let firstIntegral := ∫ point : BasePoint,
    p286LinkedActiveFullLocalFirstCoefficient source configuration
      gaugeParameter point
  let secondIntegral := ∫ point : BasePoint,
    p286LinkedActiveFullLocalSecondCoefficient source configuration
      gaugeParameter point
  let thirdIntegral := ∫ point : BasePoint,
    p286LinkedActiveFullLocalThirdCoefficient source configuration
      gaugeParameter point
  let fourthIntegral := ∫ point : BasePoint,
    p286LinkedActiveFullLocalFourthCoefficient source configuration
      gaugeParameter point
  have actionEquality :
      (fun parameter =>
        holonomicIntegratedUnifiedAction source 0
          (p286LinkedActivePrimitivePath configuration gaugeParameter
            parameter)) =
      fun parameter =>
        holonomicIntegratedUnifiedAction source 0 configuration +
          parameter * firstIntegral +
          parameter ^ 2 * secondIntegral +
          parameter ^ 3 * thirdIntegral +
          parameter ^ 4 * fourthIntegral := by
    funext parameter
    exact
      holonomicIntegratedUnifiedAction_p286LinkedActivePrimitivePath_quartic
        source configuration smooth nondegenerate densityIntegrable
        gaugeParameter parameter
  rw [actionEquality]
  change HasDerivAt
    ((((fun parameter =>
        holonomicIntegratedUnifiedAction source 0 configuration +
          parameter * firstIntegral) +
        fun parameter => parameter ^ 2 * secondIntegral) +
        fun parameter => parameter ^ 3 * thirdIntegral) +
        fun parameter => parameter ^ 4 * fourthIntegral)
      firstIntegral 0
  simpa using
    ((((((hasDerivAt_id (x := (0 : ℝ))).mul_const firstIntegral).const_add
      (holonomicIntegratedUnifiedAction source 0 configuration)).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 2).mul_const secondIntegral)).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 3).mul_const thirdIntegral)).add
      (((hasDerivAt_id (x := (0 : ℝ))).pow 4).mul_const fourthIntegral))

/-- The same derivative, faithfully read out as the integral of the actual
frozen-source scalar torque.  No zero-torque or stationarity conclusion is
made. -/
theorem
    holonomicIntegratedUnifiedAction_p286LinkedActivePrimitivePath_hasDerivAt_torque
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (densityIntegrable : HolonomicLocalDensityIntegrable source 0 configuration)
    (gaugeParameter : P286InfinitesimalGaugeParameter) :
    HasDerivAt
      (fun parameter =>
        holonomicIntegratedUnifiedAction source 0
          (p286LinkedActivePrimitivePath configuration gaugeParameter
            parameter))
      (∫ point : BasePoint,
        p286FrozenSourceScalarTorqueDensity source configuration
          gaugeParameter point)
      0 := by
  have coefficientIntegral :
      (∫ point : BasePoint,
        p286LinkedActiveFullLocalFirstCoefficient source configuration
          gaugeParameter point) =
      ∫ point : BasePoint,
        p286FrozenSourceScalarTorqueDensity source configuration
          gaugeParameter point := by
    apply integral_congr_ae
    filter_upwards with point
    rw [p286LinkedActiveFullLocalFirstCoefficient_eq_existing]
    exact linkedActiveFullLocalFirstVariationDensity_eq_torque source
      configuration smooth gaugeParameter point
  rw [← coefficientIntegral]
  exact
    holonomicIntegratedUnifiedAction_p286LinkedActivePrimitivePath_hasDerivAt
      source configuration smooth nondegenerate densityIntegrable
        gaugeParameter

end

end
  SaturationMonoid.PhysicsCore.StageNineP286LinkedActiveIntegratedWard

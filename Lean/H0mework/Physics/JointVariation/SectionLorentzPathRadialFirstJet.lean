import H0mework.Physics.JointVariation.SectionLorentzPathGlobalOperator
import H0mework.Physics.Jets.RadialCurveIntegralFirstJet

/-!
# Radial first jet of the synchronized-section Lorentz path

The four-leg source/current occurrence first emits a primitive radial Lorentz
connection.  This module differentiates that exact output.  The derivative
retains the endpoint profile and its radial variation term; it assumes no
closedness and accepts no target jet, residual, support, branch, or completed
field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineRadialCurveIntegralFirstJet

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-- The unconditional first jet of the already emitted radial increment. -/
def completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : BasePoint →L[ℝ] LorentzBivectorOneForm :=
  ∫ parameter in (0 : ℝ)..1,
    radialCurveIntegralDerivativeIntegrand
      (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
        source current)
      point parameter

@[simp] theorem
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
        source current 0 =
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
        source current 0 := by
  simp [completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet,
    radialCurveIntegralDerivativeIntegrand]

theorem
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialIncrement_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
          source current))
    (point : BasePoint) :
    HasFDerivAt
      (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialIncrement
        source current)
      (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
        source current point)
      point := by
  exact radialCurveIntegral_hasFDerivAt_of_contDiff
    (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
      source current)
    regular point

/-- The emitted primitive path connection realizes the unconditional radial
first jet at every point where its action-owned contact profile is `C¹`. -/
theorem
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
          source current))
    (point : BasePoint) :
    HasFDerivAt
      (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField
        source current)
      (radialLorentzConnectionLiftCLM.comp
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
          source current point))
      point := by
  change HasFDerivAt
    (fun endpoint =>
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathAnchor
          source current +
        radialLorentzConnectionLiftCLM
          (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialIncrement
            source current endpoint)) _ point
  have lifted :=
    radialLorentzConnectionLiftCLM.hasFDerivAt.comp point
      (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialIncrement_hasFDerivAt_of_contDiff
        source current regular point)
  convert lifted.const_add
      (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathAnchor
        source current) using 1 <;>
    rfl

private theorem
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField_coordinate_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
          source current))
    (point : BasePoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    HasFDerivAt
      (fun endpoint =>
        completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField
          source current endpoint formDirection internalOut internalIn)
      ((radialLorentzConnectionCoordinateCLM
        formDirection internalOut internalIn).comp
          (radialLorentzConnectionLiftCLM.comp
            (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
              source current point)))
      point := by
  exact
    (radialLorentzConnectionCoordinateCLM
      formDirection internalOut internalIn).hasFDerivAt.comp point
      (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField_hasFDerivAt_of_contDiff
        source current regular point)

/-- The lowered primitive derivative of the emitted path field is exactly
its radial exactification first jet. -/
theorem
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField_loweredFirstJet_eq_radialFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
          source current))
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        fderiv ℝ
          (fun endpoint =>
            completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField
              source current endpoint formDirection
              (pairFirst internalPair) (pairSecond internalPair))
          point (coordinateDirection derivativeDirection) =
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
        source current point (coordinateDirection derivativeDirection)
        formDirection internalPair := by
  rw [
    (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField_coordinate_hasFDerivAt_of_contDiff
      source current regular point formDirection
      (pairFirst internalPair) (pairSecond internalPair)).fderiv]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change
    loweredLorentzConnectionCoefficient
        (lorentzSkewConnectionOfBivectorOneForm
          (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
            source current point (coordinateDirection derivativeDirection)))
        formDirection internalPair = _
  exact loweredLorentzConnectionCoefficient_ofBivectorOneForm
    (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
      source current point (coordinateDirection derivativeDirection))
    formDirection internalPair

/-- Whole-emitter form of the unconditional path first-jet theorem. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_loweredConnectionFirstJet_eq_radialFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
          source current))
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
            source current)
          point derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
        source current point (coordinateDirection derivativeDirection)
        formDirection internalPair := by
  unfold gravityConnectionDerivative
  rw [
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_gravityConnection]
  exact
    completeJointActionSpacetimeSectionCartanECSynchronizedLorentzPathConnectionField_loweredFirstJet_eq_radialFirstJet
      source current regular point derivativeDirection formDirection internalPair

/-- Exact-occurrence form: no sibling completion payload can alter the
authoritative radial first jet at fixed source/current indices. -/
theorem
    CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence.loweredConnectionFirstJet_eq_radialFirstJet
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence
        source current)
    (regular :
      ContDiff ℝ 1
        (completeJointActionSpacetimeSectionCartanECSynchronizedLorentzJetCLM
          source current))
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative occurrence.finalActual
          point derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      completeJointActionSpacetimeSectionCartanECSynchronizedLorentzRadialFirstJet
        source current point (coordinateDirection derivativeDirection)
        formDirection internalPair := by
  rw [occurrence.eq_generated]
  exact
    sourceActionGeneratedDiracDualCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator_loweredConnectionFirstJet_eq_radialFirstJet
      source current regular point derivativeDirection formDirection internalPair

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator

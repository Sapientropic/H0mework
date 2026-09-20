import H0mework.Physics.SynchronizedJoint.GravityTailLorentzPathOperator
import H0mework.Physics.Jets.RadialCurveIntegralFirstJet

/-!
# Radial first jet of the Cartan--EC gravity-tail Lorentz path

The source/current occurrence has already emitted its primitive radial
connection.  This module differentiates that exact output.  It assumes no
closedness and accepts no target jet, residual, support, branch, or completed
field.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator

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

/-- Unconditional first jet of the emitted gravity-tail radial increment. -/
def cartanECSynchronizedGravityTailRadialFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) : BasePoint →L[ℝ] LorentzBivectorOneForm :=
  ∫ parameter in (0 : ℝ)..1,
    radialCurveIntegralDerivativeIntegrand
      (cartanECSynchronizedGravityTailJetCLM source current)
      point parameter

@[simp] theorem cartanECSynchronizedGravityTailRadialFirstJet_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    cartanECSynchronizedGravityTailRadialFirstJet source current 0 =
      cartanECSynchronizedGravityTailJetCLM source current 0 := by
  simp [cartanECSynchronizedGravityTailRadialFirstJet,
    radialCurveIntegralDerivativeIntegrand]

theorem
    cartanECSynchronizedGravityTailRadialIncrement_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (cartanECSynchronizedGravityTailJetCLM source current))
    (point : BasePoint) :
    HasFDerivAt
      (cartanECSynchronizedGravityTailRadialIncrement source current)
      (cartanECSynchronizedGravityTailRadialFirstJet source current point)
      point := by
  exact radialCurveIntegral_hasFDerivAt_of_contDiff
    (cartanECSynchronizedGravityTailJetCLM source current) regular point

theorem
    cartanECSynchronizedGravityTailRadialIncrement_hasFDerivAt_zero_of_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cartanECSynchronizedGravityTailJetCLM source current) 0) :
    HasFDerivAt
      (cartanECSynchronizedGravityTailRadialIncrement source current)
      (cartanECSynchronizedGravityTailJetCLM source current 0) 0 := by
  simpa [cartanECSynchronizedGravityTailRadialIncrement] using
    radialCurveIntegral_hasFDerivAt_zero_of_contDiffAt
      (cartanECSynchronizedGravityTailJetCLM source current) regular

/-- The primitive path connection realizes the unconditional radial first
jet wherever its occurrence-native profile is `C¹`. -/
theorem
    cartanECSynchronizedGravityTailPathConnectionField_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (cartanECSynchronizedGravityTailJetCLM source current))
    (point : BasePoint) :
    HasFDerivAt
      (cartanECSynchronizedGravityTailPathConnectionField source current)
      (radialLorentzConnectionLiftCLM.comp
        (cartanECSynchronizedGravityTailRadialFirstJet
          source current point))
      point := by
  change HasFDerivAt
    (fun endpoint =>
      cartanECSynchronizedGravityTailPathAnchor source current +
        radialLorentzConnectionLiftCLM
          (cartanECSynchronizedGravityTailRadialIncrement
            source current endpoint)) _ point
  have lifted :=
    radialLorentzConnectionLiftCLM.hasFDerivAt.comp point
      (cartanECSynchronizedGravityTailRadialIncrement_hasFDerivAt_of_contDiff
        source current regular point)
  convert lifted.const_add
      (cartanECSynchronizedGravityTailPathAnchor source current) using 1 <;>
    rfl

theorem
    cartanECSynchronizedGravityTailPathConnectionField_hasFDerivAt_zero_of_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cartanECSynchronizedGravityTailJetCLM source current) 0) :
    HasFDerivAt
      (cartanECSynchronizedGravityTailPathConnectionField source current)
      (radialLorentzConnectionLiftCLM.comp
        (cartanECSynchronizedGravityTailJetCLM source current 0)) 0 := by
  change HasFDerivAt
    (fun endpoint =>
      cartanECSynchronizedGravityTailPathAnchor source current +
        radialLorentzConnectionLiftCLM
          (cartanECSynchronizedGravityTailRadialIncrement
            source current endpoint)) _ 0
  have lifted :=
    radialLorentzConnectionLiftCLM.hasFDerivAt.comp 0
      (cartanECSynchronizedGravityTailRadialIncrement_hasFDerivAt_zero_of_contDiffAt
        source current regular)
  convert lifted.const_add
      (cartanECSynchronizedGravityTailPathAnchor source current) using 1 <;>
    rfl

private theorem
    cartanECSynchronizedGravityTailPathConnectionField_coordinate_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (cartanECSynchronizedGravityTailJetCLM source current))
    (point : BasePoint)
    (formDirection internalOut internalIn : LorentzianIndex) :
    HasFDerivAt
      (fun endpoint =>
        cartanECSynchronizedGravityTailPathConnectionField
          source current endpoint formDirection internalOut internalIn)
      ((radialLorentzConnectionCoordinateCLM
        formDirection internalOut internalIn).comp
          (radialLorentzConnectionLiftCLM.comp
            (cartanECSynchronizedGravityTailRadialFirstJet
              source current point)))
      point := by
  exact
    (radialLorentzConnectionCoordinateCLM
      formDirection internalOut internalIn).hasFDerivAt.comp point
      (cartanECSynchronizedGravityTailPathConnectionField_hasFDerivAt_of_contDiff
        source current regular point)

private theorem
    cartanECSynchronizedGravityTailPathConnectionField_coordinate_hasFDerivAt_zero_of_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cartanECSynchronizedGravityTailJetCLM source current) 0)
    (formDirection internalOut internalIn : LorentzianIndex) :
    HasFDerivAt
      (fun endpoint =>
        cartanECSynchronizedGravityTailPathConnectionField
          source current endpoint formDirection internalOut internalIn)
      ((radialLorentzConnectionCoordinateCLM
        formDirection internalOut internalIn).comp
          (radialLorentzConnectionLiftCLM.comp
            (cartanECSynchronizedGravityTailJetCLM source current 0))) 0 := by
  exact
    (radialLorentzConnectionCoordinateCLM
      formDirection internalOut internalIn).hasFDerivAt.comp 0
      (cartanECSynchronizedGravityTailPathConnectionField_hasFDerivAt_zero_of_contDiffAt
        source current regular)

/-- The lowered derivative of the emitted path field is exactly its radial
exactification first jet. -/
theorem
    cartanECSynchronizedGravityTailPathConnectionField_loweredFirstJet_eq_radialFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (cartanECSynchronizedGravityTailJetCLM source current))
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        fderiv ℝ
          (fun endpoint =>
            cartanECSynchronizedGravityTailPathConnectionField
              source current endpoint formDirection
              (pairFirst internalPair) (pairSecond internalPair))
          point (coordinateDirection derivativeDirection) =
      cartanECSynchronizedGravityTailRadialFirstJet
        source current point (coordinateDirection derivativeDirection)
        formDirection internalPair := by
  rw [
    (cartanECSynchronizedGravityTailPathConnectionField_coordinate_hasFDerivAt_of_contDiff
      source current regular point formDirection
      (pairFirst internalPair) (pairSecond internalPair)).fderiv]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change
    loweredLorentzConnectionCoefficient
        (lorentzSkewConnectionOfBivectorOneForm
          (cartanECSynchronizedGravityTailRadialFirstJet
            source current point (coordinateDirection derivativeDirection)))
        formDirection internalPair = _
  exact loweredLorentzConnectionCoefficient_ofBivectorOneForm
    (cartanECSynchronizedGravityTailRadialFirstJet
      source current point (coordinateDirection derivativeDirection))
    formDirection internalPair

/-- Local source form of the connection first-jet readback. -/
theorem
    cartanECSynchronizedGravityTailPathConnectionField_loweredFirstJet_zero_of_contDiffAt
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular : ContDiffAt ℝ 0
      (cartanECSynchronizedGravityTailJetCLM source current) 0)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        fderiv ℝ
          (fun endpoint =>
            cartanECSynchronizedGravityTailPathConnectionField
              source current endpoint formDirection
              (pairFirst internalPair) (pairSecond internalPair))
          0 (coordinateDirection derivativeDirection) =
      cartanECSynchronizedGravityTailJetCLM source current 0
        (coordinateDirection derivativeDirection) formDirection
        internalPair := by
  rw [
    (cartanECSynchronizedGravityTailPathConnectionField_coordinate_hasFDerivAt_zero_of_contDiffAt
      source current regular formDirection
      (pairFirst internalPair) (pairSecond internalPair)).fderiv]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change
    loweredLorentzConnectionCoefficient
        (lorentzSkewConnectionOfBivectorOneForm
          (cartanECSynchronizedGravityTailJetCLM source current 0
            (coordinateDirection derivativeDirection)))
        formDirection internalPair = _
  exact loweredLorentzConnectionCoefficient_ofBivectorOneForm
    (cartanECSynchronizedGravityTailJetCLM source current 0
      (coordinateDirection derivativeDirection))
    formDirection internalPair

/-- Whole-emitter form of the unconditional path first-jet theorem. -/
theorem
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_loweredConnectionFirstJet_eq_radialFirstJet
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1
        (cartanECSynchronizedGravityTailJetCLM source current))
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator
            source current)
          point derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      cartanECSynchronizedGravityTailRadialFirstJet
        source current point (coordinateDirection derivativeDirection)
        formDirection internalPair := by
  unfold gravityConnectionDerivative
  rw [
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_gravityConnection]
  exact
    cartanECSynchronizedGravityTailPathConnectionField_loweredFirstJet_eq_radialFirstJet
      source current regular point derivativeDirection formDirection internalPair

/-- Exact-occurrence form: fixed source/current custody leaves no sibling
completion payload that can alter the radial first jet. -/
theorem
    CartanECSynchronizedGravityTailOccurrence.loweredConnectionFirstJet_eq_radialFirstJet
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence : CartanECSynchronizedGravityTailOccurrence source current)
    (regular :
      ContDiff ℝ 1
        (cartanECSynchronizedGravityTailJetCLM source current))
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative occurrence.finalActual
          point derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      cartanECSynchronizedGravityTailRadialFirstJet
        source current point (coordinateDirection derivativeDirection)
        formDirection internalPair := by
  rw [occurrence.eq_generated]
  exact
    sourceActionGeneratedDiracDualCartanECSynchronizedGravityTailLorentzPathOperator_loweredConnectionFirstJet_eq_radialFirstJet
      source current regular point derivativeDirection formDirection internalPair

end


end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanECSynchronizedGravityTailLorentzPathOperator

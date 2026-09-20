import H0mework.Physics.ConstrainedCauchy.FixedJointDirectPrimitivePath
import H0mework.Physics.Jets.RadialCurveIntegralFirstJet

/-!
# Radial first jet of the direct complete-joint primitive path

The direct primitive writer has already emitted one coframe and Lorentz path
from the same source and section input.  This module differentiates those
outputs with the unconditional radial calculus and reads the resulting first
jets through the writer and the fixed P506/L0 occurrence.

Only `C¹` regularity of the exact contact-indexed one-forms is assumed.  No
closedness, target, residual, support, branch, or completion receipt enters a
theorem mouth.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePathRadialFirstJet

open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePath
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityReactionInstallation
open StageNineHolonomicField
open StageNineLorentzConnectionVariation
open StageNineRadialCurveIntegralFirstJet

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance directCoframeNormedAddCommGroup :
    NormedAddCommGroup LorentzianCoframe :=
  inferInstanceAs (NormedAddCommGroup (Fin 4 → Fin 4 → ℝ))

local instance directCoframeNormedSpace :
    NormedSpace ℝ LorentzianCoframe :=
  inferInstanceAs (NormedSpace ℝ (Fin 4 → Fin 4 → ℝ))

/-! ## Coframe path -/

/-- Coordinatewise packaging of the unconditional radial derivative of the
direct primitive coframe path. -/
def directPrimitivePathCoframeRadialFirstJet
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (point : BasePoint) : BasePoint →L[ℝ] LorentzianCoframe :=
  ContinuousLinearMap.pi fun internal =>
    ContinuousLinearMap.pi fun coordinate =>
      ∫ parameter in (0 : ℝ)..1,
        radialCurveIntegralDerivativeIntegrand
          (fun contact =>
            directPrimitivePathCoframeJetCoordinateCLM
              source sectionInput contact internal coordinate)
          point parameter

theorem directPrimitivePathCoframeRadialIncrement_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ 1 (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate))
    (point : BasePoint) :
    HasFDerivAt
      (directPrimitivePathCoframeRadialIncrement source sectionInput)
      (directPrimitivePathCoframeRadialFirstJet source sectionInput point)
      point := by
  unfold directPrimitivePathCoframeRadialFirstJet
  apply hasFDerivAt_pi.mpr
  intro internal
  apply hasFDerivAt_pi.mpr
  intro coordinate
  simpa [directPrimitivePathCoframeRadialIncrement] using
    radialCurveIntegral_hasFDerivAt_of_contDiff
      (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate)
      (regular internal coordinate) point

/-- The constant origin coframe contributes no derivative; the complete
radial exactification term is retained coordinatewise. -/
theorem directPrimitivePathCoframeField_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ 1 (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate))
    (point : BasePoint) :
    HasFDerivAt
      (directPrimitivePathCoframeField source sectionInput)
      (directPrimitivePathCoframeRadialFirstJet source sectionInput point)
      point := by
  change HasFDerivAt
    (fun candidate => sectionInput.coframe 0 +
      directPrimitivePathCoframeRadialIncrement
        source sectionInput candidate)
    (directPrimitivePathCoframeRadialFirstJet source sectionInput point)
    point
  exact
    (directPrimitivePathCoframeRadialIncrement_hasFDerivAt_of_contDiff
      source sectionInput regular point).const_add (sectionInput.coframe 0)

/-- Generic writer readback of the already emitted direct coframe field. -/
theorem
    sourceActionGeneratedDiracDualDirectPrimitivePathWrite_coframe_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ 1 (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          source sectionInput contact internal coordinate))
    (point : BasePoint) :
    HasFDerivAt
      (sourceActionGeneratedDiracDualDirectPrimitivePathWrite
        source sectionInput).coframe
      (directPrimitivePathCoframeRadialFirstJet source sectionInput point)
      point := by
  exact directPrimitivePathCoframeField_hasFDerivAt_of_contDiff
    source sectionInput regular point

/-! ## Lorentz path -/

/-- The unconditional first jet of the direct Lorentz radial compiler. -/
def directPrimitivePathLorentzRadialFirstJet
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (point : BasePoint) : BasePoint →L[ℝ] LorentzBivectorOneForm :=
  ∫ parameter in (0 : ℝ)..1,
    radialCurveIntegralDerivativeIntegrand
      (directPrimitivePathLorentzJetCLM source sectionInput)
      point parameter

theorem directPrimitivePathLorentzRadialIncrement_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1 (directPrimitivePathLorentzJetCLM source sectionInput))
    (point : BasePoint) :
    HasFDerivAt
      (directPrimitivePathLorentzRadialIncrement source sectionInput)
      (directPrimitivePathLorentzRadialFirstJet source sectionInput point)
      point := by
  exact radialCurveIntegral_hasFDerivAt_of_contDiff
    (directPrimitivePathLorentzJetCLM source sectionInput) regular point

/-- The emitted connection realizes the same unconditional radial first
jet after the canonical Lorentz lift. -/
theorem directPrimitivePathConnectionField_hasFDerivAt_of_contDiff
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1 (directPrimitivePathLorentzJetCLM source sectionInput))
    (point : BasePoint) :
    HasFDerivAt
      (directPrimitivePathConnectionField source sectionInput)
      (radialLorentzConnectionLiftCLM.comp
        (directPrimitivePathLorentzRadialFirstJet
          source sectionInput point))
      point := by
  change HasFDerivAt
    (fun endpoint =>
      sectionInput.gravityConnection 0 +
        radialLorentzConnectionLiftCLM
          (directPrimitivePathLorentzRadialIncrement
            source sectionInput endpoint)) _ point
  have lifted :=
    radialLorentzConnectionLiftCLM.hasFDerivAt.comp point
      (directPrimitivePathLorentzRadialIncrement_hasFDerivAt_of_contDiff
        source sectionInput regular point)
  convert lifted.const_add (sectionInput.gravityConnection 0) using 1 <;>
    rfl

/-- Coordinate readback on the generic source/section-input primitive
writer. -/
theorem
    sourceActionGeneratedDiracDualDirectPrimitivePathWrite_loweredConnectionFirstJet_eq_radialFirstJet
    (source : SmoothUnifiedSource)
    (sectionInput : StageNineHolonomicConfiguration)
    (regular :
      ContDiff ℝ 1 (directPrimitivePathLorentzJetCLM source sectionInput))
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (sourceActionGeneratedDiracDualDirectPrimitivePathWrite
            source sectionInput)
          point derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      directPrimitivePathLorentzRadialFirstJet source sectionInput point
        (coordinateDirection derivativeDirection) formDirection internalPair := by
  unfold gravityConnectionDerivative
  change
    minkowskiInternalSign (pairFirst internalPair) *
        fderiv ℝ
          (fun endpoint =>
            directPrimitivePathConnectionField source sectionInput endpoint
              formDirection (pairFirst internalPair) (pairSecond internalPair))
          point (coordinateDirection derivativeDirection) = _
  have coordinateDerivative :
      HasFDerivAt
        (fun endpoint =>
          directPrimitivePathConnectionField source sectionInput endpoint
            formDirection (pairFirst internalPair) (pairSecond internalPair))
        ((radialLorentzConnectionCoordinateCLM formDirection
          (pairFirst internalPair) (pairSecond internalPair)).comp
            (radialLorentzConnectionLiftCLM.comp
              (directPrimitivePathLorentzRadialFirstJet
                source sectionInput point))) point := by
    exact
      (radialLorentzConnectionCoordinateCLM formDirection
        (pairFirst internalPair) (pairSecond internalPair)).hasFDerivAt.comp point
        (directPrimitivePathConnectionField_hasFDerivAt_of_contDiff
          source sectionInput regular point)
  rw [coordinateDerivative.fderiv]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change
    loweredLorentzConnectionCoefficient
        (lorentzSkewConnectionOfBivectorOneForm
          (directPrimitivePathLorentzRadialFirstJet source sectionInput point
            (coordinateDirection derivativeDirection)))
        formDirection internalPair = _
  exact loweredLorentzConnectionCoefficient_ofBivectorOneForm
    (directPrimitivePathLorentzRadialFirstJet source sectionInput point
      (coordinateDirection derivativeDirection))
    formDirection internalPair

/-! ## Fixed P506/L0 readback -/

private abbrev FixedSource : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedCurrent : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

private abbrev FixedSectionInput : StageNineHolonomicConfiguration :=
  directPrimitivePathPrefix FixedSource FixedCurrent

private theorem completeJointDirectPrimitivePathOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
      source current).coframe =
      directPrimitivePathCoframeField source
        (directPrimitivePathPrefix source current) :=
  rfl

private theorem completeJointDirectPrimitivePathOperator_gravityConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointDirectPrimitivePathOperator
      source current).gravityConnection =
      directPrimitivePathConnectionField source
        (directPrimitivePathPrefix source current) := by
  change
    (installFormNativeGravityReaction
      (sourceActionGeneratedDiracDualDirectPrimitivePathWrite source
        (directPrimitivePathPrefix source current))).gravityConnection = _
  rw [installFormNativeGravityReaction_gravityConnection]
  rfl

/-- Fixed-lineage coframe readback.  The direct one-form's `C¹` premise is
kept explicit because the earlier gravity-tail profile regularity theorem
has a different recentered carrier. -/
theorem
    fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePath_coframe_hasFDerivAt_of_contDiff
    (regular : ∀ internal coordinate : LorentzianIndex,
      ContDiff ℝ 1 (fun contact =>
        directPrimitivePathCoframeJetCoordinateCLM
          FixedSource FixedSectionInput contact internal coordinate))
    (point : BasePoint) :
    HasFDerivAt
      fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual.coframe
      (directPrimitivePathCoframeRadialFirstJet
        FixedSource FixedSectionInput point)
      point := by
  rw [
    fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual_eq_actionWrite,
    completeJointDirectPrimitivePathOperator_coframe]
  exact directPrimitivePathCoframeField_hasFDerivAt_of_contDiff
    FixedSource FixedSectionInput regular point

/-- Fixed P506/L0 lowered-connection readback on the final reaction actual.
The exact direct Lorentz one-form's `C¹` premise remains explicit. -/
theorem
    fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePath_loweredConnectionFirstJet_eq_radialFirstJet
    (regular : ContDiff ℝ 1
      (directPrimitivePathLorentzJetCLM FixedSource FixedSectionInput))
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex)
    (internalPair : Fin 6) :
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual
          point derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) =
      directPrimitivePathLorentzRadialFirstJet
        FixedSource FixedSectionInput point
        (coordinateDirection derivativeDirection) formDirection internalPair := by
  unfold gravityConnectionDerivative
  rw [
    fixedP506L0ConstraintCauchyCompleteJointDirectPrimitivePathGlobalActual_eq_actionWrite,
    completeJointDirectPrimitivePathOperator_gravityConnection]
  change
    minkowskiInternalSign (pairFirst internalPair) *
        fderiv ℝ
          (fun endpoint =>
            directPrimitivePathConnectionField FixedSource FixedSectionInput endpoint
              formDirection (pairFirst internalPair) (pairSecond internalPair))
          point (coordinateDirection derivativeDirection) = _
  change
    minkowskiInternalSign (pairFirst internalPair) *
        gravityConnectionDerivative
          (sourceActionGeneratedDiracDualDirectPrimitivePathWrite
            FixedSource FixedSectionInput)
          point derivativeDirection formDirection
          (pairFirst internalPair) (pairSecond internalPair) = _
  exact
    sourceActionGeneratedDiracDualDirectPrimitivePathWrite_loweredConnectionFirstJet_eq_radialFirstJet
      FixedSource FixedSectionInput regular point derivativeDirection
      formDirection internalPair

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyCompleteJointDirectPrimitivePathRadialFirstJet

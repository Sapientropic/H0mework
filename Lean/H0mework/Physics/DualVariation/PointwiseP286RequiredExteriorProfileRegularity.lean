import H0mework.Physics.JointVariation.P286RequiredExteriorProfileNaturality
import H0mework.Physics.Matter.ChargedGaugeCurrentThreeFormRegularity

/-!
# Pointwise P286 required-profile regularity

This module localizes the charged-current regularity proof to one occurrence.
Primitive coframe, scalar, matter, conjugate-matter, connection, and auxiliary
continuity at that occurrence transport through the exact W13 charged
three-form and the direct P286 action read

```text
J_charged(source, current, contact) - [A, B](current, contact).
```

This is an action-read regularity bridge.  It constructs no field and consumes
no residual, support coordinate, response, or equation receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativePointwiseP286RequiredExteriorProfileRegularity

open ComplexConjugate
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCompleteJointActionP286RequiredExteriorProfileNaturality
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeChargedGaugeCurrentThreeFormRegularity
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

local instance pointwiseProfileRegularityP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance pointwiseProfileRegularityP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance pointwiseProfileRegularityMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

local instance pointwiseProfileRegularityP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem scalarPairing_continuousAt
    (first second : BasePoint → ScalarCoordinateCarrier)
    (point : BasePoint)
    (firstContinuous : ContinuousAt first point)
    (secondContinuous : ContinuousAt second point) :
    ContinuousAt
      (fun candidate =>
        scalarCoordinatePairingRe (first candidate) (second candidate))
      point := by
  have pairingContinuous :
      Continuous fun pair :
          ScalarCoordinateCarrier × ScalarCoordinateCarrier =>
        scalarCoordinatePairingReBilinear pair.1 pair.2 :=
    isBoundedBilinearMap_apply.continuous.comp
      ((scalarCoordinatePairingReBilinear.toContinuousBilinearMap.continuous.comp
        continuous_fst).prodMk continuous_snd)
  exact pairingContinuous.continuousAt.comp'
    (firstContinuous.prodMk secondContinuous)

private theorem pointwiseScalarVariation_continuousAt
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (scalarContinuous :
      ContinuousAt configuration.scalar point)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    ContinuousAt
      (fun candidate =>
        pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField configuration candidate)
          direction formDirection)
      point := by
  have bilinearContinuous : Continuous fun pair :
      P286CoordinateCarrier × ScalarCoordinateCarrier =>
        scalarP286ActionBilinear pair.1 pair.2 :=
    (scalarP286ActionBilinear.toContinuousBilinearMap.continuous.comp
      continuous_fst).clm_apply continuous_snd
  have actual :=
    bilinearContinuous.continuousAt.comp'
      ((continuousAt_const :
        ContinuousAt
          (fun _ : BasePoint => direction formDirection) point).prodMk
        scalarContinuous)
  change ContinuousAt
    (fun candidate =>
      scalarP286ActionBilinear (direction formDirection)
        (configuration.scalar candidate))
    point
  exact actual

private theorem pointwiseScalarChargedDensity_continuousAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeContinuous :
      ContinuousAt configuration.coframe point)
    (nondegenerate :
      Matrix.det (configuration.coframe point) ≠ 0)
    (scalarContinuous :
      ContinuousAt configuration.scalar point)
    (scalarCovariantContinuous :
      ContinuousAt
        (holonomicScalarCovariantDerivative configuration) point)
    (direction : P286GaugeOneForm) :
    ContinuousAt
      (fun candidate =>
        scalarGaugeConnectionKineticFirstVariationDensity source 0 candidate
          (toContinuumPointField configuration candidate)
          (pointwiseScalarP286GaugeConnectionVariation
            (toContinuumPointField configuration candidate) direction))
      point := by
  have metricInverseContinuous :
      ContinuousAt
        (fun candidate =>
          (lorentzianMetricOfCoframe
            (configuration.coframe candidate))⁻¹)
        point :=
    (StageNineCoframeLocalDifferentiability.lorentzianMetric_inv_contDiffAt
      (configuration.coframe point) nondegenerate).continuousAt.comp'
        coframeContinuous
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField,
    scalarFrameRelativeCoordinates_zeroChart]
  apply continuousAt_const.mul
  apply tendsto_finsetSum
  intro first _
  apply tendsto_finsetSum
  intro second _
  have metricEntryContinuous : ContinuousAt
      (fun candidate =>
        (lorentzianMetricOfCoframe
          (configuration.coframe candidate))⁻¹ first second)
      point :=
    (continuous_apply second).continuousAt.comp'
      ((continuous_apply first).continuousAt.comp'
        metricInverseContinuous)
  apply metricEntryContinuous.mul
  apply ContinuousAt.add
  · exact scalarPairing_continuousAt _ _ point
      (pointwiseScalarVariation_continuousAt configuration point
        scalarContinuous direction first)
      ((continuousAt_pi.mp scalarCovariantContinuous) second)
  · exact scalarPairing_continuousAt _ _ point
      ((continuousAt_pi.mp scalarCovariantContinuous) first)
      (pointwiseScalarVariation_continuousAt configuration point
        scalarContinuous direction second)

private theorem pointwiseMatterVariationCoordinate_continuousAt
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (matterContinuous :
      ContinuousAt
        (fun candidate =>
          matterCoordinateEquiv (configuration.matter candidate))
        point)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    ContinuousAt
      (fun candidate =>
        matterCoordinateEquiv
          (pointwiseMatterP286GaugeConnectionVariation
            (toContinuumPointField configuration candidate)
            direction formDirection))
      point := by
  have bilinearContinuous : Continuous fun pair :
      P286CoordinateCarrier × MatterCoordinateCarrier =>
        matterP286ActionCoordinateBilinear pair.1 pair.2 :=
    (matterP286ActionCoordinateBilinear.toContinuousBilinearMap.continuous.comp
      continuous_fst).clm_apply continuous_snd
  have actual :=
    bilinearContinuous.continuousAt.comp'
      ((continuousAt_const :
        ContinuousAt
          (fun _ : BasePoint => direction formDirection) point).prodMk
        matterContinuous)
  exact actual.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun candidate => by
      change
        matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed
                (p286CoordinateEquiv.symm (direction formDirection)))
              (configuration.matter candidate)) =
          matterCoordinateEquiv
            (diracExteriorMotherLieAction
              (p286LieBlockEmbed
                (p286CoordinateEquiv.symm (direction formDirection)))
              (matterCoordinateEquiv.symm
                (matterCoordinateEquiv (configuration.matter candidate))))
      rw [matterCoordinateEquiv.symm_apply_apply])

private theorem pointwiseMatterKineticSummandCoordinate_continuousAt
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeContinuous :
      ContinuousAt configuration.coframe point)
    (nondegenerate :
      Matrix.det (configuration.coframe point) ≠ 0)
    (matterContinuous :
      ContinuousAt
        (fun candidate =>
          matterCoordinateEquiv (configuration.matter candidate))
        point)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    ContinuousAt
      (fun candidate =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe candidate, derivative := 0 }
              formDirection)
            (pointwiseMatterP286GaugeConnectionVariation
              (toContinuumPointField configuration candidate)
              direction formDirection)))
      point := by
  have gammaContinuous :
      ContinuousAt
        (fun candidate =>
          inverseCoframeDiracGamma
            { coframe := configuration.coframe candidate, derivative := 0 }
            formDirection)
        point :=
    (StageNineCoframeLocalDifferentiability.inverseCoframeDiracGamma_contDiffAt
      (configuration.coframe point) nondegenerate formDirection).continuousAt
      |>.comp' coframeContinuous
  have variationContinuous :=
    pointwiseMatterVariationCoordinate_continuousAt configuration point
      matterContinuous direction formDirection
  have bilinearContinuous : Continuous fun pair :
      DiracMatrix × MatterCoordinateCarrier =>
        StageNineCoframeScalarMatterRegularity.diracMatrixMatterCoordinateRealBilinear
          pair.1 pair.2 :=
    (StageNineCoframeScalarMatterRegularity.diracMatrixMatterCoordinateRealBilinear
      |>.toContinuousBilinearMap
      |>.continuous
      |>.comp continuous_fst).clm_apply continuous_snd
  have actual :=
    bilinearContinuous.continuousAt.comp'
      (gammaContinuous.prodMk variationContinuous)
  exact actual.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun candidate => by
      change
        matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := configuration.coframe candidate,
                  derivative := 0 }
                formDirection)
              (pointwiseMatterP286GaugeConnectionVariation
                (toContinuumPointField configuration candidate)
                direction formDirection)) =
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := configuration.coframe candidate,
                  derivative := 0 }
                formDirection)
              (matterCoordinateEquiv.symm
                (matterCoordinateEquiv
                  (pointwiseMatterP286GaugeConnectionVariation
                    (toContinuumPointField configuration candidate)
                    direction formDirection))))
      rw [matterCoordinateEquiv.symm_apply_apply])

private theorem pointwiseMatterVariationVectorCoordinate_continuousAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeContinuous :
      ContinuousAt configuration.coframe point)
    (nondegenerate :
      Matrix.det (configuration.coframe point) ≠ 0)
    (matterContinuous :
      ContinuousAt
        (fun candidate =>
          matterCoordinateEquiv (configuration.matter candidate))
        point)
    (direction : P286GaugeOneForm) :
    ContinuousAt
      (fun candidate =>
        matterCoordinateEquiv
          (matterGaugeConnectionVariationVector source 0 candidate
            (toContinuumPointField configuration candidate)
            (pointwiseMatterP286GaugeConnectionVariation
              (toContinuumPointField configuration candidate) direction)))
      point := by
  have sumContinuous : ContinuousAt
      (fun candidate =>
        ∑ formDirection : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := configuration.coframe candidate, derivative := 0 }
                formDirection)
              (pointwiseMatterP286GaugeConnectionVariation
                (toContinuumPointField configuration candidate)
                direction formDirection)))
      point := by
    apply tendsto_finsetSum
    intro formDirection _
    exact
      pointwiseMatterKineticSummandCoordinate_continuousAt configuration
        point coframeContinuous nondegenerate matterContinuous direction
        formDirection
  have withIContinuous : ContinuousAt
      (fun candidate =>
        Complex.I •
          ∑ formDirection : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction
                (inverseCoframeDiracGamma
                  { coframe := configuration.coframe candidate,
                    derivative := 0 }
                  formDirection)
                (pointwiseMatterP286GaugeConnectionVariation
                  (toContinuumPointField configuration candidate)
                  direction formDirection)))
      point := by
    exact (sumContinuous.const_smul Complex.I).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)
  unfold matterGaugeConnectionVariationVector matterGaugeKineticSum
    matterDerivativeFrameRelative
  simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum,
    map_smul]
  exact withIContinuous

private theorem pointwiseMatterChargedDensity_continuousAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeContinuous :
      ContinuousAt configuration.coframe point)
    (nondegenerate :
      Matrix.det (configuration.coframe point) ≠ 0)
    (matterContinuous :
      ContinuousAt
        (fun candidate =>
          matterCoordinateEquiv (configuration.matter candidate))
        point)
    (conjugateMatterContinuous :
      ContinuousAt
        (holonomicConjugateMatterCoordinates configuration)
        point)
    (direction : P286GaugeOneForm) :
    ContinuousAt
      (fun candidate =>
        matterGaugeConnectionFirstVariationDensity source 0 candidate
          (toContinuumPointField configuration candidate)
          (pointwiseMatterP286GaugeConnectionVariation
            (toContinuumPointField configuration candidate) direction))
      point := by
  let vector := fun candidate =>
    matterGaugeConnectionVariationVector source 0 candidate
      (toContinuumPointField configuration candidate)
      (pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField configuration candidate) direction)
  have vectorContinuous : ContinuousAt
      (fun candidate => matterCoordinateEquiv (vector candidate)) point :=
    pointwiseMatterVariationVectorCoordinate_continuousAt source configuration
      point coframeContinuous nondegenerate matterContinuous direction
  have pairingContinuous : ContinuousAt
      (fun candidate =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector candidate) index *
            holonomicConjugateMatterCoordinates configuration candidate index)
      point := by
    apply tendsto_finsetSum
    intro index _
    have vectorEntryContinuous : ContinuousAt
        (fun candidate => matterCoordinateEquiv (vector candidate) index)
        point :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).continuousAt.comp'
          vectorContinuous
    exact vectorEntryContinuous.mul
      ((PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).continuousAt.comp'
          conjugateMatterContinuous)
  have realPairingContinuous :=
    Complex.continuous_re.continuousAt.comp' pairingContinuous
  unfold matterGaugeConnectionFirstVariationDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart]
  exact realPairingContinuous.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun candidate => by
      change
        (configuration.conjugateMatter candidate (vector candidate)).re =
          (∑ index : MatterCoordinateIndex,
            matterCoordinateEquiv (vector candidate) index *
              configuration.conjugateMatter candidate
                (matterCoordinateEquiv.symm
                  (EuclideanSpace.single index (1 : ℂ)))).re
      rw [← matterDual_coordinate_expansion
        (configuration.conjugateMatter candidate)
        (matterCoordinateEquiv (vector candidate))]
      simp only [matterCoordinateEquiv.symm_apply_apply])

private theorem pointwiseChargedCoefficient_continuousAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeContinuous :
      ContinuousAt configuration.coframe point)
    (nondegenerate :
      Matrix.det (configuration.coframe point) ≠ 0)
    (scalarContinuous :
      ContinuousAt configuration.scalar point)
    (scalarCovariantContinuous :
      ContinuousAt
        (holonomicScalarCovariantDerivative configuration) point)
    (matterContinuous :
      ContinuousAt
        (fun candidate =>
          matterCoordinateEquiv (configuration.matter candidate))
        point)
    (conjugateMatterContinuous :
      ContinuousAt
        (holonomicConjugateMatterCoordinates configuration)
        point)
    (direction : P286GaugeOneForm) :
    ContinuousAt
      (fun candidate =>
        formNativeChargedGaugeFirstCoefficient source 0 candidate
          (toContinuumPointField configuration candidate) direction)
      point := by
  have volumeContinuous : ContinuousAt
      (fun candidate =>
        generatedVolumeDensity
          (toContinuumPointField configuration candidate))
      point := by
    unfold generatedVolumeDensity toContinuumPointField
    exact
      (continuous_id.matrix_det.continuousAt.comp' coframeContinuous).abs
  exact volumeContinuous.mul
    ((pointwiseScalarChargedDensity_continuousAt source configuration point
      coframeContinuous nondegenerate scalarContinuous
      scalarCovariantContinuous direction).add
    (pointwiseMatterChargedDensity_continuousAt source configuration point
      coframeContinuous nondegenerate matterContinuous
      conjugateMatterContinuous direction))

/-- Local action-data regularity transports to the canonical W13 charged
three-form at the same occurrence. -/
theorem pointwiseChargedGaugeThreeForm_continuousAt_of_actionData
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeContinuous :
      ContinuousAt configuration.coframe point)
    (nondegenerate :
      Matrix.det (configuration.coframe point) ≠ 0)
    (scalarContinuous :
      ContinuousAt configuration.scalar point)
    (scalarCovariantContinuous :
      ContinuousAt
        (holonomicScalarCovariantDerivative configuration) point)
    (matterContinuous :
      ContinuousAt
        (fun candidate =>
          matterCoordinateEquiv (configuration.matter candidate))
        point)
    (conjugateMatterContinuous :
      ContinuousAt
        (holonomicConjugateMatterCoordinates configuration)
        point) :
    ContinuousAt
      (fun candidate =>
        formNativeChargedGaugeThreeForm source 0 candidate
          (toContinuumPointField configuration candidate))
      point := by
  let basis := Module.finBasis ℝ P286GaugeOneForm
  let coordinates := fun candidate =>
    basis.dualBasis.equivFun
      (formNativeChargedGaugeFirstLinearMap source 0 candidate
        (toContinuumPointField configuration candidate))
  have coordinatesContinuous : ContinuousAt coordinates point := by
    apply continuousAt_pi.mpr
    intro index
    rw [show (fun candidate => coordinates candidate index) =
      fun candidate =>
        formNativeChargedGaugeFirstCoefficient source 0 candidate
          (toContinuumPointField configuration candidate) (basis index) by
      funext candidate
      exact basis.dualBasis_equivFun _ index]
    exact pointwiseChargedCoefficient_continuousAt source configuration point
      coframeContinuous nondegenerate scalarContinuous
      scalarCovariantContinuous matterContinuous conjugateMatterContinuous
      (basis index)
  let reconstruct :=
    basis.dualBasis.equivFun.symm.trans p286GaugeThreeFormWedgeEquiv.symm
  let reconstructCLM :
      (Fin (Module.finrank ℝ P286GaugeOneForm) → ℝ) →L[ℝ]
        P286GaugeThreeForm :=
    ⟨reconstruct.toLinearMap,
      reconstruct.toLinearMap.continuous_of_finiteDimensional⟩
  have reconstructedContinuous : ContinuousAt
      (fun candidate => reconstructCLM (coordinates candidate)) point :=
    reconstructCLM.continuous.continuousAt.comp' coordinatesContinuous
  exact reconstructedContinuous.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun candidate => by
      change p286GaugeThreeFormWedgeEquiv.symm
          (formNativeChargedGaugeFirstLinearMap source 0 candidate
            (toContinuumPointField configuration candidate)) =
        reconstruct (coordinates candidate)
      unfold reconstruct coordinates
      rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply])

private theorem p286CoordinateLieBracket_apply_continuousAt
    (first second : BasePoint → P286CoordinateCarrier)
    (point : BasePoint)
    (firstContinuous : ContinuousAt first point)
    (secondContinuous : ContinuousAt second point) :
    ContinuousAt
      (fun candidate =>
        p286CoordinateLieBracket (first candidate) (second candidate))
      point := by
  change ContinuousAt
    (fun candidate =>
      p286CoordinateLieBracketBilinear
        (first candidate) (second candidate))
    point
  exact
    (p286CoordinateLieBracketBilinear.toContinuousBilinearMap.continuous
      |>.continuousAt
      |>.comp' firstContinuous).clm_apply secondContinuous

private theorem p286GaugeTwoFormAdjoint_continuousAt
    (generator : BasePoint → P286CoordinateCarrier)
    (form : BasePoint → P286GaugeTwoForm)
    (point : BasePoint)
    (generatorContinuous : ContinuousAt generator point)
    (formContinuous : ContinuousAt form point) :
    ContinuousAt
      (fun candidate =>
        p286GaugeTwoFormAdjoint (generator candidate) (form candidate))
      point := by
  apply continuousAt_pi.mpr
  intro pair
  exact
    p286CoordinateLieBracket_apply_continuousAt generator
      (fun candidate => form candidate pair) point generatorContinuous
      ((continuous_apply pair).continuousAt.comp' formContinuous)

private theorem orderedP286GaugeTwoFormComponent_continuousAt
    (form : BasePoint → P286GaugeTwoForm)
    (point : BasePoint)
    (formContinuous : ContinuousAt form point)
    (first second : LorentzianIndex) :
    ContinuousAt
      (fun candidate =>
        orderedP286GaugeTwoFormComponent
          (form candidate) first second)
      point := by
  unfold orderedP286GaugeTwoFormComponent
  apply tendsto_finsetSum
  intro pair _
  exact
    (continuousAt_const :
      ContinuousAt
        (fun _ : BasePoint =>
          (orientedLorentzBivectorBasisCoefficient pair first second : ℝ))
        point).smul
      ((continuous_apply pair).continuousAt.comp' formContinuous)

private theorem connectionExteriorAction_continuousAt
    (connection : BasePoint → P286GaugeOneForm)
    (auxiliary : BasePoint → P286GaugeTwoForm)
    (point : BasePoint)
    (connectionContinuous : ContinuousAt connection point)
    (auxiliaryContinuous : ContinuousAt auxiliary point) :
    ContinuousAt
      (fun candidate =>
        pointwiseP286GaugeTwoFormConnectionExteriorAction
          (connection candidate) (auxiliary candidate))
      point := by
  apply continuousAt_pi.mpr
  intro triple
  have adjointContinuous : ∀ direction,
      ContinuousAt
        (fun candidate =>
          p286GaugeTwoFormAdjoint
            (connection candidate direction) (auxiliary candidate))
        point := by
    intro direction
    exact
      p286GaugeTwoFormAdjoint_continuousAt
        (fun candidate => connection candidate direction) auxiliary point
        ((continuous_apply direction).continuousAt.comp'
          connectionContinuous)
        auxiliaryContinuous
  unfold pointwiseP286GaugeTwoFormConnectionExteriorAction
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative
    pointwiseP286GaugeTwoFormCovariantDerivative
  simp only [Pi.zero_apply, zero_add]
  exact
    ((orderedP286GaugeTwoFormComponent_continuousAt
      (fun candidate =>
        p286GaugeTwoFormAdjoint
          (connection candidate (threeFormFirst triple))
          (auxiliary candidate))
      point (adjointContinuous (threeFormFirst triple))
      (threeFormSecond triple) (threeFormThird triple)).add
    (orderedP286GaugeTwoFormComponent_continuousAt
      (fun candidate =>
        p286GaugeTwoFormAdjoint
          (connection candidate (threeFormSecond triple))
          (auxiliary candidate))
      point (adjointContinuous (threeFormSecond triple))
      (threeFormThird triple) (threeFormFirst triple))).add
    (orderedP286GaugeTwoFormComponent_continuousAt
      (fun candidate =>
        p286GaugeTwoFormAdjoint
          (connection candidate (threeFormThird triple))
          (auxiliary candidate))
      point (adjointContinuous (threeFormThird triple))
      (threeFormFirst triple) (threeFormSecond triple))

/-- Local regularity of the exact direct action read
`J_charged - [A,B]`.  This is a readout theorem, not a response producer. -/
theorem pointwiseDirectP286RequiredExteriorDerivative_continuousAt_of_actionData
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (coframeContinuous :
      ContinuousAt configuration.coframe point)
    (nondegenerate :
      Matrix.det (configuration.coframe point) ≠ 0)
    (connectionContinuous :
      ContinuousAt
        (holonomicP286GaugeConnectionCoordinate configuration) point)
    (auxiliaryContinuous :
      ContinuousAt
        (holonomicP286GaugeAuxiliaryCoordinate configuration) point)
    (scalarContinuous :
      ContinuousAt configuration.scalar point)
    (scalarCovariantContinuous :
      ContinuousAt
        (holonomicScalarCovariantDerivative configuration) point)
    (matterContinuous :
      ContinuousAt
        (fun candidate =>
          matterCoordinateEquiv (configuration.matter candidate))
        point)
    (conjugateMatterContinuous :
      ContinuousAt
        (holonomicConjugateMatterCoordinates configuration)
        point) :
    ContinuousAt
      (pointwiseDirectP286RequiredExteriorDerivative source configuration)
      point := by
  unfold pointwiseDirectP286RequiredExteriorDerivative
    formNativePhysicalChargedGaugeCurrentThreeForm
  exact
    (pointwiseChargedGaugeThreeForm_continuousAt_of_actionData source
      configuration point coframeContinuous nondegenerate scalarContinuous
      scalarCovariantContinuous matterContinuous
      conjugateMatterContinuous).neg.sub
      (connectionExteriorAction_continuousAt
        (holonomicP286GaugeConnectionCoordinate configuration)
        (holonomicP286GaugeAuxiliaryCoordinate configuration)
        point connectionContinuous auxiliaryContinuous)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativePointwiseP286RequiredExteriorProfileRegularity

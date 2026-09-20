import H0mework.Physics.Matter.ChargedGaugeCurrentThreeForm
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariationDensity
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Regularity of the form-native charged P286 three-form

This module proves continuity in the base point of the action-generated
charged P286 three-form.  It regenerates only the reusable scalar and Dirac
sector regularity from primitive smooth fields and the nondegenerate coframe;
no historical combined connection momentum, Euler coefficient, weak equation,
stationarity theorem, current receipt, or fixed actual is consumed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeChargedGaugeCurrentThreeFormRegularity

open ComplexConjugate
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

local instance p286ModuleFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance p286CoordinateIndexFintype : Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Fixed-direction scalar coefficient -/

theorem pointwiseScalarP286GaugeConnectionVariation_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      pointwiseScalarP286GaugeConnectionVariation
        (toContinuumPointField configuration point) direction formDirection := by
  have scalarContinuous : Continuous configuration.scalar :=
    smooth.2.2.2.2.2.2.1.continuous
  have actual := scalarP286Action_apply_continuous
    (fun _ : BasePoint => direction formDirection) configuration.scalar
    continuous_const scalarContinuous
  unfold pointwiseScalarP286GaugeConnectionVariation
    pointwiseP286GaugeConnectionMotherVariation toContinuumPointField
  change Continuous fun point =>
    scalarP286ActionBilinear (direction formDirection)
      (configuration.scalar point)
  exact actual

theorem holonomicFormNativeScalarChargedFirstDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      scalarGaugeConnectionKineticFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (pointwiseScalarP286GaugeConnectionVariation
          (toContinuumPointField configuration point) direction) := by
  have metricInverseContinuous :=
    holonomicLorentzianMetric_inv_continuous configuration smooth nondegenerate
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [toContinuumPointField, scalarFrameRelativeCoordinates_zeroChart]
  apply continuous_const.mul
  apply continuous_finsetSum
  intro first _
  apply continuous_finsetSum
  intro second _
  have metricEntryContinuous : Continuous fun point =>
      (lorentzianMetricOfCoframe (configuration.coframe point))⁻¹ first second :=
    (continuous_apply second).comp
      ((continuous_apply first).comp metricInverseContinuous)
  apply metricEntryContinuous.mul
  apply Continuous.add
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (pointwiseScalarP286GaugeConnectionVariation_continuous configuration
        smooth direction first)
      (holonomicScalarCovariantDerivative_continuous configuration smooth
        second)
  · exact scalarCoordinatePairingRe_apply_continuous _ _
      (holonomicScalarCovariantDerivative_continuous configuration smooth
        first)
      (pointwiseScalarP286GaugeConnectionVariation_continuous configuration
        smooth direction second)

/-! ## Fixed-direction Dirac coefficient -/

theorem pointwiseMatterP286GaugeConnectionVariation_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField configuration point) direction
            formDirection) := by
  have matterContinuous : Continuous fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1.continuous
  have actual := matterP286ActionCoordinate_apply_continuous
    (fun _ : BasePoint => direction formDirection)
    (fun point => matterCoordinateEquiv (configuration.matter point))
    continuous_const matterContinuous
  unfold pointwiseMatterP286GaugeConnectionVariation
    pointwiseP286GaugeConnectionMotherVariation toContinuumPointField
  exact actual.congr fun point => by
    change
      matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm (direction formDirection)))
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter point)))) =
        matterCoordinateEquiv
          (diracExteriorMotherLieAction
            (p286LieBlockEmbed
              (p286CoordinateEquiv.symm (direction formDirection)))
            (configuration.matter point))
    rw [matterCoordinateEquiv.symm_apply_apply]

theorem pointwiseMatterP286GaugeKineticSummand_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            formDirection)
          (pointwiseMatterP286GaugeConnectionVariation
            (toContinuumPointField configuration point) direction
              formDirection)) :=
  diracMatrixMatterCoordinate_raw_apply_continuous _ _
    (holonomicInverseCoframeDiracGamma_continuous configuration smooth
      nondegenerate formDirection)
    (pointwiseMatterP286GaugeConnectionVariation_coordinate_continuous
      configuration smooth direction formDirection)

theorem pointwiseMatterP286GaugeKineticSum_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (pointwiseMatterP286GaugeConnectionVariation
            (toContinuumPointField configuration point) direction)) := by
  have sumContinuous : Continuous fun point =>
      ∑ formDirection : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (pointwiseMatterP286GaugeConnectionVariation
              (toContinuumPointField configuration point) direction
                formDirection)) := by
    apply continuous_finsetSum
    intro formDirection _
    exact pointwiseMatterP286GaugeKineticSummand_coordinate_continuous
      configuration smooth nondegenerate direction formDirection
  exact sumContinuous.congr fun point => by
    unfold matterGaugeKineticSum matterDerivativeFrameRelative
    simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]

theorem pointwiseMatterP286GaugeVariationVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterGaugeConnectionVariationVector source 0 point
          (toContinuumPointField configuration point)
          (pointwiseMatterP286GaugeConnectionVariation
            (toContinuumPointField configuration point) direction)) := by
  have kineticContinuous :=
    pointwiseMatterP286GaugeKineticSum_coordinate_continuous source
      configuration smooth nondegenerate direction
  have coordinateContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterGaugeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (pointwiseMatterP286GaugeConnectionVariation
            (toContinuumPointField configuration point) direction)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticContinuous).congr fun point => rfl
  unfold matterGaugeConnectionVariationVector
  exact coordinateContinuous.congr fun point => by rw [map_smul]

theorem holonomicFormNativeMatterChargedFirstDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      matterGaugeConnectionFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (pointwiseMatterP286GaugeConnectionVariation
          (toContinuumPointField configuration point) direction) := by
  let vector := fun point =>
    matterGaugeConnectionVariationVector source 0 point
      (toContinuumPointField configuration point)
      (pointwiseMatterP286GaugeConnectionVariation
        (toContinuumPointField configuration point) direction)
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    pointwiseMatterP286GaugeVariationVector_coordinate_continuous source
      configuration smooth nondegenerate direction
  have dualCoefficientContinuous : ∀ index : MatterCoordinateIndex,
      Continuous fun point =>
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) :=
    fun index => smooth.2.2.2.2.2.2.2.2 index |>.continuous
  have pairingContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply continuous_finsetSum
    intro index _
    have vectorCoefficientContinuous : Continuous fun point =>
        matterCoordinateEquiv (vector point) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp
          vectorCoordinateContinuous
    exact vectorCoefficientContinuous.mul (dualCoefficientContinuous index)
  have realPairingContinuous := Complex.continuous_re.comp pairingContinuous
  unfold matterGaugeConnectionFirstVariationDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart]
  exact realPairingContinuous.congr fun point => by
    simp only [Function.comp_apply]
    rw [← matterDual_coordinate_expansion
      (configuration.conjugateMatter point)
      (matterCoordinateEquiv (vector point))]
    simp only [matterCoordinateEquiv.symm_apply_apply]
    rfl

/-! ## Charged covector and three-form regularity -/

theorem holonomicFormNativeChargedGaugeFirstCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : P286GaugeOneForm) :
    Continuous fun point =>
      formNativeChargedGaugeFirstCoefficient source 0 point
        (toContinuumPointField configuration point) direction := by
  have coframeContinuous : Continuous configuration.coframe := by
    apply continuous_pi
    intro row
    apply continuous_pi
    intro column
    exact (smooth.1 row column).continuous
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) := by
    unfold generatedVolumeDensity toContinuumPointField
    exact coframeContinuous.matrix_det.abs
  exact volumeContinuous.mul
    ((holonomicFormNativeScalarChargedFirstDensity_continuous source
      configuration smooth nondegenerate direction).add
    (holonomicFormNativeMatterChargedFirstDensity_continuous source
      configuration smooth nondegenerate direction))

/-- The unique action-signed charged three-form varies continuously on the
same actual holonomic fields. -/
theorem holonomicFormNativeChargedGaugeThreeForm_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point =>
      formNativeChargedGaugeThreeForm source 0 point
        (toContinuumPointField configuration point) := by
  let basis := Module.finBasis ℝ P286GaugeOneForm
  let coordinates := fun point =>
    basis.dualBasis.equivFun
      (formNativeChargedGaugeFirstLinearMap source 0 point
        (toContinuumPointField configuration point))
  have coordinatesContinuous : Continuous coordinates := by
    apply continuous_pi
    intro index
    rw [show (fun point => coordinates point index) =
      fun point =>
        formNativeChargedGaugeFirstCoefficient source 0 point
          (toContinuumPointField configuration point) (basis index) by
      funext point
      exact basis.dualBasis_equivFun _ index]
    exact holonomicFormNativeChargedGaugeFirstCoefficient_continuous source
      configuration smooth nondegenerate (basis index)
  let reconstruct :=
    basis.dualBasis.equivFun.symm.trans p286GaugeThreeFormWedgeEquiv.symm
  let reconstructCLM :
      (Fin (Module.finrank ℝ P286GaugeOneForm) → ℝ) →L[ℝ]
        P286GaugeThreeForm :=
    ⟨reconstruct.toLinearMap,
      reconstruct.toLinearMap.continuous_of_finiteDimensional⟩
  have reconstructedContinuous : Continuous fun point =>
      reconstructCLM (coordinates point) :=
    reconstructCLM.continuous.comp coordinatesContinuous
  exact reconstructedContinuous.congr fun point => by
    change reconstruct (coordinates point) =
      p286GaugeThreeFormWedgeEquiv.symm
        (formNativeChargedGaugeFirstLinearMap source 0 point
          (toContinuumPointField configuration point))
    unfold reconstruct coordinates
    rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeChargedGaugeCurrentThreeFormRegularity

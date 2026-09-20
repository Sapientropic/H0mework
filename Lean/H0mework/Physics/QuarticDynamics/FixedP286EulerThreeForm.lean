import H0mework.Physics.QuarticDynamics.FixedConstitutiveRegularity
import H0mework.Physics.ActionForcing.FixedMotherActionChargeScalarPairing
import H0mework.Physics.ActionForcing.FixedOccurrenceP286AllPointActionNormalForm

/-!
# Fixed U6 radial-quartic P286 Euler three-form

Compute the temporal faithful `(123)` / hypercharge read of the P286 Euler
three-form on the same radial-quartic constitutive actual.  The two summands
below keep the complete `D_A B` read and the changed charged-current read
separate.  The construction accepts no residual, correction, target, or
successor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticP286EulerThreeForm

open ProofFreeRicherAnholonomicSource
open StageNineConnectionSectorSourceBalance
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentFixedP506P286Compatibility
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalP286Verdict
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506P286RadialRequiredExteriorAnchor
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualP286AuxiliaryFirstJet
open StageNineDiracDualFormNativeFixedP506P286CanonicalGeneratedActualZeroSliceCoframe
open StageNineDiracDualFormNativeFixedP506P286CanonicalJointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286AllPointActionNormalForm
open StageNineDiracDualFormNativeFixedP506U6MotherActionChargeScalarPairing
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveRegularity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionActionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286RadialQuarticActionPrincipal
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP506CanonicalLorentzAdjointTemporalFirstGermSupport
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceGeneratedP286AffineConnectionGerm
open StageNineTopologicalP286GaugeThreeFormDuality
open StageNineTopologicalLorentzThreeFormDuality
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance radialEulerProbeP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance radialEulerProbeP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance radialEulerProbeP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Actual : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticConstitutiveActual

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source FixedInput

private abbrev Canonical : StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalGeneratedActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev Charge : P286CoordinateCarrier :=
  fixedP506L0U6OccurrenceP286MotherActionCharge

private def SpatialE0 : StageNineSpatialPoint :=
  EuclideanSpace.single 0 1

private abbrev Point : BasePoint :=
  canonicalCauchySlicePoint 0 SpatialE0

def hyperchargeCoordinate : P286CoordinateCarrier :=
  p286CoordinateEquiv (0, 0, hyperchargeGenerator)

/-- Complete new-`B` covariant-derivative contribution in faithful `e0`
orientation, before adding the charged-current term. -/
def radialQuarticCovariant123HyperchargeRead
    (space : StageNineSpatialPoint) : ℝ :=
  p286CoordinateLiePairing hyperchargeCoordinate
    (holonomicP286GaugeAuxiliaryExteriorCovariantDerivative Actual
      (canonicalCauchySlicePoint 0 space) 3)

/-- Changed scalar/matter charged-current contribution for the same new `A`. -/
def radialQuarticCharged123HyperchargeRead
    (space : StageNineSpatialPoint) : ℝ :=
  p286CoordinateLiePairing hyperchargeCoordinate
    (formNativeChargedGaugeThreeForm Source 0
      (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField Actual
        (canonicalCauchySlicePoint 0 space)) 3)

def algebraicCharged123HyperchargeRead
    (space : StageNineSpatialPoint) : ℝ :=
  p286CoordinateLiePairing hyperchargeCoordinate
    (formNativeChargedGaugeThreeForm Source 0
      (canonicalCauchySlicePoint 0 space)
      (toContinuumPointField Algebraic
        (canonicalCauchySlicePoint 0 space)) 3)

/-- Same-actual Euler read; definitionally the sum of the two authoritative
action terms, with no reconstructed correction field. -/
def radialQuarticEuler123HyperchargeRead
    (space : StageNineSpatialPoint) : ℝ :=
  p286CoordinateLiePairing hyperchargeCoordinate
    (holonomicFormNativeP286GaugeEulerThreeForm Source 0 Actual
      (canonicalCauchySlicePoint 0 space) 3)

/-! ## Primitive charged-action data -/

private theorem u6_scalar_eq_algebraic :
    U6.scalar = Algebraic.scalar := by
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
      Source U5).trans
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_eq_preEC.trans
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
          Source FixedInput))

private theorem u6_matter_eq_algebraic :
    U6.matter = Algebraic.matter := by
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_matter_eq_current
      Source U5).trans
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_matter_eq_preEC.trans
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter
          Source FixedInput))

private theorem u6_conjugateMatter_eq_algebraic :
    U6.conjugateMatter = Algebraic.conjugateMatter := by
  exact
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_conjugateMatter_eq_current
      Source U5).trans
      (fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_conjugateMatter_eq_preEC.trans
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter
          Source FixedInput))

private theorem actual_scalar_eq_algebraic :
    Actual.scalar = Algebraic.scalar := by
  exact u6_scalar_eq_algebraic

private theorem actual_coframe_eq_algebraic :
    Actual.coframe = Algebraic.coframe := by
  exact fixedP506L0U6_coframe_eq_algebraic

private theorem actual_matter_eq_algebraic :
    Actual.matter = Algebraic.matter := by
  exact u6_matter_eq_algebraic

private theorem actual_conjugateMatter_eq_algebraic :
    Actual.conjugateMatter = Algebraic.conjugateMatter := by
  exact u6_conjugateMatter_eq_algebraic

private theorem algebraic_scalar_eq_temporal :
    Algebraic.scalar = Temporal.scalar := by
  rfl

private theorem input_scalar_vacuum :
    FixedInput.scalar = fun _ => sourceGeneratedVacuumCoordinates Source := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]

private theorem algebraic_scalar_e0_eq_vacuum :
    Algebraic.scalar Point = sourceGeneratedVacuumCoordinates Source := by
  rw [congrFun algebraic_scalar_eq_temporal Point]
  calc
    Temporal.scalar Point = FixedInput.scalar Point := by
      exact
        sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
          Source FixedInput SpatialE0
    _ = sourceGeneratedVacuumCoordinates Source := by
      rw [congrFun input_scalar_vacuum Point]

private theorem actual_gaugeConnection_eq_algebraic_add_radial
    (point : BasePoint) (direction : LorentzianIndex) :
    Actual.gaugeConnection point direction =
      Algebraic.gaugeConnection point direction +
        p286CoordinateEquiv.symm
          (p286RadialQuarticTemporalConnection Charge point direction) := by
  have varied := congrFun
    (holonomicP286GaugeConnectionCoordinate_vary U6
      (p286RadialQuarticTemporalConnection Charge) 1 point) direction
  change
    p286CoordinateEquiv (Actual.gaugeConnection point direction) = _ at varied
  simp only [Pi.add_apply, one_smul] at varied
  unfold holonomicP286GaugeConnectionCoordinate at varied
  rw [fixedP506L0U6_gaugeConnection_eq_algebraic] at varied
  apply p286CoordinateEquiv.injective
  rw [map_add, p286CoordinateEquiv.apply_symm_apply]
  exact varied

def radialQuarticScalarCovariantIncrement
    (point : BasePoint) : LorentzianIndex → ScalarCoordinateCarrier :=
  fun direction =>
    scalarMotherLieAction
      (p286LieBlockEmbed
        (p286CoordinateEquiv.symm
          (p286RadialQuarticTemporalConnection Charge point direction)))
      (Algebraic.scalar point)

private theorem actual_scalarCovariantDerivative_eq_algebraic_add_radial
    (point : BasePoint) :
    holonomicScalarCovariantDerivative Actual point =
      holonomicScalarCovariantDerivative Algebraic point +
        radialQuarticScalarCovariantIncrement point := by
  funext direction
  unfold holonomicScalarCovariantDerivative
  rw [actual_scalar_eq_algebraic,
    actual_gaugeConnection_eq_algebraic_add_radial point direction,
    p286LieBlockEmbed_add, scalarMotherLieAction_add]
  simp only [Pi.add_apply, radialQuarticScalarCovariantIncrement]
  module

private theorem radialQuarticScalarCovariantIncrement_e0 :
    radialQuarticScalarCovariantIncrement Point =
      fun direction =>
        if direction = 0 then
          (1 / 40 : ℝ) •
            scalarP286ActionBilinear Charge
              (sourceGeneratedVacuumCoordinates Source)
        else 0 := by
  funext direction
  unfold radialQuarticScalarCovariantIncrement
  rw [algebraic_scalar_e0_eq_vacuum]
  change
    scalarP286ActionBilinear
        (p286RadialQuarticTemporalConnection Charge Point direction)
        (sourceGeneratedVacuumCoordinates Source) = _
  fin_cases direction <;>
    simp [p286RadialQuarticTemporalConnection,
      p286SpatialRadialQuarticCoefficient, p286SpatialRadiusSquared,
      p286SpatialMetricCovectorOperator, p286TemporalGaugeOneForm,
      Point, SpatialE0, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, p286BaseCoordinate_apply,
      Fin.sum_univ_three]

private theorem algebraic_temporalHypercharge_scalarVariation_e0 :
    holonomicScalarGaugeConnectionVariation Algebraic
        (fun _ => p286TemporalGaugeOneForm hyperchargeCoordinate) Point =
      fun direction =>
        if direction = 0 then
          scalarP286ActionBilinear hyperchargeCoordinate
            (sourceGeneratedVacuumCoordinates Source)
        else 0 := by
  funext direction
  unfold holonomicScalarGaugeConnectionVariation
    p286GaugeConnectionMotherVariation
  rw [algebraic_scalar_e0_eq_vacuum]
  change
    scalarP286ActionBilinear
        (p286TemporalGaugeOneForm hyperchargeCoordinate direction)
        (sourceGeneratedVacuumCoordinates Source) = _
  fin_cases direction <;>
    simp [p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection]

private theorem scalarCoordinatePairingRe_comm_local
    (first second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first second =
      scalarCoordinatePairingRe second first := by
  unfold scalarCoordinatePairingRe
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re, mul_comm]

private theorem scalarCoordinatePairingRe_zero_left_local
    (second : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe 0 second = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem scalarCoordinatePairingRe_zero_right_local
    (first : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe first 0 = 0 := by
  simp [scalarCoordinatePairingRe]

private theorem motherActionCharge_eq_actionNormalForm :
    Charge = fixedP506L0AlgebraicP286EulerTripleActionNormalForm Point 3 := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic Point 3 = _
  apply fixedP506L0_Algebraic_p286Euler_apply_actionNormalForm
  change Matrix.det (Canonical.coframe Point) ≠ 0
  exact
    fixedP506L0P286CanonicalGeneratedActual_coframe_nondegenerate_zeroSlice
      SpatialE0

/-- Point field carrying exactly the changed scalar covariant-derivative
slot generated by the radial connection increment.  All coefficient fields
are the unchanged algebraic action data. -/
def radialQuarticScalarConnectionChangedPointField
    (point : BasePoint) : StageNineContinuumPointField :=
  { toContinuumPointField Algebraic point with
    scalarCovariantDerivative := radialQuarticScalarCovariantIncrement point }

/-- Scalar connection-action covector generated by the radial increment.
The Dirac current has no connection-dependent point-field slot. -/
def radialQuarticScalarConnectionChangedCoefficient
    (point : BasePoint) (direction : P286GaugeOneForm) : ℝ :=
  generatedVolumeDensity (toContinuumPointField Algebraic point) *
    scalarGaugeConnectionKineticFirstVariationDensity Source 0 point
      (radialQuarticScalarConnectionChangedPointField point)
      (holonomicScalarGaugeConnectionVariation Algebraic
        (fun _ => direction) point)

private theorem radialQuarticScalarConnectionChangedCoefficient_e0_eq_pairing :
    radialQuarticScalarConnectionChangedCoefficient Point
        (p286TemporalGaugeOneForm hyperchargeCoordinate) =
      -(1 / 40 : ℝ) *
        scalarCoordinatePairingRe
          (scalarP286ActionBilinear hyperchargeCoordinate
            (sourceGeneratedVacuumCoordinates Source))
          (scalarP286ActionBilinear Charge
            (sourceGeneratedVacuumCoordinates Source)) := by
  unfold radialQuarticScalarConnectionChangedCoefficient
    radialQuarticScalarConnectionChangedPointField
  rw [algebraic_temporalHypercharge_scalarVariation_e0,
    radialQuarticScalarCovariantIncrement_e0]
  unfold generatedVolumeDensity
  simp only [toContinuumPointField]
  rw [fixedP506L0Algebraic_coframe_zeroSlice]
  simp only [Matrix.det_one, abs_one, one_mul]
  unfold scalarGaugeConnectionKineticFirstVariationDensity
    scalarFrameRelativeCovariantDerivative
  simp only [scalarFrameRelativeCoordinates_zeroChart]
  rw [
    StageNinePositiveSourceNativeGravityCurvatureBridge.lorentzianMetricOfCoframe_one_inv]
  simp [Fin.sum_univ_four, minkowskiInternalMetric, Matrix.diagonal_apply,
    scalarCoordinatePairingRe_zero_right_local,
    scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  rw [scalarCoordinatePairingRe_comm_local
    (scalarP286ActionBilinear Charge
      (sourceGeneratedVacuumCoordinates Source))
    (scalarP286ActionBilinear hyperchargeCoordinate
      (sourceGeneratedVacuumCoordinates Source))]
  ring

private theorem
    scalarGaugeConnectionKineticFirstVariationDensity_add_background
    (source : SmoothUnifiedSource) (chart : StageNineChart)
    (point : BasePoint) (field : StageNineContinuumPointField)
    (increment variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity source chart point
        { field with
          scalarCovariantDerivative :=
            field.scalarCovariantDerivative + increment }
        variation =
      scalarGaugeConnectionKineticFirstVariationDensity source chart point
          field variation +
        scalarGaugeConnectionKineticFirstVariationDensity source chart point
          { field with scalarCovariantDerivative := increment } variation := by
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  simp only [scalarFrameRelativeCovariantDerivative_add, Pi.add_apply,
    scalarCoordinatePairingRe_add_left,
    scalarCoordinatePairingRe_add_right]
  rw [← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro second _
  ring

private theorem actual_matterCurrent_eq_algebraic
    (point : BasePoint) (direction : P286GaugeOneForm) :
    p286MatterCurrentCoefficient Source Actual direction point =
      p286MatterCurrentCoefficient Source Algebraic direction point := by
  unfold p286MatterCurrentCoefficient generatedVolumeDensity
    matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
    holonomicMatterGaugeConnectionVariation
  simp only [toContinuumPointField]
  rw [congrFun actual_coframe_eq_algebraic point,
    congrFun actual_matter_eq_algebraic point,
    congrFun actual_conjugateMatter_eq_algebraic point]

private theorem actual_scalarCurrent_eq_algebraic_add_radialChanged
    (point : BasePoint) (direction : P286GaugeOneForm) :
    p286ScalarCurrentCoefficient Source Actual direction point =
      p286ScalarCurrentCoefficient Source Algebraic direction point +
        radialQuarticScalarConnectionChangedCoefficient point direction := by
  have volumeEq :
      generatedVolumeDensity (toContinuumPointField Actual point) =
        generatedVolumeDensity (toContinuumPointField Algebraic point) := by
    unfold generatedVolumeDensity
    simp only [toContinuumPointField]
    rw [congrFun actual_coframe_eq_algebraic point]
  have variationEq :
      holonomicScalarGaugeConnectionVariation Actual
          (fun _ => direction) point =
        holonomicScalarGaugeConnectionVariation Algebraic
          (fun _ => direction) point := by
    funext derivativeDirection
    unfold holonomicScalarGaugeConnectionVariation
    rw [congrFun actual_scalar_eq_algebraic point]
  have kineticEq :
      scalarGaugeConnectionKineticFirstVariationDensity Source 0 point
          (toContinuumPointField Actual point)
          (holonomicScalarGaugeConnectionVariation Algebraic
            (fun _ => direction) point) =
        scalarGaugeConnectionKineticFirstVariationDensity Source 0 point
            { toContinuumPointField Algebraic point with
              scalarCovariantDerivative :=
                (toContinuumPointField Algebraic point).scalarCovariantDerivative +
                  radialQuarticScalarCovariantIncrement point }
            (holonomicScalarGaugeConnectionVariation Algebraic
              (fun _ => direction) point) := by
    unfold scalarGaugeConnectionKineticFirstVariationDensity
    simp only [toContinuumPointField]
    rw [congrFun actual_coframe_eq_algebraic point,
      actual_scalarCovariantDerivative_eq_algebraic_add_radial point]
  unfold p286ScalarCurrentCoefficient
    radialQuarticScalarConnectionChangedCoefficient
    radialQuarticScalarConnectionChangedPointField
  rw [volumeEq, variationEq, kineticEq,
    scalarGaugeConnectionKineticFirstVariationDensity_add_background]
  ring

private theorem formNativeChargedGaugeFirstCoefficient_eq_currentSectors
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (direction : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient Source 0 point
        (toContinuumPointField configuration point) direction =
      p286ScalarCurrentCoefficient Source configuration direction point +
        p286MatterCurrentCoefficient Source configuration direction point := by
  unfold formNativeChargedGaugeFirstCoefficient
    p286ScalarCurrentCoefficient p286MatterCurrentCoefficient
  rw [pointwiseScalarP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point,
    pointwiseMatterP286GaugeConnectionVariation_actual configuration
      (fun _ => direction) point]
  rw [mul_add]

private theorem chargedGaugeFirstCoefficient_sub_eq_radialScalarChanged
    (point : BasePoint) (direction : P286GaugeOneForm) :
    formNativeChargedGaugeFirstCoefficient Source 0 point
          (toContinuumPointField Actual point) direction -
        formNativeChargedGaugeFirstCoefficient Source 0 point
          (toContinuumPointField Algebraic point) direction =
      radialQuarticScalarConnectionChangedCoefficient point direction := by
  rw [formNativeChargedGaugeFirstCoefficient_eq_currentSectors,
    formNativeChargedGaugeFirstCoefficient_eq_currentSectors,
    actual_scalarCurrent_eq_algebraic_add_radialChanged,
    actual_matterCurrent_eq_algebraic]
  ring

private theorem p286TemporalGaugeOneForm_wedge_reads_spatial123
    (coordinate : P286CoordinateCarrier)
    (threeForm : P286GaugeThreeForm) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (p286TemporalGaugeOneForm coordinate) threeForm =
      p286CoordinateLiePairing coordinate (threeForm 3) := by
  classical
  unfold p286GaugeOneFormThreeFormWedgeCoefficient
    p286TemporalGaugeOneForm canonicalLorentzianTimeDirection
    oneWedgeThreeSign missingTripleOfOneForm
  simp [Fin.sum_univ_four]

/-! ## Whole-zero-slice spatial auxiliary jet transport -/

private theorem algebraic_auxiliaryCoordinate_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate Algebraic)
      (canonicalCauchySlicePoint 0 space) := by
  have coordinateEq :
      holonomicP286GaugeAuxiliaryCoordinate Algebraic =
        holonomicP286GaugeAuxiliaryCoordinate Canonical := by
    simpa [Algebraic, Canonical, Source] using
      fixedP506L0CompleteJointGlobalP286AlgebraicCurrent_auxiliaryCoordinate_eq_canonical
  rw [coordinateEq]
  apply
    fixedP506L0P286CanonicalGeneratedActual_gaugeAuxiliaryCoordinate_differentiableAt
  change
    Matrix.det
      (Canonical.coframe (canonicalCauchySlicePoint 0 space)) ≠ 0
  exact
    fixedP506L0P286CanonicalGeneratedActual_coframe_nondegenerate_zeroSlice
      space

private theorem anchor_auxiliaryCoordinate_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      (holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual)
      (canonicalCauchySlicePoint 0 space) := by
  rw [show
    holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual =
      fun point =>
        holonomicP286GaugeAuxiliaryCoordinate Algebraic point -
          fixedP506L0P286RadialEulerAuxiliaryProfile point by
    funext point
    exact
      fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_auxiliaryCoordinate
        point]
  exact
    (algebraic_auxiliaryCoordinate_differentiableAt_zeroSlice space).sub
      ((fixedP506L0P286RadialEulerAuxiliaryProfile_contDiff.differentiable
        (by simp)).differentiableAt)

private theorem actual_auxiliaryDirectionalDerivative_spatial_eq_anchor
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    p286GaugeAuxiliaryDirectionalDerivative Actual
        (canonicalCauchySlicePoint 0 space) axis.succ =
      p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  have restrictedEq :
      (holonomicP286GaugeAuxiliaryCoordinate Actual) ∘
          canonicalCauchySlicePoint 0 =
        (holonomicP286GaugeAuxiliaryCoordinate
            fixedP506L0P286RequiredExteriorZeroSliceAnchorActual) ∘
          canonicalCauchySlicePoint 0 := by
    funext candidate
    exact
      fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_eq_requiredExteriorAnchor_zeroSlice
        candidate
  unfold p286GaugeAuxiliaryDirectionalDerivative
  calc
    fieldDirectionalDerivative
          (holonomicP286GaugeAuxiliaryCoordinate Actual)
          (canonicalCauchySlicePoint 0 space) axis.succ =
        fderiv ℝ
            ((holonomicP286GaugeAuxiliaryCoordinate Actual) ∘
              canonicalCauchySlicePoint 0)
            space (canonicalSpatialCoordinateDirection axis) :=
      (fderiv_canonicalCauchySlicePoint_spatial_local
        (holonomicP286GaugeAuxiliaryCoordinate Actual) 0 space axis
        (fixedP506L0U6RadialQuarticConstitutiveActual_auxiliaryCoordinate_differentiableAt_zeroSlice
          space)).symm
    _ = fderiv ℝ
            ((holonomicP286GaugeAuxiliaryCoordinate
                fixedP506L0P286RequiredExteriorZeroSliceAnchorActual) ∘
              canonicalCauchySlicePoint 0)
            space (canonicalSpatialCoordinateDirection axis) := by
      rw [restrictedEq]
    _ = fieldDirectionalDerivative
          (holonomicP286GaugeAuxiliaryCoordinate
            fixedP506L0P286RequiredExteriorZeroSliceAnchorActual)
          (canonicalCauchySlicePoint 0 space) axis.succ :=
      fderiv_canonicalCauchySlicePoint_spatial_local
        (holonomicP286GaugeAuxiliaryCoordinate
          fixedP506L0P286RequiredExteriorZeroSliceAnchorActual)
        0 space axis
        (anchor_auxiliaryCoordinate_differentiableAt_zeroSlice space)

private theorem actual_exteriorDerivative_123_eq_anchor
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative Actual
        (canonicalCauchySlicePoint 0 space) 3 =
      holonomicP286GaugeAuxiliaryExteriorDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) 3 := by
  have directionOne :=
    actual_auxiliaryDirectionalDerivative_spatial_eq_anchor space 0
  have directionTwo :=
    actual_auxiliaryDirectionalDerivative_spatial_eq_anchor space 1
  have directionThree :=
    actual_auxiliaryDirectionalDerivative_spatial_eq_anchor space 2
  change
    p286GaugeAuxiliaryDirectionalDerivative Actual
        (canonicalCauchySlicePoint 0 space) 1 =
      p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) 1 at directionOne
  change
    p286GaugeAuxiliaryDirectionalDerivative Actual
        (canonicalCauchySlicePoint 0 space) 2 =
      p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) 2 at directionTwo
  change
    p286GaugeAuxiliaryDirectionalDerivative Actual
        (canonicalCauchySlicePoint 0 space) 3 =
      p286GaugeAuxiliaryDirectionalDerivative
        fixedP506L0P286RequiredExteriorZeroSliceAnchorActual
        (canonicalCauchySlicePoint 0 space) 3 at directionThree
  unfold holonomicP286GaugeAuxiliaryExteriorDerivative
    pointwiseP286GaugeTwoFormExteriorDerivativeOfDerivative
  rw [show threeFormFirst 3 = 1 by rfl,
    show threeFormSecond 3 = 2 by rfl,
    show threeFormThird 3 = 3 by rfl]
  rw [directionOne, directionTwo, directionThree]

private theorem actual_exteriorDerivative_123_eq_algebraic_sub_euler
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryExteriorDerivative Actual
        (canonicalCauchySlicePoint 0 space) 3 =
      holonomicP286GaugeAuxiliaryExteriorDerivative Algebraic
          (canonicalCauchySlicePoint 0 space) 3 -
        holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
          (canonicalCauchySlicePoint 0 space) 3 := by
  rw [actual_exteriorDerivative_123_eq_anchor]
  rw [congrFun
    (fixedP506L0P286RequiredExteriorZeroSliceAnchorActual_exteriorDerivative_eq_directRequired
      space) 3]
  exact congrFun
    (pointwiseDirectP286RequiredExteriorDerivative_eq_exterior_sub_euler
      Source Algebraic (canonicalCauchySlicePoint 0 space)) 3

/-! ## Spatial connection-action support -/

private theorem u6_gaugeConnectionCoordinate_zeroSlice_spatial
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    holonomicP286GaugeConnectionCoordinate U6
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  rw [fixedP506L0U6_gaugeConnectionCoordinate_normalForm]
  have line :=
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_coordinate_line
      (-(canonicalCauchySlicePoint 0 space)) axis.succ
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm]
      at line
  unfold fixedP506FormNativeJointActionSolvedConnectionNormalForm
  simp only [Pi.neg_apply, line]
  fin_cases axis <;>
    simp [c3h181FullConnectionCoefficient, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection]

private theorem actual_gaugeConnectionCoordinate_zeroSlice_spatial
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    holonomicP286GaugeConnectionCoordinate Actual
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  change
    holonomicP286GaugeConnectionCoordinate
        fixedP506L0U6RadialQuarticConnectionActual
        (canonicalCauchySlicePoint 0 space) axis.succ = 0
  have varied := congrFun
    (holonomicP286GaugeConnectionCoordinate_vary U6
      (p286RadialQuarticTemporalConnection Charge) 1
      (canonicalCauchySlicePoint 0 space)) axis.succ
  simp only [Pi.add_apply, one_smul] at varied
  rw [u6_gaugeConnectionCoordinate_zeroSlice_spatial space axis] at varied
  simpa [fixedP506L0U6RadialQuarticConnectionActual,
    p286RadialQuarticTemporalConnection, p286TemporalGaugeOneForm,
    canonicalLorentzianTimeDirection] using varied

private theorem algebraic_gaugeConnectionCoordinate_zeroSlice_spatial
    (space : StageNineSpatialPoint) (axis : Fin 3) :
    holonomicP286GaugeConnectionCoordinate Algebraic
        (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [← fixedP506L0U6_gaugeConnection_eq_algebraic]
  exact u6_gaugeConnectionCoordinate_zeroSlice_spatial space axis

private theorem
    pointwiseP286GaugeTwoFormConnectionExteriorAction_123_eq_zero_of_spatial_zero
    (connection : P286GaugeOneForm) (value : P286GaugeTwoForm)
    (spatialOne : connection 1 = 0)
    (spatialTwo : connection 2 = 0)
    (spatialThree : connection 3 = 0) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction connection value 3 = 0 := by
  simp [pointwiseP286GaugeTwoFormConnectionExteriorAction,
    pointwiseP286GaugeTwoFormExteriorCovariantDerivative,
    pointwiseP286GaugeTwoFormCovariantDerivative,
    p286GaugeTwoFormAdjoint, threeFormFirst, threeFormSecond,
    threeFormThird, spatialOne, spatialTwo, spatialThree,
    StageNineP286GaugeConnectionVariationDensity.p286CoordinateLieBracket_zero_left]

private theorem actual_connectionExteriorAction_123_zero
    (space : StageNineSpatialPoint) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate Actual
          (canonicalCauchySlicePoint 0 space))
        (holonomicP286GaugeAuxiliaryCoordinate Actual
          (canonicalCauchySlicePoint 0 space)) 3 = 0 := by
  apply
    pointwiseP286GaugeTwoFormConnectionExteriorAction_123_eq_zero_of_spatial_zero
  · exact actual_gaugeConnectionCoordinate_zeroSlice_spatial space 0
  · exact actual_gaugeConnectionCoordinate_zeroSlice_spatial space 1
  · exact actual_gaugeConnectionCoordinate_zeroSlice_spatial space 2

private theorem algebraic_connectionExteriorAction_123_zero
    (space : StageNineSpatialPoint) :
    pointwiseP286GaugeTwoFormConnectionExteriorAction
        (holonomicP286GaugeConnectionCoordinate Algebraic
          (canonicalCauchySlicePoint 0 space))
        (holonomicP286GaugeAuxiliaryCoordinate Algebraic
          (canonicalCauchySlicePoint 0 space)) 3 = 0 := by
  apply
    pointwiseP286GaugeTwoFormConnectionExteriorAction_123_eq_zero_of_spatial_zero
  · exact algebraic_gaugeConnectionCoordinate_zeroSlice_spatial space 0
  · exact algebraic_gaugeConnectionCoordinate_zeroSlice_spatial space 1
  · exact algebraic_gaugeConnectionCoordinate_zeroSlice_spatial space 2

private theorem euler123_eq_charged_sub_of_exteriorDerivative_eq
    (space : StageNineSpatialPoint)
    (exteriorDerivativeEq :
      holonomicP286GaugeAuxiliaryExteriorDerivative Actual
          (canonicalCauchySlicePoint 0 space) 3 =
        holonomicP286GaugeAuxiliaryExteriorDerivative Algebraic
            (canonicalCauchySlicePoint 0 space) 3 -
          holonomicFormNativeP286GaugeEulerThreeForm Source 0 Algebraic
            (canonicalCauchySlicePoint 0 space) 3) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Actual
        (canonicalCauchySlicePoint 0 space) 3 =
      formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Actual
            (canonicalCauchySlicePoint 0 space)) 3 -
        formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Algebraic
            (canonicalCauchySlicePoint 0 space)) 3 := by
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
  simp only [Pi.add_apply]
  rw [actual_connectionExteriorAction_123_zero, add_zero, exteriorDerivativeEq]
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [holonomicP286GaugeAuxiliaryExteriorCovariantDerivative_eq_parts]
  simp only [Pi.add_apply]
  rw [algebraic_connectionExteriorAction_123_zero, add_zero]
  module

/-- Exact post-anchor reduction on the whole canonical zero slice.  The new
Euler `(123)` component is precisely the changed charged-current read. -/
theorem fixedP506L0U6RadialQuarticConstitutiveActual_euler123_eq_charged_sub_algebraic
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0 Actual
        (canonicalCauchySlicePoint 0 space) 3 =
      formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Actual
            (canonicalCauchySlicePoint 0 space)) 3 -
        formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Algebraic
            (canonicalCauchySlicePoint 0 space)) 3 := by
  exact euler123_eq_charged_sub_of_exteriorDerivative_eq space
    (actual_exteriorDerivative_123_eq_algebraic_sub_euler space)

theorem radialQuarticEuler123HyperchargeRead_eq_charged_difference
    (space : StageNineSpatialPoint) :
    radialQuarticEuler123HyperchargeRead space =
      radialQuarticCharged123HyperchargeRead space -
        algebraicCharged123HyperchargeRead space := by
  unfold radialQuarticEuler123HyperchargeRead
    radialQuarticCharged123HyperchargeRead
    algebraicCharged123HyperchargeRead
  rw [fixedP506L0U6RadialQuarticConstitutiveActual_euler123_eq_charged_sub_algebraic]
  change p286CoordinateLiePairingBilinear hyperchargeCoordinate (_ - _) = _
  rw [map_sub]
  rfl

/-- Faithful changed read with the Dirac sector cancelled: only the scalar
kinetic bilinear generated by the literal radial connection increment
remains. -/
theorem radialQuarticEuler123HyperchargeRead_eq_radialScalarChanged
    (space : StageNineSpatialPoint) :
    radialQuarticEuler123HyperchargeRead space =
      radialQuarticScalarConnectionChangedCoefficient
        (canonicalCauchySlicePoint 0 space)
        (p286TemporalGaugeOneForm hyperchargeCoordinate) := by
  rw [radialQuarticEuler123HyperchargeRead_eq_charged_difference]
  unfold radialQuarticCharged123HyperchargeRead
    algebraicCharged123HyperchargeRead
  rw [← p286TemporalGaugeOneForm_wedge_reads_spatial123,
    ← p286TemporalGaugeOneForm_wedge_reads_spatial123,
    formNativeChargedGaugeThreeForm_evaluation,
    formNativeChargedGaugeThreeForm_evaluation]
  exact chargedGaugeFirstCoefficient_sub_eq_radialScalarChanged
    (canonicalCauchySlicePoint 0 space)
    (p286TemporalGaugeOneForm hyperchargeCoordinate)

/-- Exact `e₀` theorem mouth for the remaining finite Cartan read.  This is
still the same radial-quartic actual: the only unreduced scalar is the action
pairing of the hypercharge direction with the mother-action charge. -/
theorem radialQuarticEuler123HyperchargeRead_e0_eq_scalarActionPairing :
    radialQuarticEuler123HyperchargeRead SpatialE0 =
      -(1 / 40 : ℝ) *
        scalarCoordinatePairingRe
          (scalarP286ActionBilinear hyperchargeCoordinate
            (sourceGeneratedVacuumCoordinates Source))
          (scalarP286ActionBilinear Charge
            (sourceGeneratedVacuumCoordinates Source)) := by
  rw [radialQuarticEuler123HyperchargeRead_eq_radialScalarChanged]
  exact radialQuarticScalarConnectionChangedCoefficient_e0_eq_pairing

/-- Exact changed P286 read on the post-A/B radial constitutive actual.
It is computed from the native mother-action charge, not from the former U6
residual or from a demanded target.  Because the radial writer was selected to
pay the same U6 P286 Euler demand, this is a producer-consistency obstruction,
not a second independent constraint debt. -/
theorem radialQuarticEuler123HyperchargeRead_e0_eq :
    radialQuarticEuler123HyperchargeRead SpatialE0 =
      -(29 / 2160 : ℝ) := by
  rw [radialQuarticEuler123HyperchargeRead_e0_eq_scalarActionPairing]
  rw [show
    scalarCoordinatePairingRe
        (scalarP286ActionBilinear hyperchargeCoordinate
          (sourceGeneratedVacuumCoordinates Source))
        (scalarP286ActionBilinear Charge
          (sourceGeneratedVacuumCoordinates Source)) =
      motherActionChargeHyperchargeScalarPairing by rfl]
  rw [motherActionChargeHyperchargeScalarPairing_eq]
  norm_num

theorem radialQuarticEuler123HyperchargeRead_e0_ne_zero :
    radialQuarticEuler123HyperchargeRead SpatialE0 ≠ 0 := by
  rw [radialQuarticEuler123HyperchargeRead_e0_eq]
  norm_num

/-- Public exact-occurrence read on the post-A/B constitutive actual.  The
source anchor is unchanged, while the actual is explicitly the radial
constitutive successor rather than U6. -/
theorem fixedP506L0U6RadialQuarticConstitutiveActual_p286_zeroSlice_e0_spatial123_hypercharge_eq :
    p286CoordinateLiePairing hyperchargeCoordinate
        ((diracDualFormNativePointwiseJointResidual
          positiveSmoothUnifiedSource
          fixedP506L0U6RadialQuarticConstitutiveActual
          (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1))
          ).p286GaugeConnection 3) =
      -(29 / 2160 : ℝ) := by
  change radialQuarticEuler123HyperchargeRead SpatialE0 = _
  exact radialQuarticEuler123HyperchargeRead_e0_eq

theorem fixedP506L0U6RadialQuarticConstitutiveActual_p286_zeroSlice_e0_ne_zero :
    (diracDualFormNativePointwiseJointResidual
      positiveSmoothUnifiedSource
      fixedP506L0U6RadialQuarticConstitutiveActual
      (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1))
      ).p286GaugeConnection ≠ 0 := by
  intro formZero
  have evaluated := congrArg
    (fun form : P286GaugeThreeForm =>
      p286CoordinateLiePairing hyperchargeCoordinate (form 3)) formZero
  have zeroValue :
      p286CoordinateLiePairing hyperchargeCoordinate
          ((0 : P286GaugeThreeForm) 3) = 0 := by
    change p286CoordinateLiePairing hyperchargeCoordinate 0 = 0
    rw [show (0 : P286CoordinateCarrier) =
        (0 : ℝ) • hyperchargeCoordinate by simp,
      p286CoordinateLiePairing_smul_right]
    norm_num
  have contradiction : (-(29 / 2160 : ℝ)) = 0 := by
    rw [←
      fixedP506L0U6RadialQuarticConstitutiveActual_p286_zeroSlice_e0_spatial123_hypercharge_eq]
    exact evaluated.trans zeroValue
  norm_num at contradiction

/-- The exact post-A/B actual therefore fails the complete pointwise joint
zero fiber at the same source-owned occurrence. -/
theorem fixedP506L0U6RadialQuarticConstitutiveActual_not_onPointwiseJointZeroFiber_zeroSlice_e0 :
    ¬ OnDiracDualFormNativePointwiseJointZeroFiber
      positiveSmoothUnifiedSource
      fixedP506L0U6RadialQuarticConstitutiveActual
      (canonicalCauchySlicePoint 0 (EuclideanSpace.single 0 1)) := by
  intro zeroFiber
  apply
    fixedP506L0U6RadialQuarticConstitutiveActual_p286_zeroSlice_e0_ne_zero
  unfold OnDiracDualFormNativePointwiseJointZeroFiber at zeroFiber
  have projected := congrArg
    (fun residual : DiracDualFormNativePointwiseJointResidualCarrier =>
      residual.p286GaugeConnection) zeroFiber
  simpa using projected

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticP286EulerThreeForm

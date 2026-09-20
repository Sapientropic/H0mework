import H0mework.Physics.ConstrainedCauchy.FixedCartanECCauchyTemporalGlobalOperator
import H0mework.Physics.Jets.CanonicalTimePrimitiveMeasurableGermCalculus
import H0mework.Physics.Coframe.CoframeGravityGaugeRegularity
import H0mework.Physics.JointVariation.MatterTemporalLocalRegularity
import H0mework.Physics.IdentityGerms.IdentityECCartanRestartOriginCurvature
import H0mework.Physics.IdentityGerms.CoframeHessianLoadStability
import H0mework.Physics.QuarticDynamics.FixedScalarMomentumIdentityECLoadTransport

/-!
# Fixed P506/L0 Cartan--EC constraint/Cauchy common write

The temporal Cartan--EC writer closes all twelve evolution rows but preserves
the four Cauchy constraints.  This module inserts the existing action-owned
identity-EC Hessian leg before that temporal writer:

```text
same fixed source/current
  -> current-native Cartan base
  -> ten-row EC coframe Hessian and its Levi--Civita connection jet
  -> Cartan--EC temporal global writer
  -> one common holonomic actual.
```

Both public actuals below are closed terms generated from the fixed source and
current.  No residual value, support coordinate, target field, branch,
zero-fiber receipt, or free coefficient enters either constructor.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator

open Filter MeasureTheory Set
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCartanTangentSimplicityResponse
open StageNineCoframeHolonomicRegularity
open StageNineCoframeScalarMatterRegularity
open StageNineConjugateMatterVariation
open StageEightProofFreeSource
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionActualizationRegression
open StageNineDiracDualFormNativeCartanGravityAuxiliaryObstructionRegression
open StageNineDiracDualFormNativeCartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointMatterTemporalLocalRegularity
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCoframeECContactLocalActualLift
open StageNineDiracDualFormNativeCoframeECCurvatureNormalSection
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity
open StageNineDiracDualFormNativeCoframeMatterEulerParameterContinuity
open StageNineDiracDualFormNativeECCauchyConnectionLocalActualLift
open StageNineDiracDualFormNativeFixedP506CartanECCauchyTemporalGlobalOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedGravityTailCoframeLoadTemporalSpatial01
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticHessianOffDiagonalRows
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumIdentityECLoadTransport
open StageNineDiracDualFormNativeFourLegCriticalLocusCorrespondence
open StageNineDiracDualFormNativeIdentityECCartanRestartOriginCurvature
open StageNineDiracDualFormNativeIdentityECTemporalEvolutionSection
open StageNineDiracDualFormNativeIdentityECCurvatureNormalSection
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLoadStability
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianSection
open StageNineDiracDualFormNativeIIPlusCoframeECBalance
open StageNineDiracDualFormNativeIIPlusReductionLocalVariation
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeSynchronizedECNormalLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeGravityReactionInstallation
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality
open StageNineHolonomicGravityCurvatureVarianceNormalization
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIIPlusRestriction
open StageNineLinearPlebanskiCoframeActionPrincipal
open StageNineLorentzConnectionVariation
open StageNineP286ActionCauchySplit
open StageNineCanonicalTimePrimitiveMeasurableGermCalculus
open StageNineCoframeGravityGaugeRegularity
open StageNineTopologicalFourFormPairing

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

local instance fixedConstraintP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineDiracDualFormNativeCoframeGaugeEulerParameterContinuity.p286CoordinateIndexFintype

local instance fixedConstraintMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalInput

private abbrev CartanBase : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECCauchyTemporalBase

/-- The source/action-owned constraint leg.  Its Hessian is generated from
all ten eta-compatible coframe-action rows of the live Cartan current. -/
def fixedP506L0CartanECConstraintPreparedActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
    Source CartanBase

/-- The exact Cartan reread performed by the downstream temporal writer. -/
def fixedP506L0CartanECConstraintRestartActual :
    StageNineHolonomicConfiguration :=
  cartanECCauchyTemporalBase Source
    fixedP506L0CartanECConstraintPreparedActual

/-- One common constraint-plus-evolution successor.  The temporal operator
restarts Cartan and recomputes the live reaction only after the coframe and
its Levi--Civita jet have been written. -/
def fixedP506L0CartanECConstraintCauchyGlobalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator
    Source fixedP506L0CartanECConstraintPreparedActual

private abbrev Prepared : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintPreparedActual

private abbrev Restart : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintRestartActual

private abbrev Output : StageNineHolonomicConfiguration :=
  fixedP506L0CartanECConstraintCauchyGlobalActual

@[simp] theorem fixedP506L0CartanECConstraintPreparedActual_coframe_origin :
    fixedP506L0CartanECConstraintPreparedActual.coframe 0 = 1 := by
  unfold fixedP506L0CartanECConstraintPreparedActual
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  rw [identityECHolonomicCoframeHessianIncrementLocalActualLift_coframe_origin]
  rw [fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one]

private theorem prepared_smooth : Prepared.Smooth := by
  unfold Prepared fixedP506L0CartanECConstraintPreparedActual
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  exact
    identityECHolonomicCoframeHessianIncrementLocalActualLift_smooth
      CartanBase
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        Source CartanBase)
      fixedP506L0CartanECCauchyTemporalBase_smooth

theorem fixedP506L0CartanECConstraintPreparedActual_smooth :
    fixedP506L0CartanECConstraintPreparedActual.Smooth :=
  prepared_smooth

@[simp] theorem
    fixedP506L0CartanECConstraintCauchyGlobalActual_conjugateMatter_eq_prepared :
    fixedP506L0CartanECConstraintCauchyGlobalActual.conjugateMatter =
      fixedP506L0CartanECConstraintPreparedActual.conjugateMatter :=
  rfl

private theorem prepared_nondegenerate_origin :
    Matrix.det (Prepared.coframe 0) ≠ 0 := by
  rw [fixedP506L0CartanECConstraintPreparedActual_coframe_origin]
  norm_num

private theorem restart_connection_component_contDiffAt_one_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    ContDiffAt ℝ 1
      (fun point => Restart.gravityConnection point formDirection
        internalOut internalIn) 0 := by
  exact
    (cartanReactionRestart_connection_component_contDiffAt
      Source Prepared prepared_smooth 0 prepared_nondegenerate_origin
        formDirection internalOut internalIn).of_le (by norm_num)

private def ProfileField (contact : BasePoint) :
    StageNineContinuumPointField :=
  restrictContinuumPointFieldToIIPlus
    (toContinuumPointField Restart contact)

private theorem profileField_eq
    (contact : BasePoint) :
    diracDualFormNativeECNormalContactField
        (cartanECCauchyTemporalProfileInput Source Prepared contact) =
      ProfileField contact := by
  unfold diracDualFormNativeECNormalContactField
    diracDualFormNativeECNormalPreparedActual ProfileField
    cartanECCauchyTemporalProfileInput
  rw [toContinuumPointField_restrictHolonomicConfigurationToIIPlus]
  rw [fullyRecenterHolonomicConfiguration_pointField_origin_unconditional]
  rfl

private theorem profileField_coframe_contDiffAt_origin :
    ContDiffAt ℝ 0 (fun contact => (ProfileField contact).coframe) 0 := by
  change ContDiffAt ℝ 0 Prepared.coframe 0
  exact
    (holonomicCoframe_contDiff Prepared prepared_smooth).contDiffAt.of_le
      (by norm_num)

private theorem profileField_coframe_nondegenerate_origin :
    Matrix.det (ProfileField 0).coframe ≠ 0 := by
  change Matrix.det (Prepared.coframe 0) ≠ 0
  exact prepared_nondegenerate_origin

private theorem profileGaugeParameter_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun contact =>
        coframeGaugeActionParameterOfField (ProfileField contact)) 0 := by
  apply ContDiffAt.prodMk
  · apply contDiffAt_pi'
    intro pair
    change ContDiffAt ℝ 0
      (fun contact => p286CoordinateEquiv
        (Prepared.gaugeAuxiliary contact pair)) 0
    exact (prepared_smooth.2.2.2.2.2.1 pair).contDiffAt.of_le
      (by norm_num)
  · apply contDiffAt_pi'
    intro pair
    change ContDiffAt ℝ 0
      (fun contact => p286CoordinateEquiv
        (holonomicGaugeCurvature Prepared contact pair)) 0
    exact
      (holonomicGaugeCurvature_coordinate_contDiff Prepared prepared_smooth pair
        ).contDiffAt.of_le (by norm_num)

private theorem profileMatterParameter_contDiffAt_origin :
    ContDiffAt ℝ 0
      (fun contact =>
        coframeMatterActionParameterOfField (ProfileField contact)) 0 := by
  have scalarRegular : ContDiffAt ℝ 0 Prepared.scalar 0 :=
    prepared_smooth.2.2.2.2.2.2.1.contDiffAt.of_le (by norm_num)
  have scalarDerivativeRegular : ContDiffAt ℝ 0
      (fun contact => holonomicScalarCovariantDerivative Prepared contact) 0 := by
    apply contDiffAt_pi'
    intro direction
    exact
      (holonomicScalarCovariantDerivative_contDiff_local
        Prepared prepared_smooth direction).contDiffAt.of_le (by norm_num)
  have matterRegular : ContDiffAt ℝ 0
      (fun contact => matterCoordinateEquiv (Prepared.matter contact)) 0 :=
    prepared_smooth.2.2.2.2.2.2.2.1.contDiffAt.of_le (by norm_num)
  have matterDerivativeRegular : ContDiffAt ℝ 0
      (fun contact => fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative Restart contact direction)) 0 := by
    apply contDiffAt_pi'
    intro direction
    exact
      (cartanReactionRestart_matterCovariantDerivative_contDiffAt
        Source Prepared prepared_smooth 0 prepared_nondegenerate_origin
          direction).of_le (by norm_num)
  have conjugateRegular : ContDiffAt ℝ 0
      (fun contact => matterDualCoordinates
        (Prepared.conjugateMatter contact)) 0 :=
    (holonomicConjugateMatterCoordinates_contDiff Prepared prepared_smooth
      ).contDiffAt.of_le (by norm_num)
  change ContDiffAt ℝ 0 (fun contact =>
    (Prepared.scalar contact,
      holonomicScalarCovariantDerivative Prepared contact,
      matterCoordinateEquiv (Prepared.matter contact),
      (fun direction => matterCoordinateEquiv
        (holonomicMatterCovariantDerivative Restart contact direction)),
      matterDualCoordinates (Prepared.conjugateMatter contact))) 0
  exact scalarRegular.prodMk
    (scalarDerivativeRegular.prodMk
      (matterRegular.prodMk
        (matterDerivativeRegular.prodMk conjugateRegular)))

private theorem profileGaugeEuler_coordinate_contDiffAt_origin
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Prepared contact))
        (coframeCoordinateDirection row column)) 0 := by
  rw [show
    (fun contact =>
      diracDualFormNativeCoframeGaugeEulerCovector Source
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Prepared contact))
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeGaugeEulerCovector Source
          (ProfileField contact)
          (coframeCoordinateDirection row column) by
    funext contact
    rw [profileField_eq]]
  exact
    diracDualFormNativeCoframeGaugeEuler_coordinate_contDiffAt
      Source ProfileField 0 profileGaugeParameter_contDiffAt_origin
        profileField_coframe_contDiffAt_origin
        profileField_coframe_nondegenerate_origin row column

private theorem profileMatterEuler_coordinate_contDiffAt_origin
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Prepared contact))
        (coframeCoordinateDirection row column)) 0 := by
  rw [show
    (fun contact =>
      diracDualFormNativeCoframeMatterEulerCovector Source 0
        (diracDualFormNativeECNormalContactField
          (cartanECCauchyTemporalProfileInput Source Prepared contact))
        (coframeCoordinateDirection row column)) =
      fun contact =>
        diracDualFormNativeCoframeMatterEulerCovector Source 0
          (ProfileField contact)
          (coframeCoordinateDirection row column) by
    funext contact
    rw [profileField_eq]]
  exact
    diracDualFormNativeCoframeMatterEuler_coordinate_contDiffAt
      Source 0 ProfileField 0 profileMatterParameter_contDiffAt_origin
        profileField_coframe_contDiffAt_origin
        profileField_coframe_nondegenerate_origin row column

private theorem profileLoad_coordinate_contDiffAt_origin
    (row column : LorentzianIndex) :
    ContDiffAt ℝ 0 (fun contact =>
      diracDualFormNativeIdentityECLoad Source
        (cartanECCauchyTemporalProfileInput Source Prepared contact)
        (coframeCoordinateDirection row column)) 0 := by
  unfold diracDualFormNativeIdentityECLoad
  simp only [add_apply]
  exact
    (contDiffAt_const.add
      (profileGaugeEuler_coordinate_contDiffAt_origin row column)).add
      (profileMatterEuler_coordinate_contDiffAt_origin row column)

private theorem profileCurrentCurvature_eq_restart
    (contact : BasePoint) :
    diracDualFormNativeECCauchyCurrentCurvature
        (cartanECCauchyTemporalProfileInput Source Prepared contact) =
      holonomicGravityCurvature Restart contact := by
  unfold diracDualFormNativeECCauchyCurrentCurvature
    diracDualFormNativeECNormalPreparedActual
    cartanECCauchyTemporalProfileInput
  change
    holonomicGravityCurvature
        (fullyRecenterHolonomicConfiguration Restart contact) 0 =
      holonomicGravityCurvature Restart contact
  exact
    fullyRecenterHolonomicConfiguration_gravityCurvature_origin_unconditional
      Restart contact

private theorem profileCurrentCurvature_component_contDiffAt_origin
    (internalPair spacetimePair : Fin 6) :
    ContDiffAt ℝ 0 (fun contact =>
      diracDualFormNativeECCauchyCurrentCurvature
          (cartanECCauchyTemporalProfileInput Source Prepared contact)
          internalPair spacetimePair) 0 := by
  rw [show
    (fun contact =>
      diracDualFormNativeECCauchyCurrentCurvature
          (cartanECCauchyTemporalProfileInput Source Prepared contact)
          internalPair spacetimePair) =
      fun contact =>
        holonomicGravityCurvature Restart contact
          internalPair spacetimePair by
    funext contact
    rw [profileCurrentCurvature_eq_restart]]
  exact
    holonomicGravityCurvature_component_contDiffAt_of_connectionComponents
      Restart 0 restart_connection_component_contDiffAt_one_origin
        internalPair spacetimePair

private theorem profileCurrentCurvature_contDiffAt_origin :
    ContDiffAt ℝ 0 (fun contact =>
      diracDualFormNativeECCauchyCurrentCurvature
        (cartanECCauchyTemporalProfileInput Source Prepared contact)) 0 := by
  apply contDiffAt_pi'
  intro internalPair
  apply contDiffAt_pi'
  intro spacetimePair
  exact profileCurrentCurvature_component_contDiffAt_origin
    internalPair spacetimePair

private theorem profileDesiredEvolution_contDiffAt_origin :
    ContDiffAt ℝ 0 (fun contact =>
      diracDualFormNativeECDesiredEvolutionObservation Source
        (cartanECCauchyTemporalProfileInput Source Prepared contact)) 0 := by
  apply contDiffAt_pi'
  intro row
  apply contDiffAt_pi'
  intro direction
  unfold diracDualFormNativeECDesiredEvolutionObservation
    identityECSpatialCoframeCoordinatesOfCovector
  exact
    (profileLoad_coordinate_contDiffAt_origin row direction.succ).neg

private theorem profileIncrement_coordinate_contDiffAt_origin
    (internalPair : Fin 6) (direction : Fin 3) :
    ContDiffAt ℝ 0 (fun contact =>
      diracDualFormNativeECTemporalCurvatureIncrement Source
          (cartanECCauchyTemporalProfileInput Source Prepared contact)
          internalPair direction) 0 := by
  have generated :=
    diracDualFormNativeECTemporalCurvatureIncrement_contDiffAt_zero
      Source
      (fun contact =>
        cartanECCauchyTemporalProfileInput Source Prepared contact)
      0 profileCurrentCurvature_contDiffAt_origin
        profileDesiredEvolution_contDiffAt_origin
  exact contDiffAt_pi.mp (contDiffAt_pi.mp generated internalPair) direction

private theorem correctionProfile_coordinate_contDiffAt_origin
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ 0 (fun contact =>
      cartanECCauchyTemporalConnectionCorrectionProfile Source Prepared contact
        formDirection internalPair) 0 := by
  fin_cases formDirection
  · exact contDiffAt_const
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      profileIncrement_coordinate_contDiffAt_origin internalPair 0
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      profileIncrement_coordinate_contDiffAt_origin internalPair 1
  · simpa [cartanECCauchyTemporalConnectionCorrectionProfile] using
      profileIncrement_coordinate_contDiffAt_origin internalPair 2

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
      (0 : BasePoint) := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem profileInput_zero_eq_restart :
    cartanECCauchyTemporalProfileInput Source Prepared 0 = Restart := by
  change fullyRecenterHolonomicConfiguration Restart 0 = Restart
  exact fullyRecenterHolonomicConfiguration_zero Restart

private theorem correctionPrimitive_coordinate_differentiableAt_origin
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (fun point =>
        cartanECCauchyTemporalConnectionCorrectionPrimitive Source Prepared
          point formDirection internalPair) 0 := by
  exact
    (canonicalTimePrimitive_hasFDerivAt_zero_of_contDiffAt_zero
      (fun contact =>
        cartanECCauchyTemporalConnectionCorrectionProfile Source Prepared
          contact formDirection internalPair)
      (correctionProfile_coordinate_contDiffAt_origin
        formDirection internalPair)).differentiableAt

private theorem output_connection_component_differentiableAt_origin
    (formDirection internalOut internalIn : LorentzianIndex) :
    DifferentiableAt ℝ
      (fun point => Output.gravityConnection point formDirection
        internalOut internalIn) 0 := by
  have correctionDifferentiable : DifferentiableAt ℝ
      (fun point =>
        lorentzSkewConnectionOfBivectorOneForm
            (cartanECCauchyTemporalConnectionCorrectionPrimitive
              Source Prepared point)
          formDirection internalOut internalIn) 0 := by
    unfold lorentzSkewConnectionOfBivectorOneForm
      loweredLorentzBivectorMatrix
    have sumDifferentiable : DifferentiableAt ℝ
        (fun point =>
        ∑ pair : Fin 6,
          cartanECCauchyTemporalConnectionCorrectionPrimitive Source Prepared
              point formDirection pair *
            orientedLorentzBivectorBasisCoefficient pair internalOut
              internalIn) 0 := by
      rw [show
        (fun point =>
          ∑ pair : Fin 6,
            cartanECCauchyTemporalConnectionCorrectionPrimitive Source
                Prepared point formDirection pair *
              orientedLorentzBivectorBasisCoefficient pair internalOut
                internalIn) =
          ∑ pair : Fin 6, fun point =>
          cartanECCauchyTemporalConnectionCorrectionPrimitive Source Prepared
              point formDirection pair *
            orientedLorentzBivectorBasisCoefficient pair internalOut
              internalIn by
        funext point
        simp]
      exact DifferentiableAt.sum fun internalPair _ =>
        (correctionPrimitive_coordinate_differentiableAt_origin
          formDirection internalPair).mul (differentiableAt_const _)
    exact
      (differentiableAt_const (c := minkowskiInternalSign internalOut)).mul
        sumDifferentiable
  change DifferentiableAt ℝ (fun point =>
    Restart.gravityConnection point formDirection internalOut internalIn +
      lorentzSkewConnectionOfBivectorOneForm
          (cartanECCauchyTemporalConnectionCorrectionPrimitive
            Source Prepared point)
        formDirection internalOut internalIn) 0
  exact
    (restart_connection_component_contDiffAt_one_origin
      formDirection internalOut internalIn).differentiableAt (by norm_num) |>.add
        correctionDifferentiable

private theorem correctionProfile_timeLine_contDiffAt_origin
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    ContDiffAt ℝ 0 (fun time =>
      cartanECCauchyTemporalConnectionCorrectionProfile Source Prepared
        (canonicalCauchySlicePoint time (0 : StageNineSpatialPoint))
        formDirection internalPair) 0 := by
  have timeLineRegular : ContDiffAt ℝ 0
      (fun time : ℝ =>
        canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) 0 := by
    rw [show
      (fun time : ℝ =>
        canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)) =
        fun time =>
          canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) +
            time • coordinateDirection canonicalLorentzianTimeDirection by
      funext time
      apply PiLp.ext
      intro direction
      fin_cases direction <;>
        simp [canonicalCauchySlicePoint, coordinateDirection,
          canonicalLorentzianTimeDirection, Fin.sum_univ_three]]
    fun_prop
  let outer : BasePoint → ℝ := fun contact =>
    cartanECCauchyTemporalConnectionCorrectionProfile Source Prepared
      contact formDirection internalPair
  let inner : ℝ → BasePoint := fun time =>
    canonicalCauchySlicePoint time (0 : StageNineSpatialPoint)
  have outerRegular : ContDiffAt ℝ 0 outer (inner 0) := by
    rw [show inner 0 = (0 : BasePoint) by
      exact canonicalCauchySlicePoint_zero_zero]
    exact correctionProfile_coordinate_contDiffAt_origin
      formDirection internalPair
  have composed := outerRegular.comp 0 timeLineRegular
  simpa [outer, inner, Function.comp_def] using composed

private theorem stronglyMeasurableAtFilter_nhds_of_contDiffAt_zero
    (field : ℝ → ℝ)
    (regular : ContDiffAt ℝ 0 field 0) :
    StronglyMeasurableAtFilter field (nhds 0) volume := by
  obtain ⟨localSet, localSetNhd, fieldContinuousOn⟩ :=
    contDiffAt_zero.mp regular
  obtain ⟨domain, domainSubset, domainOpen, zeroMem⟩ :=
    mem_nhds_iff.mp localSetNhd
  exact
    ⟨domain, domainOpen.mem_nhds zeroMem,
      (fieldContinuousOn.mono domainSubset).aestronglyMeasurable
        domainOpen.measurableSet⟩

/-- The generated global connection realizes the complete action target at
the common occurrence.  Local regularity is proved from its explicit
source/current profile; no curvature target is accepted by the constructor. -/
theorem fixedP506L0CartanECConstraintCauchyGlobalActual_curvature_origin :
    holonomicGravityCurvature Output 0 =
      diracDualFormNativeECCauchyCurvatureTarget Source
        Restart := by
  have generated :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_curvature_zeroSlice
      Source Prepared (0 : StageNineSpatialPoint)
      (fun formDirection internalOut internalIn => by
        rw [canonicalCauchySlicePoint_zero_zero]
        exact
        (restart_connection_component_contDiffAt_one_origin
          formDirection internalOut internalIn).differentiableAt
            (by norm_num))
      (fun formDirection internalOut internalIn => by
        rw [canonicalCauchySlicePoint_zero_zero]
        exact output_connection_component_differentiableAt_origin
          formDirection internalOut internalIn)
      (fun formDirection internalPair =>
        (correctionProfile_timeLine_contDiffAt_origin
          formDirection internalPair).continuousAt)
      (fun formDirection internalPair =>
        stronglyMeasurableAtFilter_nhds_of_contDiffAt_zero _
          (correctionProfile_timeLine_contDiffAt_origin
            formDirection internalPair))
  rw [canonicalCauchySlicePoint_zero_zero] at generated
  rw [profileInput_zero_eq_restart] at generated
  exact generated

/-- The missing temporal-diagonal constraint is paid by the action-generated
ten-row Hessian on its own output actual.  This is producer soundness of the
constraint leg; the rejected `-319/108` read is nowhere consumed. -/
theorem fixedP506L0CartanECConstraintPreparedActual_balance_temporalDiagonal00 :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature
              fixedP506L0CartanECConstraintPreparedActual 0) +
          diracDualFormNativeIdentityECLoad Source
            fixedP506L0CartanECConstraintPreparedActual) 0 0 =
      0 := by
  have settlement :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_sameActual_settlement
      Source CartanBase
      fixedP506L0CartanECCauchyTemporalBase_smooth
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
        Source Current)
  have coordinate := congrFun (congrFun settlement
    (0 : LorentzianIndex)) (0 : LorentzianIndex)
  simpa [fixedP506L0CartanECConstraintPreparedActual,
    identityECEtaAntisymmetricPart, identityECEtaAdjoint,
    minkowskiInternalSign] using coordinate

private theorem cartanBase_connection_origin_eq_fixedAction :
    CartanBase.gravityConnection 0 = fixedActionCartanConnection := by
  have pointZero :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  have generated := base_connection_zeroSlice_eq_fixedAction
    (0 : StageNineSpatialPoint)
  rw [pointZero] at generated
  exact generated

private theorem cartanBase_connectionDerivative_origin_zero
    (direction formDirection internalOut internalIn : LorentzianIndex) :
    gravityConnectionDerivative CartanBase 0 direction
        formDirection internalOut internalIn =
      0 := by
  fin_cases direction
  · change
      gravityConnectionDerivative
          fixedP506L0CartanECCauchyTemporalBase 0
          canonicalLorentzianTimeDirection formDirection internalOut
          internalIn = 0
    exact base_connection_temporalDerivative_origin_zero
      formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (0 : Fin 3) formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (1 : Fin 3) formDirection internalOut internalIn
  · simpa using base_connection_spatialDerivative_origin_zero
      (2 : Fin 3) formDirection internalOut internalIn

/-- The fixed Cartan base already balances every spatial--temporal identity-EC
row before the Hessian write. -/
theorem fixedP506L0CartanECCauchyTemporalBase_balance_spatialTemporal
    (row : Fin 3) :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature CartanBase 0) +
          diracDualFormNativeIdentityECLoad Source CartanBase)
        row.succ 0 =
      0 := by
  rw [base_load_eq_input]
  have inputLoad :
      diracDualFormNativeCoframeECContactLoad Source
          fixedP506L0CartanECCauchyTemporalInput 0 =
        diracDualFormNativeIdentityECLoad Source
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual := by
    exact
      fixedP506L0ActionSelectedGravityTail_contactLoad_eq_u6RadialQuarticIdentityLoad
  rw [inputLoad]
  change
    identityDiracDualECConstraintObservation
          (holonomicGravityCurvature CartanBase 0) row.succ +
        diracDualFormNativeIdentityECLoad Source
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual
          (coframeCoordinateDirection row.succ 0) =
      0
  rw [congrFun
    (identityDiracDualECConstraintObservation_explicit
      (holonomicGravityCurvature CartanBase 0)) row.succ]
  fin_cases row
  · change
      (-holonomicGravityCurvature CartanBase 0 1 5 +
          holonomicGravityCurvature CartanBase 0 2 4) +
        diracDualFormNativeIdentityECLoad Source
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual
          (coframeCoordinateDirection 1 0) = 0
    rw [current_identityECLoad_spatialTemporal10_zero]
    simp +decide [holonomicGravityCurvature,
      cartanBase_connectionDerivative_origin_zero,
      cartanBase_connection_origin_eq_fixedAction,
      fixedActionCartanConnection_eq_positiveNormalForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      positiveDiracDualCartanContorsionNormalForm,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.sum_univ_four, Fin.sum_univ_six]
  · change
      (holonomicGravityCurvature CartanBase 0 0 5 -
          holonomicGravityCurvature CartanBase 0 2 3) +
        diracDualFormNativeIdentityECLoad Source
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual
          (coframeCoordinateDirection 2 0) = 0
    rw [current_identityECLoad_spatialTemporal20_zero]
    simp +decide [holonomicGravityCurvature,
      cartanBase_connectionDerivative_origin_zero,
      cartanBase_connection_origin_eq_fixedAction,
      fixedActionCartanConnection_eq_positiveNormalForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      positiveDiracDualCartanContorsionNormalForm,
      pairFirst, pairSecond, minkowskiInternalSign,
      Fin.sum_univ_four, Fin.sum_univ_six]
  · change
      (-holonomicGravityCurvature CartanBase 0 0 4 +
          holonomicGravityCurvature CartanBase 0 1 3) +
        diracDualFormNativeIdentityECLoad Source
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual
          (coframeCoordinateDirection 3 0) = 0
    rw [current_identityECLoad_spatialTemporal30]
    simp +decide [holonomicGravityCurvature,
      cartanBase_connectionDerivative_origin_zero,
      cartanBase_connection_origin_eq_fixedAction,
      fixedActionCartanConnection_eq_positiveNormalForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      positiveDiracDualCartanContorsionNormalForm,
      pairFirst, pairSecond, minkowskiInternalSign, Fin.sum_univ_six]
    norm_num

/-- The opposite temporal--spatial rows are balanced by the same source and
the same action load. -/
theorem fixedP506L0CartanECCauchyTemporalBase_balance_temporalSpatial
    (column : Fin 3) :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature CartanBase 0) +
          diracDualFormNativeIdentityECLoad Source CartanBase)
        0 column.succ =
      0 := by
  rw [base_load_eq_input]
  have inputLoad :
      diracDualFormNativeCoframeECContactLoad Source
          fixedP506L0CartanECCauchyTemporalInput 0 =
        diracDualFormNativeIdentityECLoad Source
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual := by
    exact
      fixedP506L0ActionSelectedGravityTail_contactLoad_eq_u6RadialQuarticIdentityLoad
  rw [inputLoad]
  change
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature CartanBase 0)
          (coframeCoordinateDirection 0 column.succ) +
        diracDualFormNativeIdentityECLoad Source
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual
          (coframeCoordinateDirection 0 column.succ) =
      0
  fin_cases column
  · change
      identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature CartanBase 0)
            (coframeCoordinateDirection 0 1) +
          diracDualFormNativeIdentityECLoad Source
            fixedP506L0U6RadialQuarticScalarMomentumCarryActual
            (coframeCoordinateDirection 0 1) = 0
    rw [current_identityECLoad_temporalSpatial01_zero]
    simp +decide [identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, internalBivectorDual,
      gravityInternalPairVarianceNormalization,
      gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      holonomicGravityCurvature,
      cartanBase_connectionDerivative_origin_zero,
      cartanBase_connection_origin_eq_fixedAction,
      fixedActionCartanConnection_eq_positiveNormalForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      positiveDiracDualCartanContorsionNormalForm,
      pairFirst, pairSecond, minkowskiInternalSign, Matrix.one_apply,
      Fin.sum_univ_four, Fin.sum_univ_six]
  · change
      identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature CartanBase 0)
            (coframeCoordinateDirection 0 2) +
          diracDualFormNativeIdentityECLoad Source
            fixedP506L0U6RadialQuarticScalarMomentumCarryActual
            (coframeCoordinateDirection 0 2) = 0
    rw [current_identityECLoad_temporalSpatial02_zero]
    simp +decide [identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, internalBivectorDual,
      gravityInternalPairVarianceNormalization,
      gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      holonomicGravityCurvature,
      cartanBase_connectionDerivative_origin_zero,
      cartanBase_connection_origin_eq_fixedAction,
      fixedActionCartanConnection_eq_positiveNormalForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      positiveDiracDualCartanContorsionNormalForm,
      pairFirst, pairSecond, minkowskiInternalSign, Matrix.one_apply,
      Fin.sum_univ_four, Fin.sum_univ_six]
  · change
      identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature CartanBase 0)
            (coframeCoordinateDirection 0 3) +
          diracDualFormNativeIdentityECLoad Source
            fixedP506L0U6RadialQuarticScalarMomentumCarryActual
            (coframeCoordinateDirection 0 3) = 0
    rw [current_identityECLoad_temporalSpatial03]
    simp +decide [identityDiracDualECCurvatureObservation,
      coframeCoordinateDirection, physicalIIPlusCoframeTangent,
      coframeWedgeTangent, internalBivectorDual,
      gravityInternalPairVarianceNormalization,
      gravityTopologicalWedgeCoefficient,
      orientedTwoFormWedgeCoefficient_explicit,
      lorentzianCoframeHodge, lorentzianTwoFormSign,
      holonomicGravityCurvature,
      cartanBase_connectionDerivative_origin_zero,
      cartanBase_connection_origin_eq_fixedAction,
      fixedActionCartanConnection_eq_positiveNormalForm,
      lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,
      orientedLorentzBivectorBasisCoefficient,
      positiveDiracDualCartanContorsionNormalForm,
      pairFirst, pairSecond, minkowskiInternalSign, Matrix.one_apply,
      Fin.sum_univ_four, Fin.sum_univ_six]
    norm_num

private theorem
    fixedP506L0CartanECConstraintPreparedActual_balance_spatialTemporal
    (row : Fin 3) :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Prepared 0) +
          diracDualFormNativeIdentityECLoad Source Prepared)
        row.succ 0 =
      0 := by
  have settlement :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_sameActual_settlement
      Source CartanBase
      fixedP506L0CartanECCauchyTemporalBase_smooth
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
        Source Current)
  have coordinate := congrFun (congrFun settlement row.succ)
    (0 : LorentzianIndex)
  change _ =
    identityECEtaAntisymmetricPart
      (coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature CartanBase 0) +
          diracDualFormNativeIdentityECLoad Source CartanBase))
      row.succ 0 at coordinate
  change
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature
              (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
                Source CartanBase) 0) +
          diracDualFormNativeIdentityECLoad Source
            (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
              Source CartanBase))
        row.succ 0 = 0
  rw [coordinate]
  simp [identityECEtaAntisymmetricPart, identityECEtaAdjoint,
    fixedP506L0CartanECCauchyTemporalBase_balance_spatialTemporal,
    fixedP506L0CartanECCauchyTemporalBase_balance_temporalSpatial]

/-- The one Hessian write closes the complete four-row identity-EC Cauchy
constraint carrier on its own output actual. -/
theorem fixedP506L0CartanECConstraintPreparedActual_balance_constraints
    (row : LorentzianIndex) :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Prepared 0) +
          diracDualFormNativeIdentityECLoad Source Prepared)
        row 0 =
      0 := by
  fin_cases row
  · exact
      fixedP506L0CartanECConstraintPreparedActual_balance_temporalDiagonal00
  · simpa using
      fixedP506L0CartanECConstraintPreparedActual_balance_spatialTemporal
        (0 : Fin 3)
  · simpa using
      fixedP506L0CartanECConstraintPreparedActual_balance_spatialTemporal
        (1 : Fin 3)
  · simpa using
      fixedP506L0CartanECConstraintPreparedActual_balance_spatialTemporal
        (2 : Fin 3)

private theorem cartanBase_connection_eq_actionNative :
    CartanBase.gravityConnection = fun point =>
      diracDualFormNativeActionCartanConnectionAt Source CartanBase point := by
  funext point
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_connection_selfGenerated
      Source Current point

private theorem constraintRestart_connection_origin :
    fixedP506L0CartanECConstraintRestartActual.gravityConnection 0 =
      fixedP506L0CartanECConstraintPreparedActual.gravityConnection 0 := by
  unfold fixedP506L0CartanECConstraintRestartActual
    cartanECCauchyTemporalBase
    fixedP506L0CartanECConstraintPreparedActual
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_connection_origin
      Source CartanBase
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        Source CartanBase)
      fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one
      cartanBase_connection_eq_actionNative

/-- The Cartan reread sees the same origin curvature as the generated
constraint Hessian actual.  Thus it cannot silently discard the constraint
write before the temporal leg runs. -/
theorem fixedP506L0CartanECConstraintRestartActual_curvature_origin :
    holonomicGravityCurvature
        fixedP506L0CartanECConstraintRestartActual 0 =
      holonomicGravityCurvature
        fixedP506L0CartanECConstraintPreparedActual 0 := by
  unfold fixedP506L0CartanECConstraintRestartActual
    cartanECCauchyTemporalBase
    fixedP506L0CartanECConstraintPreparedActual
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_identityECHessian_curvature_origin
      Source CartanBase
      (sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
        Source CartanBase)
      fixedP506L0CartanECCauchyTemporalBase_coframe_eq_one
      fixedP506L0CartanECCauchyTemporalBase_smooth
      cartanBase_connection_eq_actionNative

private theorem constraintRestart_nonGravityProjection_eq_prepared :
    identityECNonGravityContactProjection
        (diracDualFormNativeECNormalContactField
          fixedP506L0CartanECConstraintRestartActual) =
      identityECNonGravityContactProjection
        (diracDualFormNativeECNormalContactField
          fixedP506L0CartanECConstraintPreparedActual) := by
  have restartPrepared :
      diracDualFormNativeECNormalPreparedActual
          fixedP506L0CartanECConstraintRestartActual =
        fixedP506L0CartanECConstraintRestartActual :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      _).2
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
        Source fixedP506L0CartanECConstraintPreparedActual)
  have hessianPrepared :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift_prepared
      Source CartanBase
  unfold diracDualFormNativeECNormalContactField
  rw [restartPrepared]
  change
    identityECNonGravityContactProjection
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            fixedP506L0CartanECConstraintRestartActual 0)) =
      identityECNonGravityContactProjection
        (restrictContinuumPointFieldToIIPlus
          (toContinuumPointField
            (diracDualFormNativeECNormalPreparedActual
              (sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
                Source CartanBase)) 0))
  rw [hessianPrepared]
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext direction
    change
      holonomicMatterCovariantDerivative
          fixedP506L0CartanECConstraintRestartActual 0 direction =
        holonomicMatterCovariantDerivative
          fixedP506L0CartanECConstraintPreparedActual 0 direction
    unfold holonomicMatterCovariantDerivative
    rw [constraintRestart_connection_origin]
    rfl
  · rfl

theorem fixedP506L0CartanECConstraintRestartActual_load_origin :
    diracDualFormNativeIdentityECLoad Source
        fixedP506L0CartanECConstraintRestartActual =
      diracDualFormNativeIdentityECLoad Source
        fixedP506L0CartanECConstraintPreparedActual :=
  diracDualFormNativeIdentityECLoad_eq_of_nonGravityProjection_eq
    Source fixedP506L0CartanECConstraintRestartActual
      fixedP506L0CartanECConstraintPreparedActual
      constraintRestart_nonGravityProjection_eq_prepared

/-- The Hessian settlement survives the Cartan reread on the same actual. -/
theorem fixedP506L0CartanECConstraintRestartActual_balance_temporalDiagonal00 :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature
              fixedP506L0CartanECConstraintRestartActual 0) +
          diracDualFormNativeIdentityECLoad Source
            fixedP506L0CartanECConstraintRestartActual) 0 0 =
      0 := by
  rw [fixedP506L0CartanECConstraintRestartActual_curvature_origin,
    fixedP506L0CartanECConstraintRestartActual_load_origin]
  exact
    fixedP506L0CartanECConstraintPreparedActual_balance_temporalDiagonal00

/-- The Cartan reread preserves the complete four-row constraint carrier. -/
theorem fixedP506L0CartanECConstraintRestartActual_balance_constraints
    (row : LorentzianIndex) :
    coframeCovectorCoordinates
        (identityDiracDualECCurvatureObservation
            (holonomicGravityCurvature Restart 0) +
          diracDualFormNativeIdentityECLoad Source Restart)
        row 0 =
      0 := by
  rw [fixedP506L0CartanECConstraintRestartActual_curvature_origin,
    fixedP506L0CartanECConstraintRestartActual_load_origin]
  exact
    fixedP506L0CartanECConstraintPreparedActual_balance_constraints row

/-- The temporal target preserves every already-paid Cauchy row while
replacing the twelve evolution rows. -/
theorem fixedP506L0CartanECConstraintCauchyTarget_balance_constraints
    (row : LorentzianIndex) :
    identityDiracDualECCurvatureObservation
          (diracDualFormNativeECCauchyCurvatureTarget Source Restart)
          (coframeCoordinateDirection row 0) +
        diracDualFormNativeIdentityECLoad Source Restart
          (coframeCoordinateDirection row 0) =
      0 := by
  have constraintPreserved := congrFun
    (identityDiracDualECConstraintObservation_totalTarget
      (holonomicGravityCurvature Restart 0)
      (diracDualFormNativeECDesiredEvolutionObservation Source Restart))
    row
  change
    identityDiracDualECCurvatureObservation
        (diracDualFormNativeECCauchyCurvatureTarget Source Restart)
        (coframeCoordinateDirection row 0) =
      identityDiracDualECCurvatureObservation
        (holonomicGravityCurvature Restart 0)
        (coframeCoordinateDirection row 0) at constraintPreserved
  rw [constraintPreserved]
  exact fixedP506L0CartanECConstraintRestartActual_balance_constraints row

/-- At the origin the temporal action target itself carries the already paid
constraint.  The temporal target changes only the twelve evolution rows and
therefore does not reopen the Hessian-generated E00 row. -/
theorem fixedP506L0CartanECConstraintCauchyTarget_balance_temporalDiagonal00 :
    identityDiracDualECCurvatureObservation
          (diracDualFormNativeECCauchyCurvatureTarget Source
            fixedP506L0CartanECConstraintRestartActual)
          (coframeCoordinateDirection 0 0) +
        diracDualFormNativeIdentityECLoad Source
          fixedP506L0CartanECConstraintRestartActual
          (coframeCoordinateDirection 0 0) =
      0 :=
  fixedP506L0CartanECConstraintCauchyTarget_balance_constraints 0

private theorem constraintCauchyOutput_connection_origin :
    Output.gravityConnection 0 = Restart.gravityConnection 0 := by
  have generated :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_connection_zeroSlice
      Source Prepared (0 : StageNineSpatialPoint)
  rw [canonicalCauchySlicePoint_zero_zero] at generated
  exact generated

private theorem constraintCauchyOutput_nonGravityProjection_eq_restart :
    identityECNonGravityContactProjection
        (diracDualFormNativeECNormalContactField Output) =
      identityECNonGravityContactProjection
        (diracDualFormNativeECNormalContactField Restart) := by
  have outputPrepared :
      diracDualFormNativeECNormalPreparedActual Output = Output :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      _).2
      (sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
        Source Prepared)
  have restartPrepared :
      diracDualFormNativeECNormalPreparedActual Restart = Restart :=
    (restrictHolonomicConfigurationToIIPlus_eq_self_iff_diracDualFormNativeSimplicity
      _).2
      (sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
        Source Prepared)
  unfold diracDualFormNativeECNormalContactField
  rw [outputPrepared, restartPrepared]
  apply StageNineContinuumPointField.ext
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext direction
    change
      holonomicMatterCovariantDerivative Output 0 direction =
        holonomicMatterCovariantDerivative Restart 0 direction
    unfold holonomicMatterCovariantDerivative
    rw [constraintCauchyOutput_connection_origin]
    rfl
  · rfl

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_load_origin :
    diracDualFormNativeIdentityECLoad Source Output =
      diracDualFormNativeIdentityECLoad Source Restart :=
  diracDualFormNativeIdentityECLoad_eq_of_nonGravityProjection_eq
    Source Output Restart
      constraintCauchyOutput_nonGravityProjection_eq_restart

/-- The temporal leg closes all twelve spatial-column evolution rows on the
same final Output actual. -/
theorem fixedP506L0CartanECConstraintCauchyGlobalActual_evolutionBalance_origin :
    identityDiracDualECTemporalEvolutionObservation
          (holonomicGravityCurvature Output 0) +
        identityECSpatialCoframeCoordinatesOfCovector
          (diracDualFormNativeIdentityECLoad Source Output) =
      0 := by
  have generated :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_evolutionBalance_zeroSlice
      Source Prepared (0 : StageNineSpatialPoint)
      (fun formDirection internalOut internalIn => by
        rw [canonicalCauchySlicePoint_zero_zero]
        exact
          (restart_connection_component_contDiffAt_one_origin
            formDirection internalOut internalIn).differentiableAt
              (by norm_num))
      (fun formDirection internalOut internalIn => by
        rw [canonicalCauchySlicePoint_zero_zero]
        exact output_connection_component_differentiableAt_origin
          formDirection internalOut internalIn)
      (fun formDirection internalPair =>
        (correctionProfile_timeLine_contDiffAt_origin
          formDirection internalPair).continuousAt)
      (fun formDirection internalPair =>
        stronglyMeasurableAtFilter_nhds_of_contDiffAt_zero _
          (correctionProfile_timeLine_contDiffAt_origin
            formDirection internalPair))
  rw [canonicalCauchySlicePoint_zero_zero,
    profileInput_zero_eq_restart] at generated
  rw [fixedP506L0CartanECConstraintCauchyGlobalActual_load_origin]
  exact generated

/-- The single generated constraint-plus-evolution actual closes all four
Cauchy rows on the same origin occurrence. -/
theorem fixedP506L0CartanECConstraintCauchyGlobalActual_balance_constraints
    (row : LorentzianIndex) :
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output 0)
          (coframeCoordinateDirection row 0) +
        diracDualFormNativeIdentityECLoad Source Output
          (coframeCoordinateDirection row 0) =
      0 := by
  exact
    (congrArg₂ (fun first second : ℝ => first + second)
      (congrArg
        (fun curvature => identityDiracDualECCurvatureObservation curvature
          (coframeCoordinateDirection row 0))
        fixedP506L0CartanECConstraintCauchyGlobalActual_curvature_origin)
      (congrArg
        (fun load : LorentzianCoframe →L[ℝ] ℝ =>
          load (coframeCoordinateDirection row 0))
        fixedP506L0CartanECConstraintCauchyGlobalActual_load_origin)).trans
      (fixedP506L0CartanECConstraintCauchyTarget_balance_constraints row)

private theorem
    fixedP506L0CartanECConstraintCauchyGlobalActual_balance_coordinate
    (row column : LorentzianIndex) :
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output 0)
          (coframeCoordinateDirection row column) +
        diracDualFormNativeIdentityECLoad Source Output
          (coframeCoordinateDirection row column) =
      0 := by
  fin_cases column
  · exact
      fixedP506L0CartanECConstraintCauchyGlobalActual_balance_constraints row
  · have coordinate := congrFun (congrFun
      fixedP506L0CartanECConstraintCauchyGlobalActual_evolutionBalance_origin
      row) (0 : Fin 3)
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun
      fixedP506L0CartanECConstraintCauchyGlobalActual_evolutionBalance_origin
      row) (1 : Fin 3)
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate
  · have coordinate := congrFun (congrFun
      fixedP506L0CartanECConstraintCauchyGlobalActual_evolutionBalance_origin
      row) (2 : Fin 3)
    simpa [identityDiracDualECTemporalEvolutionObservation,
      identityECSpatialCoframeCoordinatesOfCovector] using coordinate

private theorem constraintCauchyOutput_normalContactField_eq :
    diracDualFormNativeECNormalContactField Output =
      restrictContinuumPointFieldToIIPlus
        (toContinuumPointField Output 0) := by
  rfl

private theorem
    fixedP506L0CartanECConstraintCauchyGlobalActual_coframeResidual_coordinate_origin
    (row column : LorentzianIndex) :
    (diracDualFormNativePointwiseJointResidual Source Output 0).coframe
        (coframeCoordinateDirection row column) =
      0 := by
  let variation := coframeCoordinateDirection row column
  have outputSimplicity : FormNativeGravitySimplicityEquation Output :=
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
      Source Prepared
  have outputAuxiliary : FormNativeGravityAuxiliaryEquation Output :=
    installFormNativeGravityReaction_auxiliaryEquation
      (cartanECCauchyTemporalConnectedActual Source Prepared)
  have reduction :=
    holonomicDiracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_full_of_equations
      Source Output outputSimplicity outputAuxiliary
      (fun _ => variation) 0
  change
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity Source 0
        (toContinuumPointField Output 0) variation =
      diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField Output 0) variation at reduction
  change
    diracDualFormNativeCoframeEulerCovector Source 0
        (toContinuumPointField Output 0) variation = 0
  rw [← reduction]
  rw [
    diracDualFormNativeIIPlusReducedCoframeFirstVariationDensity_eq_EC_balance
      Source 0 (toContinuumPointField Output 0)
      (by
        change Matrix.det (Prepared.coframe 0) ≠ 0
        exact prepared_nondegenerate_origin)
      variation]
  have outputCoframeOne :
      (toContinuumPointField Output 0).coframe =
        (1 : LorentzianCoframe) := by
    change Prepared.coframe 0 = 1
    exact fixedP506L0CartanECConstraintPreparedActual_coframe_origin
  rw [outputCoframeOne]
  rw [gravityTopologicalWedgeCoefficient_add_right]
  rw [show
      gravityTopologicalWedgeCoefficient
          (physicalIIPlusCoframeTangent (1 : LorentzianCoframe) variation)
          (gravityInternalPairVarianceNormalization
            (toContinuumPointField Output 0).gravityCurvature) =
        identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output 0) variation by
      rfl]
  rw [← identityDiracDualECCurvatureObservation_intrinsic_apply variation]
  have balance :=
    fixedP506L0CartanECConstraintCauchyGlobalActual_balance_coordinate
      row column
  unfold diracDualFormNativeIdentityECLoad at balance
  rw [constraintCauchyOutput_normalContactField_eq] at balance
  simpa only [add_apply, add_assoc] using balance

/-- The complete coframe Euler covector, not only selected coordinates,
vanishes on the one constraint-plus-evolution Output actual. -/
theorem
    fixedP506L0CartanECConstraintCauchyGlobalActual_coframeResidual_origin_zero :
    (diracDualFormNativePointwiseJointResidual Source Output 0).coframe = 0 := by
  apply (coframeCovector_eq_iff_coordinateDirections _ _).2
  intro row column
  rw [zero_apply]
  exact
    fixedP506L0CartanECConstraintCauchyGlobalActual_coframeResidual_coordinate_origin
      row column

/-- The closed constraint/Cauchy current is already the fixed point of the
same source-native EC curvature target at the canonical occurrence. -/
theorem
    fixedP506L0CartanECConstraintCauchyGlobalActual_curvature_eq_contactTarget_origin :
    holonomicGravityCurvature Output 0 =
      diracDualFormNativeCoframeECContactCurvatureTarget Source Output 0 := by
  have coframeOne : Output.coframe 0 = (1 : LorentzianCoframe) :=
    by
      change Prepared.coframe 0 = 1
      exact fixedP506L0CartanECConstraintPreparedActual_coframe_origin
  have loadEq :
      diracDualFormNativeCoframeECContactLoad Source Output 0 =
        diracDualFormNativeIdentityECLoad Source Output := by
    unfold diracDualFormNativeCoframeECContactLoad
      diracDualFormNativeIdentityECLoad
      diracDualFormNativeCoframeECContactField
      diracDualFormNativeECNormalContactField
      diracDualFormNativeCoframeECContactPreparedActual
      diracDualFormNativeECNormalPreparedActual
    rw [coframeOne]
    rfl
  have observed :
      coframeDiracDualECCurvatureObservation (Output.coframe 0)
          (holonomicGravityCurvature Output 0) =
        -diracDualFormNativeCoframeECContactLoad Source Output 0 := by
    rw [coframeOne, loadEq]
    apply (coframeCovector_eq_iff_coordinateDirections _ _).2
    intro row column
    rw [neg_apply]
    have balance :=
      fixedP506L0CartanECConstraintCauchyGlobalActual_balance_coordinate
        row column
    change
      identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output 0)
          (coframeCoordinateDirection row column) =
        -diracDualFormNativeIdentityECLoad Source Output
          (coframeCoordinateDirection row column)
    linarith
  unfold diracDualFormNativeCoframeECContactCurvatureTarget
  apply coframeDiracDualECCurvatureTarget_unique
  · exact observed
  · rfl

/-- The same generated output actual, rather than only its action target,
closes the previously missing temporal-diagonal identity-EC row. -/
theorem fixedP506L0CartanECConstraintCauchyGlobalActual_balance_temporalDiagonal00 :
    identityDiracDualECCurvatureObservation
          (holonomicGravityCurvature Output 0)
          (coframeCoordinateDirection 0 0) +
        diracDualFormNativeIdentityECLoad Source Output
          (coframeCoordinateDirection 0 0) =
      0 :=
  fixedP506L0CartanECConstraintCauchyGlobalActual_balance_constraints 0

@[simp] theorem fixedP506L0CartanECConstraintCauchyGlobalActual_coframe_origin :
    fixedP506L0CartanECConstraintCauchyGlobalActual.coframe 0 = 1 := by
  change fixedP506L0CartanECConstraintPreparedActual.coframe 0 = 1
  exact fixedP506L0CartanECConstraintPreparedActual_coframe_origin

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_simplicity :
    FormNativeGravitySimplicityEquation
      fixedP506L0CartanECConstraintCauchyGlobalActual := by
  exact
    sourceActionGeneratedDiracDualCartanECCauchyTemporalGlobalOperator_simplicity
      Source fixedP506L0CartanECConstraintPreparedActual

theorem fixedP506L0CartanECConstraintCauchyGlobalActual_exactLineage :
    Source.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  positiveSmoothUnifiedSource_generates_exactP506L0Lineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator

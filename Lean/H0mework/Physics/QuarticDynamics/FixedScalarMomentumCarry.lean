import H0mework.Physics.Cauchy.ScalarActionTemporalMomentumCarryCauchyDevelopmentOperator
import H0mework.Physics.QuarticDynamics.FixedP286EulerThreeForm
import H0mework.Physics.QuarticDynamics.FixedActionSelection
import H0mework.Physics.ScalarJets.FixedJointScalarSegmentRegularity

/-!
# Fixed P506/L0 scalar-momentum carry across the radial P286 write

The mother-action scalar temporal momentum selects a unique covariant scalar
velocity.  This module carries that already generated momentum through the
radial P286 connection update and installs the corresponding raw scalar first
jet on the same source/current lineage.  It consumes neither the post-write
P286 residual nor its `-29 / 2160` coordinate.

On the complete zero slice the new actual has the same scalar covariant first
jet and charged scalar current as the pre-radial algebraic actual; consequently
the `(123)` P286 readback vanishes.  This is producer soundness for the same
transported P286 responsibility, not an additional independent constraint.

The combined radial-plus-carry construction is called action-native only after
the separate source-event selection seam identifies the radial inverse
principal with the occurrence write selected by the mother action.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECFullOccurrenceGlobalAssemblySeamClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricECOriginTransport
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506CompleteJointScalarSegmentRegularity
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeFixedP506U6OccurrenceP286ZeroSliceActionProfile
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticActionSelection
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticConstitutiveAnchor
open StageNineDiracDualFormNativeFixedP506U6RadialQuarticP286EulerThreeForm
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineFormNativeChargedGaugeCurrentThreeForm
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricKinematics
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286RadialQuarticActionPrincipal
open StageNineScalarActionTemporalMomentumCarryCauchyDevelopmentOperator
open StageNineScalarActionTemporalMomentumLegendreVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherGaugeTheory
open SU7MotherLieAlgebra

open scoped ContDiff

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

local instance scalarCarryP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance scalarCarryP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance scalarCarryP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier :=
  StageNineP286HolonomicSecondJetCarrier.p286CoordinateIsTopologicalAddGroup

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Temporal : StageNineHolonomicConfiguration :=
  completeJointGlobalTemporalCurrent Source FixedInput

private abbrev Algebraic : StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent Source FixedInput

private abbrev U5 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual

private abbrev U6 : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointLiveElectricECFullOccurrenceGlobalActual

private abbrev PostAB : StageNineHolonomicConfiguration :=
  fixedP506L0U6RadialQuarticConstitutiveActual

private abbrev Charge : P286CoordinateCarrier :=
  fixedP506L0U6OccurrenceP286MotherActionCharge

def fixedP506L0U6RadialQuarticScalarMomentumCarryActual :
    StageNineHolonomicConfiguration :=
  scalarActionTemporalMomentumCarryCauchyDevelopmentOperator Source
    Algebraic PostAB

/-- The complete radial-plus-scalar actual factors through the radial field
selected by the fixed source/current mother-action occurrence.  This is the
producer-authority seam: the scalar carry does not turn a caller-supplied
radial charge into an action-owned update. -/
theorem fixedP506L0U6RadialQuarticScalarMomentumCarryActual_eq_actionSelected :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual =
      scalarActionTemporalMomentumCarryCauchyDevelopmentOperator Source
        Algebraic
        fixedP506L0U6ActionSelectedRadialQuarticConstitutiveActual := by
  unfold fixedP506L0U6RadialQuarticScalarMomentumCarryActual
  change
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator Source
        Algebraic fixedP506L0U6RadialQuarticConstitutiveActual = _
  rw [fixedP506L0U6RadialQuarticConstitutiveActual_eq_actionSelected]

private theorem input_scalar_vacuum :
    FixedInput.scalar = fun _ => sourceGeneratedVacuumCoordinates Source := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar,
    fixedP506JointActual_scalar_vacuum]

private theorem algebraic_scalar_eq_temporal :
    Algebraic.scalar = Temporal.scalar :=
  rfl

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

private theorem postAB_scalar_eq_algebraic :
    PostAB.scalar = Algebraic.scalar :=
  u6_scalar_eq_algebraic

private theorem postAB_scalar_eq_u5 :
    PostAB.scalar = U5.scalar :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator_scalar_eq_current
    Source U5

private theorem postAB_coframe_eq_algebraic :
    PostAB.coframe = Algebraic.coframe :=
  fixedP506L0U6_coframe_eq_algebraic

private theorem postAB_matter_eq_algebraic :
    PostAB.matter = Algebraic.matter :=
  u6_matter_eq_algebraic

private theorem postAB_conjugateMatter_eq_algebraic :
    PostAB.conjugateMatter = Algebraic.conjugateMatter :=
  u6_conjugateMatter_eq_algebraic

private theorem postAB_gaugeConnection_eq_algebraic_add_radial
    (point : BasePoint) (direction : LorentzianIndex) :
    PostAB.gaugeConnection point direction =
      Algebraic.gaugeConnection point direction +
        p286CoordinateEquiv.symm
          (p286RadialQuarticTemporalConnection Charge point direction) := by
  have varied := congrFun
    (holonomicP286GaugeConnectionCoordinate_vary U6
      (p286RadialQuarticTemporalConnection Charge) 1 point) direction
  change
    p286CoordinateEquiv (PostAB.gaugeConnection point direction) = _ at varied
  simp only [Pi.add_apply, one_smul] at varied
  unfold holonomicP286GaugeConnectionCoordinate at varied
  rw [fixedP506L0U6_gaugeConnection_eq_algebraic] at varied
  apply p286CoordinateEquiv.injective
  rw [map_add, p286CoordinateEquiv.apply_symm_apply]
  exact varied

private theorem algebraic_scalar_zeroSlice_eq_vacuum
    (space : StageNineSpatialPoint) :
    Algebraic.scalar (canonicalCauchySlicePoint 0 space) =
      sourceGeneratedVacuumCoordinates Source := by
  rw [congrFun algebraic_scalar_eq_temporal]
  calc
    Temporal.scalar (canonicalCauchySlicePoint 0 space) =
        FixedInput.scalar (canonicalCauchySlicePoint 0 space) :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_zeroSlice
        Source FixedInput space
    _ = sourceGeneratedVacuumCoordinates Source := by
      rw [congrFun input_scalar_vacuum]

private theorem temporal_scalarDirectionalDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative Temporal.scalar
        (canonicalCauchySlicePoint 0 space) direction = 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have inputDifferentiable : DifferentiableAt ℝ FixedInput.scalar point :=
    (fixedP506FormNativeJointActionSolvedSuccessor_smooth.2.2.2.2.2.2.1
      |>.differentiable (by simp) |>.differentiableAt)
  by_cases generatedDifferentiable : DifferentiableAt ℝ Temporal.scalar point
  · have generated :=
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator_scalar_firstJet_zeroSlice
        Source FixedInput space inputDifferentiable
        (by simpa [Temporal, completeJointGlobalTemporalCurrent, point] using
          generatedDifferentiable) direction
    change
      fieldDirectionalDerivative
          (sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
            Source FixedInput).scalar
          (canonicalCauchySlicePoint 0 space) direction = 0
    rw [generated]
    rw [input_scalar_vacuum]
    simp [fieldDirectionalDerivative]
  · unfold fieldDirectionalDerivative
    rw [fderiv_zero_of_not_differentiableAt generatedDifferentiable]
    rfl

private theorem algebraic_scalarDirectionalDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fieldDirectionalDerivative Algebraic.scalar
        (canonicalCauchySlicePoint 0 space) direction = 0 := by
  rw [algebraic_scalar_eq_temporal]
  exact temporal_scalarDirectionalDerivative_zeroSlice space direction

/-- The action-momentum velocity does not invert the post-A/B Euler read.
It is exactly the raw representation correction required to carry the old
covariant momentum through the independently generated radial connection. -/
theorem fixedP506L0U6RadialQuarticScalarMomentumCarryVelocity_eq
    (space : StageNineSpatialPoint) :
    scalarActionTemporalMomentumCarryVelocity Source Algebraic PostAB space =
      -scalarP286ActionBilinear
        (p286RadialQuarticTemporalConnection Charge
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection)
        (sourceGeneratedVacuumCoordinates Source) := by
  let point := canonicalCauchySlicePoint 0 space
  unfold scalarActionTemporalMomentumCarryVelocity
  dsimp only
  rw [scalarTemporalCovariantVelocityOfMomentum_eq Source Algebraic point
    (fixedP506L0Algebraic_coframe_zeroSlice space)]
  unfold holonomicScalarCovariantDerivative
  rw [algebraic_scalarDirectionalDerivative_zeroSlice space
      canonicalLorentzianTimeDirection,
    congrFun postAB_scalar_eq_algebraic point,
    algebraic_scalar_zeroSlice_eq_vacuum space,
    postAB_gaugeConnection_eq_algebraic_add_radial point
      canonicalLorentzianTimeDirection,
    p286LieBlockEmbed_add, scalarMotherLieAction_add]
  simp only [zero_add]
  abel

/-- Explicit polynomial/affine normal form of the coupled scalar field. -/
theorem fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_normalForm
    (point : BasePoint) :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar point =
      sourceGeneratedVacuumCoordinates Source +
        canonicalTimeProjection point •
          (-scalarP286ActionBilinear
            (p286RadialQuarticTemporalConnection Charge
              (canonicalCauchySlicePoint 0
                (canonicalSpatialProjection point))
              canonicalLorentzianTimeDirection)
            (sourceGeneratedVacuumCoordinates Source)) := by
  unfold fixedP506L0U6RadialQuarticScalarMomentumCarryActual
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator
  change
    PostAB.scalar
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)) +
        canonicalTimeProjection point •
          scalarActionTemporalMomentumCarryVelocity Source Algebraic PostAB
            (canonicalSpatialProjection point) = _
  rw [congrFun postAB_scalar_eq_algebraic,
    algebraic_scalar_zeroSlice_eq_vacuum,
    fixedP506L0U6RadialQuarticScalarMomentumCarryVelocity_eq]

theorem fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_contDiff :
    ContDiff ℝ ∞
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar := by
  have sliceSmooth : ContDiff ℝ ∞ fun point : BasePoint =>
      canonicalCauchySlicePoint 0 (canonicalSpatialProjection point) := by
    have zeroSliceSmooth : ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
      rw [show canonicalCauchySlicePoint 0 = canonicalSpatialInclusion by
        funext space
        rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
        simp]
      exact canonicalSpatialInclusion.contDiff
    exact zeroSliceSmooth.comp canonicalSpatialProjection.contDiff
  have radialSmooth : ContDiff ℝ ∞ fun point : BasePoint =>
      p286RadialQuarticTemporalConnection Charge
        (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))
        canonicalLorentzianTimeDirection := by
    exact
      (contDiff_pi.mp (p286RadialQuarticTemporalConnection_contDiff Charge)
        canonicalLorentzianTimeDirection).comp sliceSmooth
  have actionSmooth : ContDiff ℝ ∞ fun point : BasePoint =>
      scalarP286ActionBilinear
        (p286RadialQuarticTemporalConnection Charge
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))
          canonicalLorentzianTimeDirection)
        (sourceGeneratedVacuumCoordinates Source) := by
    exact
      (scalarP286ActionBilinear.toContinuousBilinearMap.contDiff.comp
        radialSmooth).clm_apply contDiff_const
  rw [show fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar =
      fun point => sourceGeneratedVacuumCoordinates Source +
        canonicalTimeProjection point •
          (-scalarP286ActionBilinear
            (p286RadialQuarticTemporalConnection Charge
              (canonicalCauchySlicePoint 0
                (canonicalSpatialProjection point))
              canonicalLorentzianTimeDirection)
            (sourceGeneratedVacuumCoordinates Source)) by
    funext point
    exact
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_normalForm
        point]
  exact contDiff_const.add
    (canonicalTimeProjection.contDiff.smul actionSmooth.neg)

private theorem postAB_scalar_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ PostAB.scalar
      (canonicalCauchySlicePoint 0 space) := by
  rw [postAB_scalar_eq_u5]
  have regular :=
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual_scalar_contDiffAt
      0 space (fixedP506L0FinalCommonTimeAxis_zero_mem_originDomain space)
  simpa [U5] using regular.differentiableAt (by simp)

private theorem fixedCarry_scalar_differentiableAt_zeroSlice
    (space : StageNineSpatialPoint) :
    DifferentiableAt ℝ
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar
      (canonicalCauchySlicePoint 0 space) :=
  fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_contDiff
    |>.differentiable (by simp) |>.differentiableAt

theorem fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.coframe
        (canonicalCauchySlicePoint 0 space) = 1 := by
  change PostAB.coframe (canonicalCauchySlicePoint 0 space) = 1
  rw [congrFun postAB_coframe_eq_algebraic]
  exact fixedP506L0Algebraic_coframe_zeroSlice space

private theorem fixedCarry_gaugeConnection_eq_postAB :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.gaugeConnection =
      PostAB.gaugeConnection :=
  rfl

private theorem fixedCarry_gaugeAuxiliary_eq_postAB :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.gaugeAuxiliary =
      PostAB.gaugeAuxiliary :=
  rfl

private theorem fixedCarry_coframe_eq_algebraic :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.coframe =
      Algebraic.coframe :=
  postAB_coframe_eq_algebraic

private theorem fixedCarry_matter_eq_algebraic :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.matter =
      Algebraic.matter :=
  postAB_matter_eq_algebraic

private theorem fixedCarry_conjugateMatter_eq_algebraic :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.conjugateMatter =
      Algebraic.conjugateMatter :=
  postAB_conjugateMatter_eq_algebraic

/-! The following whole-field equalities are the public dependency seam for
later action legs.  They expose only fields already preserved by the
radial-plus-momentum constructor; no equation or residual is promoted to an
input. -/

theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_coframe_eq_algebraic :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.coframe =
      Algebraic.coframe :=
  fixedCarry_coframe_eq_algebraic

theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_matter_eq_algebraic :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.matter =
      Algebraic.matter :=
  fixedCarry_matter_eq_algebraic

theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_conjugateMatter_eq_algebraic :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.conjugateMatter =
      Algebraic.conjugateMatter :=
  fixedCarry_conjugateMatter_eq_algebraic

theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_gaugeConnection_eq_postAB :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.gaugeConnection =
      PostAB.gaugeConnection :=
  fixedCarry_gaugeConnection_eq_postAB

theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_gaugeAuxiliary_eq_postAB :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.gaugeAuxiliary =
      PostAB.gaugeAuxiliary :=
  fixedCarry_gaugeAuxiliary_eq_postAB

theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_gaugeConnection_normalForm
    (point : BasePoint) (direction : LorentzianIndex) :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.gaugeConnection
        point direction =
      Algebraic.gaugeConnection point direction +
        p286CoordinateEquiv.symm
          (p286RadialQuarticTemporalConnection Charge point direction) := by
  rw [congrFun fixedCarry_gaugeConnection_eq_postAB point]
  exact postAB_gaugeConnection_eq_algebraic_add_radial point direction

theorem fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar
        (canonicalCauchySlicePoint 0 space) =
      Algebraic.scalar (canonicalCauchySlicePoint 0 space) := by
  rw [show
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar
        (canonicalCauchySlicePoint 0 space) =
      PostAB.scalar (canonicalCauchySlicePoint 0 space) by
    exact
      scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_zeroSlice
        Source Algebraic PostAB space]
  rw [congrFun postAB_scalar_eq_algebraic]

private theorem postAB_gaugeConnection_zeroSlice_spatial_eq_algebraic
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    PostAB.gaugeConnection (canonicalCauchySlicePoint 0 space) axis.succ =
      Algebraic.gaugeConnection
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  rw [postAB_gaugeConnection_eq_algebraic_add_radial]
  have radialZero :
      p286RadialQuarticTemporalConnection Charge
          (canonicalCauchySlicePoint 0 space) axis.succ = 0 := by
    simp [p286RadialQuarticTemporalConnection,
      p286TemporalGaugeOneForm, canonicalLorentzianTimeDirection]
  rw [radialZero, map_zero, add_zero]

private theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalarSpatialDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    fieldDirectionalDerivative
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar
        (canonicalCauchySlicePoint 0 space) axis.succ =
      fieldDirectionalDerivative Algebraic.scalar
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  rw [show
    fieldDirectionalDerivative
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual.scalar
        (canonicalCauchySlicePoint 0 space) axis.succ =
      fieldDirectionalDerivative PostAB.scalar
        (canonicalCauchySlicePoint 0 space) axis.succ by
    exact
      scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_scalar_spatialDirectionalDerivative_zeroSlice
        Source Algebraic PostAB space axis
        (postAB_scalar_differentiableAt_zeroSlice space)
        (fixedCarry_scalar_differentiableAt_zeroSlice space)]
  rw [postAB_scalar_eq_algebraic]

/-- The coupled write carries the canonical scalar covariant momentum through
the post-A/B connection on the entire zero slice. -/
theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_temporalCovariantDerivative_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection =
      holonomicScalarCovariantDerivative Algebraic
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection := by
  rw [show
      holonomicScalarCovariantDerivative
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual
          (canonicalCauchySlicePoint 0 space)
          canonicalLorentzianTimeDirection =
        scalarTemporalCovariantVelocityOfMomentum Source Algebraic
          (canonicalCauchySlicePoint 0 space) by
    exact
      scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_temporalCovariantDerivative_zeroSlice
        Source Algebraic PostAB space
        (fixedCarry_scalar_differentiableAt_zeroSlice space)]
  exact scalarTemporalCovariantVelocityOfMomentum_eq Source Algebraic
    (canonicalCauchySlicePoint 0 space)
    (fixedP506L0Algebraic_coframe_zeroSlice space)

private theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_spatialCovariantDerivative_zeroSlice
    (space : StageNineSpatialPoint)
    (axis : Fin 3) :
    holonomicScalarCovariantDerivative
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual
        (canonicalCauchySlicePoint 0 space) axis.succ =
      holonomicScalarCovariantDerivative Algebraic
        (canonicalCauchySlicePoint 0 space) axis.succ := by
  unfold holonomicScalarCovariantDerivative
  rw [
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalarSpatialDerivative_zeroSlice,
    congrFun fixedCarry_gaugeConnection_eq_postAB,
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_zeroSlice_eq_algebraic,
    postAB_gaugeConnection_zeroSlice_spatial_eq_algebraic]

/-- Complete scalar covariant first-jet carry, not only its temporal
coordinate. -/
theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalarCovariantDerivative_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicScalarCovariantDerivative
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicScalarCovariantDerivative Algebraic
        (canonicalCauchySlicePoint 0 space) := by
  funext direction
  fin_cases direction
  · exact
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_temporalCovariantDerivative_zeroSlice
        space
  · exact
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_spatialCovariantDerivative_zeroSlice
        space 0
  · exact
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_spatialCovariantDerivative_zeroSlice
        space 1
  · exact
      fixedP506L0U6RadialQuarticScalarMomentumCarryActual_spatialCovariantDerivative_zeroSlice
        space 2

/-- The complete charged scalar/matter action current is carried back to the
pre-radial algebraic read on the same zero slice. -/
theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_chargedGaugeThreeForm_zeroSlice_eq_algebraic
    (space : StageNineSpatialPoint) :
    formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField
          fixedP506L0U6RadialQuarticScalarMomentumCarryActual
          (canonicalCauchySlicePoint 0 space)) =
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Algebraic
          (canonicalCauchySlicePoint 0 space)) := by
  exact formNativeChargedGaugeThreeForm_eq_of_actionData_eq Source
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual Algebraic
    (canonicalCauchySlicePoint 0 space)
    (congrFun fixedCarry_coframe_eq_algebraic _)
    (fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalar_zeroSlice_eq_algebraic
      space)
    (fixedP506L0U6RadialQuarticScalarMomentumCarryActual_scalarCovariantDerivative_zeroSlice
      space)
    (congrFun fixedCarry_matter_eq_algebraic _)
    (congrFun fixedCarry_conjugateMatter_eq_algebraic _)

private theorem
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_p286Geometric_eq_postAB
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual point =
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative PostAB point := by
  unfold holonomicP286GaugeAuxiliaryExteriorCovariantDerivative
    p286GaugeAuxiliaryDirectionalDerivative
    holonomicP286GaugeConnectionCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  rw [fixedCarry_gaugeConnection_eq_postAB,
    fixedCarry_gaugeAuxiliary_eq_postAB]

/-- P286 producer soundness after the scalar momentum-carry leg: the complete
`(123)` Euler component is zero at every zero-slice occurrence. -/
theorem fixedP506L0U6RadialQuarticScalarMomentumCarryActual_p286Euler123_zeroSlice
    (space : StageNineSpatialPoint) :
    holonomicFormNativeP286GaugeEulerThreeForm Source 0
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual
        (canonicalCauchySlicePoint 0 space) 3 = 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have chargedEq :=
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_chargedGaugeThreeForm_zeroSlice_eq_algebraic
      space
  have postABReduction :=
    fixedP506L0U6RadialQuarticConstitutiveActual_euler123_eq_charged_sub_algebraic
      space
  have postABReduction' :
      holonomicFormNativeP286GaugeEulerThreeForm Source 0 PostAB
          (canonicalCauchySlicePoint 0 space) 3 =
        formNativeChargedGaugeThreeForm Source 0
            (canonicalCauchySlicePoint 0 space)
            (toContinuumPointField PostAB
              (canonicalCauchySlicePoint 0 space)) 3 -
          formNativeChargedGaugeThreeForm Source 0
            (canonicalCauchySlicePoint 0 space)
            (toContinuumPointField Algebraic
              (canonicalCauchySlicePoint 0 space)) 3 := by
    simpa [Source, PostAB, Algebraic] using postABReduction
  have geometricEq :
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative PostAB
          (canonicalCauchySlicePoint 0 space) 3 =
        -formNativeChargedGaugeThreeForm Source 0
          (canonicalCauchySlicePoint 0 space)
          (toContinuumPointField Algebraic
            (canonicalCauchySlicePoint 0 space)) 3 := by
    unfold holonomicFormNativeP286GaugeEulerThreeForm at postABReduction'
    simp only [Pi.add_apply] at postABReduction'
    let geometric :=
      holonomicP286GaugeAuxiliaryExteriorCovariantDerivative PostAB
        (canonicalCauchySlicePoint 0 space) 3
    let postCharged :=
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField PostAB
          (canonicalCauchySlicePoint 0 space)) 3
    let algebraicCharged :=
      formNativeChargedGaugeThreeForm Source 0
        (canonicalCauchySlicePoint 0 space)
        (toContinuumPointField Algebraic
          (canonicalCauchySlicePoint 0 space)) 3
    change geometric + postCharged = postCharged - algebraicCharged at postABReduction'
    change geometric = -algebraicCharged
    calc
      geometric = (geometric + postCharged) - postCharged := by abel
      _ = (postCharged - algebraicCharged) - postCharged := by
        rw [postABReduction']
      _ = -algebraicCharged := by abel
  unfold holonomicFormNativeP286GaugeEulerThreeForm
  rw [
    fixedP506L0U6RadialQuarticScalarMomentumCarryActual_p286Geometric_eq_postAB,
    chargedEq]
  simp only [Pi.add_apply, geometricEq]
  abel

/-- Exact action-momentum preservation.  The recomputed P286 read is therefore
a producer-soundness check for this coupled leg, not an independent debt. -/
theorem fixedP506L0U6RadialQuarticScalarMomentumCarryActual_momentum_preserved_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : ScalarCoordinateCarrier) :
    scalarTemporalMomentumDualAt Source
        fixedP506L0U6RadialQuarticScalarMomentumCarryActual
        (canonicalCauchySlicePoint 0 space) direction =
      scalarTemporalMomentumDualAt Source Algebraic
        (canonicalCauchySlicePoint 0 space) direction := by
  exact
    scalarActionTemporalMomentumCarryCauchyDevelopmentOperator_momentum_preserved_zeroSlice
      Source Algebraic PostAB space
      (fixedP506L0Algebraic_coframe_zeroSlice space)
      (by
        rw [congrFun postAB_coframe_eq_algebraic]
        exact fixedP506L0Algebraic_coframe_zeroSlice space)
      (fixedCarry_scalar_differentiableAt_zeroSlice space) direction

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506U6RadialQuarticScalarMomentumCarry

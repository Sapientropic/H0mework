import H0mework.Physics.FixedJoint.FixedSectionResponseResidual
import H0mework.Physics.ConstitutiveAction.ResponseOperator
import H0mework.Physics.Constitutive.P286GaugeConstitutiveElimination

/-!
# Fixed P506/L0 form-native constitutive joint-action successor

The canonical section response is already generated before this module
starts.  Its residual is not an input here.  The next common actual is
generated forward by the authoritative algebraic action equivalence:

```text
canonical source/action successor
  -> live-coframe, live-curvature P286 constitutive inverse
  -> current-owned primal matter write
  -> current-owned independent adjoint write
  -> repaired-root full Einstein--Cartan recomputation
  -> one common successor.
```

No residual coordinate, sign, support, branch, endpoint, zero-fiber witness,
or supplied response enters the constructor.  The P286 auxiliary equation is
then re-read on the output wherever its already generated coframe is
nondegenerate.  The module does not claim that the P286 connection equation,
the other Euler channels, or the complete global zero fiber are closed.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineBlockwiseConstitutive
open StageNineCanonicalCauchyState
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeECFullCauchyConnectionJetReadout
open StageNineDiracDualFormNativeConstitutiveJointActionResponseOperator
open StageNineDiracDualFormNativeCoframeLocalVariation
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponseResidual
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeGaugeWedge
open StageNineFormNativeGravityMultiplierAuxiliaryIntegratedVariation
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance constitutiveSuccessorP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance constitutiveSuccessorP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance constitutiveSuccessorP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  ext direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private abbrev FixedConstitutiveInput :
    StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-! ## Forward action-owned constitutive leg -/

/-- The unique three-block auxiliary coordinate generated from the live
coframe and the literal curvature of the already generated input actual. -/
def fixedP506FormNativeConstitutiveAuxiliaryCoordinate
    (point : BasePoint) : FormNativeP286GaugeCoordinateTwoForm :=
  formNativeP286GaugeActualToCoordinateLinear
    (formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (FixedConstitutiveInput.coframe point)
      (holonomicGaugeCurvature FixedConstitutiveInput point))

def fixedP506FormNativeConstitutiveAuxiliaryField :
    BasePoint → Fin 6 → P286LieBlockData :=
  fun point =>
    formNativeP286GaugeEliminatedAuxiliaryAtBoundary
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (FixedConstitutiveInput.coframe point)
      (holonomicGaugeCurvature FixedConstitutiveInput point)

/-- Install the action-owned algebraic response on the whole current actual.
This is a full-configuration write even though its active primitive field is
the P286 auxiliary. -/
private def fixedP506FormNativeConstitutiveWrittenCurrent :
    StageNineHolonomicConfiguration :=
  { FixedConstitutiveInput with
    gaugeAuxiliary := fixedP506FormNativeConstitutiveAuxiliaryField }

private def fixedP506FormNativeConstitutivePrimalWrittenCurrent :
    StageNineHolonomicConfiguration :=
  actionGeneratedCurrentCoframeMatterTimeResponseActual
    fixedP506FormNativeConstitutiveWrittenCurrent

private def fixedP506FormNativeConstitutiveDualWrittenCurrent :
    StageNineHolonomicConfiguration :=
  actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
    fixedP506FormNativeConstitutivePrimalWrittenCurrent

/-- One public same-source common successor after all downstream action
dependencies of the constitutive write are recomputed. -/
def FixedP506FormNativeConstitutiveJointActionSuccessor :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    positiveSmoothUnifiedSource
    fixedP506FormNativeConstitutiveDualWrittenCurrent

/-- The fixed P506/L0 successor is exactly the specialization of the public
branch-free action operator.  This equality records forward producer
provenance; no residual or zero-fiber readout enters either side. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_eq_actionOperator :
    FixedP506FormNativeConstitutiveJointActionSuccessor =
      diracDualFormNativeConstitutiveJointActionResponseOperator
        positiveSmoothUnifiedSource
        FixedP506FormNativeJointActionSolvedSuccessor := by
  rfl

/-! ## Primitive provenance seams -/

theorem fixedP506FormNativeConstitutiveJointActionSuccessor_coframe :
    FixedP506FormNativeConstitutiveJointActionSuccessor.coframe =
      FixedConstitutiveInput.coframe := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    fixedP506FormNativeConstitutiveDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_coframe,
    fixedP506FormNativeConstitutivePrimalWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_coframe]
  rfl

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeConnection =
      FixedConstitutiveInput.gaugeConnection := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection,
    fixedP506FormNativeConstitutiveDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gaugeConnection,
    fixedP506FormNativeConstitutivePrimalWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gaugeConnection]
  rfl

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeAuxiliary =
      fixedP506FormNativeConstitutiveAuxiliaryField := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary,
    fixedP506FormNativeConstitutiveDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gaugeAuxiliary,
    fixedP506FormNativeConstitutivePrimalWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gaugeAuxiliary]
  rfl

theorem fixedP506FormNativeConstitutiveJointActionSuccessor_scalar :
    FixedP506FormNativeConstitutiveJointActionSuccessor.scalar =
      FixedConstitutiveInput.scalar := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar,
    fixedP506FormNativeConstitutiveDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_scalar,
    fixedP506FormNativeConstitutivePrimalWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_scalar]
  rfl

theorem fixedP506FormNativeConstitutiveJointActionSuccessor_matter_origin :
    FixedP506FormNativeConstitutiveJointActionSuccessor.matter 0 =
      FixedConstitutiveInput.matter 0 := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter,
    fixedP506FormNativeConstitutiveDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_matter,
    fixedP506FormNativeConstitutivePrimalWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_matter_origin]
  rfl

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter_origin :
    FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter 0 =
      FixedConstitutiveInput.conjugateMatter 0 := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    fixedP506FormNativeConstitutiveDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin,
    fixedP506FormNativeConstitutivePrimalWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_conjugateMatter]
  rfl

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_exactLineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506FormNativeJointActionSolvedSuccessor_exactLineage

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    FixedP506FormNativeConstitutiveJointActionSuccessor.coframe
        (canonicalCauchySlicePoint 0 space) =
      1 := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice space

/-! ## Action-equivalence agreement on the generated Cauchy slice -/

/-- On the complete generated time-zero slice, the authoritative live-coframe
constitutive inverse returns the auxiliary already carried by the canonical
joint-action solution.  This is uniqueness of the action equivalence on its
zero fiber; no residual coordinate, sign, support, or branch is consumed by
the new write. -/
theorem fixedP506FormNativeConstitutiveAuxiliaryField_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveAuxiliaryField
        (canonicalCauchySlicePoint 0 space) =
      FixedConstitutiveInput.gaugeAuxiliary
        (canonicalCauchySlicePoint 0 space) := by
  let point := canonicalCauchySlicePoint 0 space
  have nondegenerate :
      Matrix.det (FixedConstitutiveInput.coframe point) ≠ 0 := by
    rw [show FixedConstitutiveInput.coframe point = 1 by
      exact
        fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
          space]
    norm_num
  have oldResidualZero :
      formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
          (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (toContinuumPointField FixedConstitutiveInput point) =
        0 := by
    simpa [point,
      fixedP506FormNativeJointActionSolvedSuccessorResidualSection,
      diracDualFormNativeJointResidualSection,
      diracDualFormNativePointwiseJointResidual] using
      fixedP506FormNativeJointActionSolvedSuccessorResidual_p286GaugeAuxiliary_zeroSlice
        space
  have oldEquation :
      FormNativeP286GaugeAuxiliaryEquationAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField FixedConstitutiveInput point) :=
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField FixedConstitutiveInput point)).1
      oldResidualZero
  have oldIsEliminated :=
    (formNativeP286GaugeAuxiliaryEquationAtBoundary_iff_eliminated
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField FixedConstitutiveInput point)
      nondegenerate).1 oldEquation
  exact oldIsEliminated.symm

theorem fixedP506FormNativeConstitutiveAuxiliaryCoordinate_zeroSlice
    (space : StageNineSpatialPoint) :
    fixedP506FormNativeConstitutiveAuxiliaryCoordinate
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate FixedConstitutiveInput
        (canonicalCauchySlicePoint 0 space) := by
  unfold fixedP506FormNativeConstitutiveAuxiliaryCoordinate
    holonomicP286GaugeAuxiliaryCoordinate
  exact congrArg formNativeP286GaugeActualToCoordinateLinear
    (fixedP506FormNativeConstitutiveAuxiliaryField_zeroSlice space)

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary_origin :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeAuxiliary 0 =
      FixedConstitutiveInput.gaugeAuxiliary 0 := by
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary]
  rw [← canonicalCauchySlicePoint_zero_zero]
  exact
    fixedP506FormNativeConstitutiveAuxiliaryField_zeroSlice
      (0 : StageNineSpatialPoint)

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnectionCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate
        FixedP506FormNativeConstitutiveJointActionSuccessor 0 =
      0 := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnectionCoordinate_origin_zero

private theorem fixedP506FormNativeConstitutiveWrittenCurrent_pointField_zeroSlice
    (space : StageNineSpatialPoint) :
    toContinuumPointField fixedP506FormNativeConstitutiveWrittenCurrent
        (canonicalCauchySlicePoint 0 space) =
      toContinuumPointField FixedConstitutiveInput
        (canonicalCauchySlicePoint 0 space) := by
  apply StageNineContinuumPointField.ext <;> try rfl
  exact fixedP506FormNativeConstitutiveAuxiliaryField_zeroSlice space

/-! ## Downstream action-write idempotence

The constitutive write changes only the P286 auxiliary.  At the canonical
contact this field is absent from both Dirac temporal action laws.  The
already generated source/action solution therefore remains their unique
response, so recomputing those writes does not select new matter data. -/

private theorem fixedConstitutiveInput_coframe_eq_fixedActual :
    FixedConstitutiveInput.coframe = FixedP506JointActual.coframe := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_coframe,
    fixedP506JointActionSuccessor_coframe]

private theorem fixedConstitutiveInput_gravityConnection_origin_eq_fixedActual :
    FixedConstitutiveInput.gravityConnection 0 =
      FixedP506JointActual.gravityConnection 0 := by
  rw [
    fixedP506FormNativeJointActionSolvedSuccessor_gravityConnection_origin,
    fixedP506JointActionSuccessor_gravityConnection]

private theorem fixedConstitutiveInput_gaugeConnection_origin_eq_fixedActual :
    FixedConstitutiveInput.gaugeConnection 0 =
      FixedP506JointActual.gaugeConnection 0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeConnectionCoordinate FixedConstitutiveInput 0
        direction =
      holonomicP286GaugeConnectionCoordinate FixedP506JointActual 0
        direction
  rw [congrFun
      fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnectionCoordinate_origin_zero
      direction,
    congrFun fixedP506JointActual_gaugeConnectionCoordinate_origin_zero
      direction]

private theorem fixedConstitutiveInput_scalar_eq_fixedActual :
    FixedConstitutiveInput.scalar = FixedP506JointActual.scalar := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_scalar,
    fixedP506JointActionSuccessor_scalar]

private theorem fixedConstitutiveInput_matter_eq_fixedActual :
    FixedConstitutiveInput.matter = FixedP506JointActual.matter := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_matter,
    fixedP506JointActionSuccessor_matter]

private theorem fixedConstitutiveInput_conjugateMatter_eq_fixedActual :
    FixedConstitutiveInput.conjugateMatter =
      FixedP506JointActual.conjugateMatter := by
  rw [fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter,
    fixedP506JointActionSuccessor_conjugateMatter]

private theorem
    fixedConstitutiveInput_matterCovariantDerivative_origin_eq_fixedActual :
    holonomicMatterCovariantDerivative FixedConstitutiveInput 0 =
      holonomicMatterCovariantDerivative FixedP506JointActual 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [fixedConstitutiveInput_matter_eq_fixedActual,
    fixedConstitutiveInput_gravityConnection_origin_eq_fixedActual,
    fixedConstitutiveInput_gaugeConnection_origin_eq_fixedActual]

private theorem fixedConstitutiveInput_generatedMatterVector_origin_zero :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField FixedConstitutiveInput 0) =
      0 := by
  have old :=
    fixedP506JointActual_generatedContinuumMatterVector_origin_zero
  unfold generatedContinuumMatterVector at old ⊢
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart] at old ⊢
  rw [fixedConstitutiveInput_coframe_eq_fixedActual,
    fixedConstitutiveInput_matterCovariantDerivative_origin_eq_fixedActual,
    fixedConstitutiveInput_scalar_eq_fixedActual,
    fixedConstitutiveInput_matter_eq_fixedActual]
  exact old

private theorem fixedConstitutiveInput_primalActionLaw :
    HolonomicCurrentCoframeMatterTimeActionLaw FixedConstitutiveInput 0
      (holonomicMatterCovariantDerivative FixedConstitutiveInput 0
        canonicalLorentzianTimeDirection) := by
  exact
    currentCoframeActionLaw_of_generatedContinuumMatterVector_zero
      positiveSmoothUnifiedSource FixedConstitutiveInput
      fixedConstitutiveInput_generatedMatterVector_origin_zero

private theorem fixedConstitutiveInput_noncharacteristic :
    coframeTemporalPrincipalScalar (FixedConstitutiveInput.coframe 0) ≠
      0 := by
  rw [fixedConstitutiveInput_coframe_eq_fixedActual,
    fixedGlobalMatterDualP286Complete_coframe_origin]
  simp

private theorem fixedP506FormNativeConstitutiveWrittenCurrent_primalActionLaw :
    HolonomicCurrentCoframeMatterTimeActionLaw
      fixedP506FormNativeConstitutiveWrittenCurrent 0
      (holonomicMatterCovariantDerivative
        fixedP506FormNativeConstitutiveWrittenCurrent 0
        canonicalLorentzianTimeDirection) := by
  change
    HolonomicCurrentCoframeMatterTimeActionLaw FixedConstitutiveInput 0
      (holonomicMatterCovariantDerivative FixedConstitutiveInput 0
        canonicalLorentzianTimeDirection)
  exact fixedConstitutiveInput_primalActionLaw

private theorem
    fixedP506FormNativeConstitutivePrimalWrittenCurrent_eq_writtenCurrent :
    fixedP506FormNativeConstitutivePrimalWrittenCurrent =
      fixedP506FormNativeConstitutiveWrittenCurrent := by
  unfold fixedP506FormNativeConstitutivePrimalWrittenCurrent
  apply
    (actionGeneratedCurrentCoframeMatterTimeResponseActual_eq_iff
      fixedP506FormNativeConstitutiveWrittenCurrent).2
  exact
    holonomicCurrentCoframeMatterTimeActionLaw_unique
      fixedP506FormNativeConstitutiveWrittenCurrent 0
      fixedConstitutiveInput_noncharacteristic
      _ _
      fixedP506FormNativeConstitutiveWrittenCurrent_primalActionLaw
      (actionGeneratedHolonomicCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
        fixedP506FormNativeConstitutiveWrittenCurrent 0
        fixedConstitutiveInput_noncharacteristic)

private theorem fixedConstitutiveInput_adjointActionLaw :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      FixedConstitutiveInput 0
      (holonomicConjugateMatterDerivativeDual FixedConstitutiveInput 0
        canonicalLorentzianTimeDirection) := by
  have derivativeEq (direction : LorentzianIndex) :
      holonomicConjugateMatterDerivativeDual
          FixedConstitutiveInput 0 direction =
        holonomicConjugateMatterDerivativeDual
          FixedP506JointActual 0 direction := by
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rw [fixedConstitutiveInput_conjugateMatter_eq_fixedActual]
  have spatialTransportEq :
      holonomicIdentityCoframeConjugateMatterSpatialTransport
          FixedConstitutiveInput 0 =
        holonomicIdentityCoframeConjugateMatterSpatialTransport
          FixedP506JointActual 0 := by
    unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
    simp_rw [derivativeEq]
  have connectionOperatorEq :
      holonomicIdentityCoframeMatterConnectionOperator
          FixedConstitutiveInput 0 =
        holonomicIdentityCoframeMatterConnectionOperator
          FixedP506JointActual 0 := by
    funext direction
    unfold holonomicIdentityCoframeMatterConnectionOperator
    rw [fixedConstitutiveInput_gravityConnection_origin_eq_fixedActual,
      fixedConstitutiveInput_gaugeConnection_origin_eq_fixedActual]
  have algebraicOperatorEq :
      holonomicIdentityCoframeMatterAlgebraicOperator
          FixedConstitutiveInput 0 =
        holonomicIdentityCoframeMatterAlgebraicOperator
          FixedP506JointActual 0 := by
    unfold holonomicIdentityCoframeMatterAlgebraicOperator
    rw [connectionOperatorEq, fixedConstitutiveInput_scalar_eq_fixedActual]
  have law := fixedP506JointActual_adjointActionLaw
  unfold HolonomicIdentityCoframeConjugateMatterTimeActionLaw at law ⊢
  rw [derivativeEq, spatialTransportEq,
    congrFun fixedConstitutiveInput_conjugateMatter_eq_fixedActual 0,
    algebraicOperatorEq]
  exact law

private theorem
    fixedP506FormNativeConstitutiveWrittenCurrent_adjointActionLaw :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      fixedP506FormNativeConstitutiveWrittenCurrent 0
      (holonomicConjugateMatterDerivativeDual
        fixedP506FormNativeConstitutiveWrittenCurrent 0
        canonicalLorentzianTimeDirection) := by
  change
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      FixedConstitutiveInput 0
      (holonomicConjugateMatterDerivativeDual FixedConstitutiveInput 0
        canonicalLorentzianTimeDirection)
  exact fixedConstitutiveInput_adjointActionLaw

private theorem
    fixedP506FormNativeConstitutiveDualWrittenCurrent_eq_writtenCurrent :
    fixedP506FormNativeConstitutiveDualWrittenCurrent =
      fixedP506FormNativeConstitutiveWrittenCurrent := by
  unfold fixedP506FormNativeConstitutiveDualWrittenCurrent
  rw [
    fixedP506FormNativeConstitutivePrimalWrittenCurrent_eq_writtenCurrent]
  apply
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_eq_iff
      fixedP506FormNativeConstitutiveWrittenCurrent).2
  exact
    (holonomicIdentityCoframeConjugateMatterTimeActionLaw_iff
      fixedP506FormNativeConstitutiveWrittenCurrent 0 _).1
      fixedP506FormNativeConstitutiveWrittenCurrent_adjointActionLaw

theorem fixedP506FormNativeConstitutiveJointActionSuccessor_matter :
    FixedP506FormNativeConstitutiveJointActionSuccessor.matter =
      FixedConstitutiveInput.matter := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter,
    fixedP506FormNativeConstitutiveDualWrittenCurrent_eq_writtenCurrent]
  rfl

theorem fixedP506FormNativeConstitutiveJointActionSuccessor_conjugateMatter :
    FixedP506FormNativeConstitutiveJointActionSuccessor.conjugateMatter =
      FixedConstitutiveInput.conjugateMatter := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    fixedP506FormNativeConstitutiveDualWrittenCurrent_eq_writtenCurrent]
  rfl

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_gravityConnection_origin :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gravityConnection 0 =
      FixedConstitutiveInput.gravityConnection 0 := by
  rw [FixedP506FormNativeConstitutiveJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero,
    fixedP506FormNativeConstitutiveDualWrittenCurrent_eq_writtenCurrent]
  rfl

/-- Internally generated EC curvature target of the same constitutive write.
It is exposed only as producer provenance for the resulting normalized-affine
gravity connection; no residual coordinate enters this definition. -/
def fixedP506FormNativeConstitutiveGravityCurvatureTarget :
    PhysicalBivector :=
  sourceActionGeneratedDiracDualECFullCauchyCurvatureTarget
    positiveSmoothUnifiedSource
    fixedP506FormNativeConstitutiveDualWrittenCurrent

/-- Explicit global normal form of the gravity connection carried by the
constitutive successor.  Its origin is read from that same successor, while
its target is generated by the authoritative EC action write above. -/
theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_gravityConnection_normalForm :
    FixedP506FormNativeConstitutiveJointActionSuccessor.gravityConnection =
      normalizedAffineLorentzConnectionField
        (FixedP506FormNativeConstitutiveJointActionSuccessor.gravityConnection
          0)
        fixedP506FormNativeConstitutiveGravityCurvatureTarget := by
  have generated :=
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_eq_normalizedAffine
      positiveSmoothUnifiedSource
      fixedP506FormNativeConstitutiveDualWrittenCurrent
  unfold FixedP506FormNativeConstitutiveJointActionSuccessor
    fixedP506FormNativeConstitutiveGravityCurvatureTarget
  rw [generated, normalizedAffineLorentzConnectionField_zero]

private theorem
    fixedP506FormNativeConstitutiveDualWrittenCurrent_coframe_origin_one :
    fixedP506FormNativeConstitutiveDualWrittenCurrent.coframe 0 = 1 := by
  rw [fixedP506FormNativeConstitutiveDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_coframe,
    fixedP506FormNativeConstitutivePrimalWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_coframe]
  change FixedConstitutiveInput.coframe 0 = 1
  rw [← canonicalCauchySlicePoint_zero_zero]
  exact
    fixedP506FormNativeJointActionSolvedSuccessor_coframe_zeroSlice
      (0 : StageNineSpatialPoint)

/-! ## Downstream constitutive acceptance -/

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_curvature
    (point : BasePoint) :
    holonomicGaugeCurvature
        FixedP506FormNativeConstitutiveJointActionSuccessor point =
      holonomicGaugeCurvature FixedConstitutiveInput point :=
  holonomicGaugeCurvature_eq_of_connection_eq_current
    FixedP506FormNativeConstitutiveJointActionSuccessor
    FixedConstitutiveInput
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeConnection
    point

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_curvatureCoordinate
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        FixedP506FormNativeConstitutiveJointActionSuccessor point =
      holonomicP286GaugeCurvatureCoordinate FixedConstitutiveInput point := by
  unfold holonomicP286GaugeCurvatureCoordinate
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_curvature]

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_auxiliaryCoordinate
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        FixedP506FormNativeConstitutiveJointActionSuccessor point =
      fixedP506FormNativeConstitutiveAuxiliaryCoordinate point := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary]
  rfl

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessor_p286AuxiliaryEquation
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
        (FixedP506FormNativeConstitutiveJointActionSuccessor.coframe point) ≠
        0) :
    holonomicGaugeCurvature
        FixedP506FormNativeConstitutiveJointActionSuccessor point =
      formNativeP286BlockwiseConstitutive
        (FixedP506FormNativeConstitutiveJointActionSuccessor.coframe point)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).weakCouplingSquared : ℝ)
        ((sourceGeneratedUnifiedCouplings
          positiveSmoothUnifiedSource).hyperchargeCouplingSquared : ℝ)
        (FixedP506FormNativeConstitutiveJointActionSuccessor.gaugeAuxiliary
          point) := by
  rw [
    fixedP506FormNativeConstitutiveJointActionSuccessor_curvature,
    fixedP506FormNativeConstitutiveJointActionSuccessor_coframe,
    fixedP506FormNativeConstitutiveJointActionSuccessor_gaugeAuxiliary]
  exact
    (formNativeP286GaugeEliminatedAuxiliaryAtBoundary_solves
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (FixedConstitutiveInput.coframe point)
      (by
        simpa only [
          fixedP506FormNativeConstitutiveJointActionSuccessor_coframe] using
          nondegenerate)
      (holonomicGaugeCurvature FixedConstitutiveInput point)).symm

/-- Complete repaired-root residual section of the action-generated common
successor.  It is defined only after the successor exists. -/
def fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection :
    BasePoint → DiracDualFormNativePointwiseJointResidualCarrier :=
  diracDualFormNativeJointResidualSection positiveSmoothUnifiedSource
    FixedP506FormNativeConstitutiveJointActionSuccessor

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
    (point : BasePoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection point
      ).gravityMultiplier =
      0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor point) =
      0
  rw [formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity]
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_simplicity
      positiveSmoothUnifiedSource
      fixedP506FormNativeConstitutiveDualWrittenCurrent point

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
    (point : BasePoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection point
      ).gravityAuxiliary =
      0 := by
  have equation :
      FormNativeGravityAuxiliaryEquation
        FixedP506FormNativeConstitutiveJointActionSuccessor := by
    unfold FixedP506FormNativeConstitutiveJointActionSuccessor
    exact
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_auxiliaryEquation
        positiveSmoothUnifiedSource
        fixedP506FormNativeConstitutiveDualWrittenCurrent
  exact congrFun equation point

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zero
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
        (FixedP506FormNativeConstitutiveJointActionSuccessor.coframe point) ≠
        0) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection point
      ).p286GaugeAuxiliary =
      0 := by
  change
    formNativeP286GaugeAuxiliaryEulerResidualAtBoundary
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor point) =
      0
  apply
    (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff
      (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
      (toContinuumPointField
        FixedP506FormNativeConstitutiveJointActionSuccessor point)).2
  exact
    fixedP506FormNativeConstitutiveJointActionSuccessor_p286AuxiliaryEquation
      point nondegenerate

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_coframe_origin_zero :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection 0
      ).coframe =
      0 := by
  change
    diracDualFormNativeCoframeEulerCovector positiveSmoothUnifiedSource 0
        (toContinuumPointField
          FixedP506FormNativeConstitutiveJointActionSuccessor 0) =
      0
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_fullCoframeEuler_zero
      positiveSmoothUnifiedSource
      fixedP506FormNativeConstitutiveDualWrittenCurrent
      fixedP506FormNativeConstitutiveDualWrittenCurrent_coframe_origin_one

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_algebraic_zero
    (point : BasePoint)
    (nondegenerate :
      Matrix.det
        (FixedP506FormNativeConstitutiveJointActionSuccessor.coframe point) ≠
        0) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection point
        ).gravityMultiplier = 0 ∧
      (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection point
        ).gravityAuxiliary = 0 ∧
      (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection point
        ).p286GaugeAuxiliary = 0 := by
  exact
    ⟨fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityMultiplier_zero
        point,
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_gravityAuxiliary_zero
        point,
      fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zero
        point nondegenerate⟩

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
      (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary =
      0 := by
  apply
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_p286GaugeAuxiliary_zero
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
  norm_num

theorem
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_algebraic_zeroSlice
    (space : StageNineSpatialPoint) :
    (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space)).gravityMultiplier = 0 ∧
      (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space)).gravityAuxiliary = 0 ∧
      (fixedP506FormNativeConstitutiveJointActionSuccessorResidualSection
        (canonicalCauchySlicePoint 0 space)).p286GaugeAuxiliary = 0 := by
  apply
    fixedP506FormNativeConstitutiveJointActionSuccessorResidual_algebraic_zero
  rw [fixedP506FormNativeConstitutiveJointActionSuccessor_coframe_zeroSlice]
  norm_num

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionConstitutiveSuccessor

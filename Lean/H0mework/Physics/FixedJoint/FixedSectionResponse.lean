import H0mework.Physics.FixedJoint.FixedSectionResidual

/-!
# Fixed P506/L0 section-level joint action response

The preceding module computes the complete residual section of the first
form-native action successor.  This module does not consume that residual.
Instead it continues the already generated action path:

```text
same fixed P506/L0 source and current
  -> form-native BF velocity and Gauss charge
  -> their canonical temporal plus radial connection second jet
  -> current-owned primal and adjoint matter writes
  -> repaired-root full Einstein--Cartan recomputation
  -> one common holonomic successor.
```

The public successor has no residual, support, endpoint, inverse image,
branch, response value, coefficient, or equation receipt argument.  The
second-jet coefficients are the existing source coupling and the two unique
action responses.  Residual substitution is downstream producer-consistency
only.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionSectionResponse

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineCurrentCoframeMatterTimeResponse
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCurrentCoframeMatterTimeResponseActualLift
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualP286CompleteActual
open StageNineDiracDualFormNativeFixedP506JointActionSectionResidual
open StageNineDiracDualFormNativeFixedP506JointActionWrite
open StageNineDiracDualFormNativeFixedP506JointActionZeroFiber
open StageNineDiracDualFormNativeFixedP506JointResidual
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineGravityBianchi
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineIdentityCoframeConjugateMatterTimeResponseActualLift
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286ColorCartanQuadraticConnectionJet
open StageNineP286GaugeAuxiliaryVariation
open StageNineP286GaugeConnectionVariation
open StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaussRadialSecondJetLift
open StageNineP286HolonomicSecondJetCarrier
open StageNineP286HolonomicSecondJetCurvatureSymbol
open StageNineP286TemporalVelocitySecondJetLift
open StageNineSourceActionGeneratedP286GaussJointLocalActualLift
open StageNineSourceActionGeneratedP286MomentumJointLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteResponseLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullSynchronizedActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286CompleteActionPrincipalFullNonlinearLocalActualLift
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

local instance sectionResponseP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance sectionResponseP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

local instance sectionResponseP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

abbrev fixedP506FormNativeStrongCouplingSquared : ℝ :=
  ((sourceGeneratedUnifiedCouplings
    positiveSmoothUnifiedSource).strongCouplingSquared : ℝ)

/-! ## Forward action-owned connection response -/

/-- Temporal Hessian forced by the already generated BF velocity. -/
def fixedP506FormNativeTemporalVelocitySecondJet :
    P286HolonomicConnectionSecondJet :=
  p286TemporalVelocityActionSecondJet
    fixedP506FormNativeStrongCouplingSquared
    fixedP506FormNativeP286SpatialAuxiliaryVelocity

/-- Spatial Hessian forced by the already generated Gauss charge. -/
def fixedP506FormNativeGaussRadialSecondJet :
    P286HolonomicConnectionSecondJet :=
  p286GaussRadialActionSecondJet
    fixedP506FormNativeStrongCouplingSquared
    fixedP506FormNativeP286GaussCharge

/-- The two independent action sectors are assembled before installation.
There is no fieldwise residual correction between them. -/
def fixedP506FormNativeCompleteActionSecondJet :
    P286HolonomicConnectionSecondJet :=
  fixedP506FormNativeTemporalVelocitySecondJet +
    fixedP506FormNativeGaussRadialSecondJet

theorem fixedP506FormNativeCompleteActionSecondJet_timeResponse :
    p286HolonomicSecondJetCurvatureSymbol
        fixedP506FormNativeCompleteActionSecondJet
        canonicalLorentzianTimeDirection =
      liftGaugeTwoFormOperator
        (fixedP506FormNativeStrongCouplingSquared •
          coframeGaugeSpacetimeHodgeLinear 1)
        (p286SpatialAuxiliaryVelocityEmbedding
          fixedP506FormNativeP286SpatialAuxiliaryVelocity) := by
  rw [fixedP506FormNativeCompleteActionSecondJet, map_add]
  simp only [Pi.add_apply]
  rw [fixedP506FormNativeTemporalVelocitySecondJet,
    p286TemporalVelocityActionSecondJet_curvatureSymbol_time]
  change
    liftGaugeTwoFormOperator
          (fixedP506FormNativeStrongCouplingSquared •
            coframeGaugeSpacetimeHodgeLinear 1)
          (p286SpatialAuxiliaryVelocityEmbedding
            fixedP506FormNativeP286SpatialAuxiliaryVelocity) +
        p286HolonomicSecondJetCurvatureSymbol
          (p286GaussRadialActionSecondJet
            fixedP506FormNativeStrongCouplingSquared
            fixedP506FormNativeP286GaussCharge)
          canonicalLorentzianTimeDirection =
      _
  rw [p286GaussRadialActionSecondJet_curvatureSymbol_time, add_zero]

theorem fixedP506FormNativeCompleteActionSecondJet_spatialResponse
    (axis : Fin 3) :
    p286HolonomicSecondJetCurvatureSymbol
        fixedP506FormNativeCompleteActionSecondJet axis.succ =
      liftGaugeTwoFormOperator
        (fixedP506FormNativeStrongCouplingSquared •
          coframeGaugeSpacetimeHodgeLinear 1)
        (fieldDirectionalDerivative
          (p286GaussRadialAuxiliaryProfile
            fixedP506FormNativeP286GaussCharge)
          0 axis.succ) := by
  rw [fixedP506FormNativeCompleteActionSecondJet, map_add]
  simp only [Pi.add_apply]
  rw [fixedP506FormNativeTemporalVelocitySecondJet,
    p286TemporalVelocityActionSecondJet_curvatureSymbol_spatial,
    zero_add]
  exact
    p286GaussRadialActionSecondJet_curvatureSymbol_eq_auxiliaryFirstJet
      fixedP506FormNativeStrongCouplingSquared
      fixedP506FormNativeP286GaussCharge axis

theorem fixedP506FormNativeCompleteActionSecondJet_eq_neg_sourceJet :
    fixedP506FormNativeCompleteActionSecondJet =
      (-1 : ℝ) •
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet := by
  have spatialFormNeg :
      StageNineP286ActionCanonicalPairUpdate.canonicalP286SpatialGaugeOneForm
          (-positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity) =
        -StageNineP286ActionCanonicalPairUpdate.canonicalP286SpatialGaugeOneForm
          positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity := by
    funext direction
    refine Fin.cases ?_ (fun _ => ?_) direction <;>
      simp [StageNineP286ActionCanonicalPairUpdate.canonicalP286SpatialGaugeOneForm]
  have temporalFormNeg :
      p286TemporalGaugeOneForm
          (-positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge) =
        -p286TemporalGaugeOneForm
          positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge := by
    funext direction
    by_cases directionTime :
        direction = canonicalLorentzianTimeDirection
    · subst direction
      simp
    · simp [p286TemporalGaugeOneForm, directionTime]
  apply Subtype.ext
  change
    p286TemporalVelocityActionSecondJetAmbient
          fixedP506FormNativeStrongCouplingSquared
          fixedP506FormNativeP286SpatialAuxiliaryVelocity +
        p286GaussRadialActionSecondJetAmbient
          fixedP506FormNativeStrongCouplingSquared
          fixedP506FormNativeP286GaussCharge =
      (-1 : ℝ) •
        (p286TemporalVelocityActionSecondJetAmbient
            fixedP506FormNativeStrongCouplingSquared
            positiveP506MatterCurrentP286NonzeroCurvatureSpatialAuxiliaryVelocity +
          p286GaussRadialActionSecondJetAmbient
            fixedP506FormNativeStrongCouplingSquared
            positiveP506MatterCurrentP286NonzeroCurvatureGaussCharge)
  rw [fixedP506FormNativeSpatialVelocity_eq_neg_U7,
    fixedP506FormNativeGaussCharge_eq_neg_U7]
  apply ContinuousLinearMap.ext
  intro first
  apply ContinuousLinearMap.ext
  intro second
  funext direction
  simp only [p286TemporalVelocityActionSecondJetAmbient,
    p286GaussRadialActionSecondJetAmbient]
  rw [spatialFormNeg, temporalFormNeg]
  simp [ContinuousLinearMap.smulRight_apply]

theorem
    fixedP506FormNativeCompleteActionSecondJet_realization_eq_neg_sourceJet
    (point : BasePoint) :
    p286HolonomicSecondJetQuadraticRealization
        fixedP506FormNativeCompleteActionSecondJet point =
      -p286HolonomicSecondJetQuadraticRealization
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet point := by
  rw [fixedP506FormNativeCompleteActionSecondJet_eq_neg_sourceJet, map_smul]
  simp

theorem
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet_realization_neg_point
    (point : BasePoint) :
    p286HolonomicSecondJetQuadraticRealization
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet (-point) =
      p286HolonomicSecondJetQuadraticRealization
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet point := by
  simp [p286HolonomicSecondJetQuadraticRealization_apply]

theorem c3h181U7ConnectionNormalForm_neg (point : BasePoint) :
    c3h181U7ConnectionNormalForm (-point) =
      -c3h181U7ConnectionNormalForm point := by
  funext direction
  by_cases directionOne : direction = 1
  · subst direction
    simp [c3h181U7ConnectionNormalForm]
  · simp [c3h181U7ConnectionNormalForm, directionOne]

/-! ## One public joint successor -/

/-- Internal P286 leg: install the action-owned Hessian on the same actual
that already carries the action-owned auxiliary field. -/
private def fixedP506FormNativeP286ActionWrittenCurrent :
    StageNineHolonomicConfiguration :=
  installP286HolonomicConnectionSecondJet
    FixedP506JointActionSuccessor
    fixedP506FormNativeCompleteActionSecondJet 1

/-- Recompute the primal response after both primitive P286 fields changed. -/
private def fixedP506FormNativePrimalMatterWrittenCurrent :
    StageNineHolonomicConfiguration :=
  actionGeneratedCurrentCoframeMatterTimeResponseActual
    fixedP506FormNativeP286ActionWrittenCurrent

/-- Recompute the independent adjoint response on that same live current. -/
private def fixedP506FormNativeMatterDualWrittenCurrent :
    StageNineHolonomicConfiguration :=
  actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
    fixedP506FormNativePrimalMatterWrittenCurrent

/-- One common source/action-generated successor.  All internal response legs
are hidden and deterministic; callers supply only the already fixed source
lineage/current embodied by this specialization. -/
def FixedP506FormNativeJointActionSuccessor :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    positiveSmoothUnifiedSource fixedP506FormNativeMatterDualWrittenCurrent

theorem fixedP506FormNativeJointActionSuccessor_gaugeConnection :
    FixedP506FormNativeJointActionSuccessor.gaugeConnection =
      fixedP506FormNativeP286ActionWrittenCurrent.gaugeConnection := by
  rw [FixedP506FormNativeJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection,
    fixedP506FormNativeMatterDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gaugeConnection,
    fixedP506FormNativePrimalMatterWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gaugeConnection]

/-- Public action-provenance seam for the P286 primitive field.  The right
side is the forward second-jet installer itself, not a residual correction. -/
theorem fixedP506FormNativeJointActionSuccessor_gaugeConnection_actionWrite :
    FixedP506FormNativeJointActionSuccessor.gaugeConnection =
      (installP286HolonomicConnectionSecondJet
        FixedP506JointActionSuccessor
        fixedP506FormNativeCompleteActionSecondJet 1).gaugeConnection := by
  exact fixedP506FormNativeJointActionSuccessor_gaugeConnection

theorem fixedP506FormNativeJointActionSuccessor_gaugeAuxiliary :
    FixedP506FormNativeJointActionSuccessor.gaugeAuxiliary =
      FixedP506JointActionSuccessor.gaugeAuxiliary := by
  rw [FixedP506FormNativeJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary,
    fixedP506FormNativeMatterDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gaugeAuxiliary,
    fixedP506FormNativePrimalMatterWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gaugeAuxiliary]
  rfl

theorem fixedP506FormNativeJointActionSuccessor_coframe :
    FixedP506FormNativeJointActionSuccessor.coframe =
      FixedP506JointActionSuccessor.coframe := by
  rw [FixedP506FormNativeJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    fixedP506FormNativeMatterDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_coframe,
    fixedP506FormNativePrimalMatterWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_coframe]
  rfl

theorem fixedP506FormNativeJointActionSuccessor_scalar :
    FixedP506FormNativeJointActionSuccessor.scalar =
      FixedP506JointActionSuccessor.scalar := by
  rw [FixedP506FormNativeJointActionSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar,
    fixedP506FormNativeMatterDualWrittenCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_scalar,
    fixedP506FormNativePrimalMatterWrittenCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_scalar]
  rfl

theorem fixedP506FormNativeJointActionSuccessor_smooth :
    FixedP506FormNativeJointActionSuccessor.Smooth := by
  have p286Smooth :
      fixedP506FormNativeP286ActionWrittenCurrent.Smooth := by
    exact
      installP286HolonomicConnectionSecondJet_smooth
        FixedP506JointActionSuccessor
        fixedP506JointActionSuccessor_smooth
        fixedP506FormNativeCompleteActionSecondJet 1
  have primalSmooth :
      fixedP506FormNativePrimalMatterWrittenCurrent.Smooth :=
    actionGeneratedCurrentCoframeMatterTimeResponseActual_smooth
      fixedP506FormNativeP286ActionWrittenCurrent p286Smooth
  have dualSmooth :
      fixedP506FormNativeMatterDualWrittenCurrent.Smooth :=
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_smooth
      fixedP506FormNativePrimalMatterWrittenCurrent primalSmooth
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_smooth
      positiveSmoothUnifiedSource fixedP506FormNativeMatterDualWrittenCurrent
      dualSmooth

theorem fixedP506FormNativeJointActionSuccessor_exactLineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506JointActionSuccessor_exactLineage

/-! ## Canonical primitive restart

The additive current response above is useful for read-after-write auditing,
but the action equation determines a total primitive connection, not an
instruction to accumulate an already installed radial response.  The fixed
P506/L0 lineage already owns the canonical constant-curvature primitive.
The next producer restarts from that source-owned primitive, installs the
current form-native Hessian once, and only then recomputes matter and EC.

This is still forward action generation.  The constructor below accepts no
residual or support coordinate and does not negate an observed mismatch.
-/

/-- Same-lineage canonical P286 primitive with the current action Hessian
installed exactly once. -/
private def fixedP506FormNativeP286SolvedReferenceActual :
    StageNineHolonomicConfiguration :=
  installP286HolonomicConnectionSecondJet
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
    fixedP506FormNativeCompleteActionSecondJet 1

/-- Graft only that action-generated primitive connection into the current
whole configuration.  All other fields remain the single form-native current
that generated the Hessian. -/
private def fixedP506FormNativeP286SolvedCurrent :
    StageNineHolonomicConfiguration :=
  { FixedP506JointActionSuccessor with
    gaugeConnection :=
      fixedP506FormNativeP286SolvedReferenceActual.gaugeConnection }

private def fixedP506FormNativeSolvedPrimalMatterCurrent :
    StageNineHolonomicConfiguration :=
  actionGeneratedCurrentCoframeMatterTimeResponseActual
    fixedP506FormNativeP286SolvedCurrent

private def fixedP506FormNativeSolvedMatterDualCurrent :
    StageNineHolonomicConfiguration :=
  actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual
    fixedP506FormNativeSolvedPrimalMatterCurrent

/-- The canonical same-source joint action successor after primitive restart.
The public mouth remains proof-free and branch-free. -/
def FixedP506FormNativeJointActionSolvedSuccessor :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualECFullCauchyLocalActualLift
    positiveSmoothUnifiedSource fixedP506FormNativeSolvedMatterDualCurrent

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnection_actionWrite :
    FixedP506FormNativeJointActionSolvedSuccessor.gaugeConnection =
      (installP286HolonomicConnectionSecondJet
        positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
        fixedP506FormNativeCompleteActionSecondJet 1).gaugeConnection := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeConnection,
    fixedP506FormNativeSolvedMatterDualCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gaugeConnection,
    fixedP506FormNativeSolvedPrimalMatterCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gaugeConnection]
  rfl

/-- Explicit whole-space connection produced by the canonical primitive
restart.  It is the parity-reflected old complete action normal form because
the new action Hessian is its source-owned negative. -/
def fixedP506FormNativeJointActionSolvedConnectionNormalForm
    (point : BasePoint) : P286GaugeOneForm :=
  -c3h181FullConnectionNormalForm (-point)

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_connection_normalForm
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        FixedP506FormNativeJointActionSolvedSuccessor point =
      fixedP506FormNativeJointActionSolvedConnectionNormalForm point := by
  unfold holonomicP286GaugeConnectionCoordinate
  rw [
    fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnection_actionWrite]
  change
    holonomicP286GaugeConnectionCoordinate
        (installP286HolonomicConnectionSecondJet
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          fixedP506FormNativeCompleteActionSecondJet 1)
        point =
      fixedP506FormNativeJointActionSolvedConnectionNormalForm point
  unfold installP286HolonomicConnectionSecondJet
  rw [holonomicP286GaugeConnectionCoordinate_vary]
  simp only [one_smul]
  rw [
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm,
    fixedP506FormNativeCompleteActionSecondJet_realization_eq_neg_sourceJet]
  unfold fixedP506FormNativeJointActionSolvedConnectionNormalForm
    c3h181FullConnectionNormalForm
  rw [c3h181U7ConnectionNormalForm_neg,
    positiveP506MatterCurrentCompleteActionPrincipalSecondJet_realization_neg_point]
  abel

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_connection_eq_neg_source_neg_point
    (point : BasePoint) :
    holonomicP286GaugeConnectionCoordinate
        FixedP506FormNativeJointActionSolvedSuccessor point =
      -holonomicP286GaugeConnectionCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        (-point) := by
  rw [
    fixedP506FormNativeJointActionSolvedSuccessor_connection_normalForm,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connection_normalForm]
  rfl

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_connectionDerivative_eq_source_neg_point
    (point : BasePoint)
    (derivativeDirection formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        FixedP506FormNativeJointActionSolvedSuccessor
        point derivativeDirection formDirection =
      p286GaugeConnectionCoordinateDerivative
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        (-point) derivativeDirection formDirection := by
  rw [
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_normalForm]
  have finalFunctionEquality :
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate
          FixedP506FormNativeJointActionSolvedSuccessor
          candidate formDirection) =
        fun candidate =>
          holonomicP286GaugeConnectionCoordinate
            (installP286HolonomicConnectionSecondJet
              positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
              fixedP506FormNativeCompleteActionSecondJet 1)
            candidate formDirection := by
    funext candidate
    unfold holonomicP286GaugeConnectionCoordinate
    rw [
      fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnection_actionWrite]
  unfold p286GaugeConnectionCoordinateDerivative
  rw [finalFunctionEquality]
  change
    p286GaugeConnectionCoordinateDerivative
        (installP286HolonomicConnectionSecondJet
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          fixedP506FormNativeCompleteActionSecondJet 1)
        point derivativeDirection formDirection =
      c3h181U7ConnectionLinear
          (coordinateDirection derivativeDirection) formDirection +
        positiveP506MatterCurrentCompleteActionPrincipalSecondJet.1
          (-point) (coordinateDirection derivativeDirection) formDirection
  unfold installP286HolonomicConnectionSecondJet
  rw [
    p286GaugeConnectionCoordinateDerivative_vary_of_contDiff
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
      positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_smooth
      (p286HolonomicSecondJetQuadraticRealization
        fixedP506FormNativeCompleteActionSecondJet)
      (p286HolonomicSecondJetQuadraticRealization_contDiff
        fixedP506FormNativeCompleteActionSecondJet),
    p286HolonomicSecondJetQuadraticRealization_variationDerivative]
  simp only [one_smul]
  have backgroundFunctionEquality :
      (fun candidate =>
        holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
          candidate formDirection) =
        fun candidate =>
          c3h181U7ConnectionNormalForm candidate formDirection := by
    funext candidate
    exact congrFun
      (positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm
        candidate) formDirection
  unfold p286GaugeConnectionCoordinateDerivative
  rw [backgroundFunctionEquality,
    c3h181U7ConnectionNormalForm_component_directionalDerivative,
    fixedP506FormNativeCompleteActionSecondJet_eq_neg_sourceJet]
  simp

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_connectionDerivative_diagonal_zero
    (direction : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        FixedP506FormNativeJointActionSolvedSuccessor
        0 direction direction =
      0 := by
  rw [
    fixedP506FormNativeJointActionSolvedSuccessor_connectionDerivative_eq_source_neg_point]
  simpa using
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_diagonal_zero
      direction

/-- The action-written P286 connection has no spatial first jet at the fixed
origin.  This is the full three-by-four source-generated statement, not only
the diagonal readout used by the constitutive zero fiber. -/
theorem
    fixedP506FormNativeJointActionSolvedSuccessor_connectionSpatialOneJet_zero
    (axis : Fin 3) (formDirection : LorentzianIndex) :
    p286GaugeConnectionCoordinateDerivative
        FixedP506FormNativeJointActionSolvedSuccessor
        0 axis.succ formDirection =
      0 := by
  rw [
    fixedP506FormNativeJointActionSolvedSuccessor_connectionDerivative_eq_source_neg_point,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionDerivative_normalForm]
  fin_cases axis <;> fin_cases formDirection <;>
    simp [c3h181U7ConnectionLinear,
      positiveP506MatterCurrentCompleteActionPrincipalSecondJet,
      positiveActionGeneratedTemporalVelocityP286SecondJet,
      positiveActionGeneratedGaussRadialP286SecondJet,
      p286TemporalVelocityActionSecondJet,
      p286TemporalVelocityActionSecondJetAmbient,
      p286GaussRadialActionSecondJet,
      p286GaussRadialActionSecondJetAmbient,
      ContinuousLinearMap.smulRight_apply,
      coordinateDirection, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

private theorem p286CoordinateLieBracket_neg_neg
    (first second : P286CoordinateCarrier) :
    p286CoordinateLieBracket (-first) (-second) =
      p286CoordinateLieBracket first second := by
  rw [← neg_one_smul ℝ first, ← neg_one_smul ℝ second]
  rw [p286CoordinateLieBracket_smul_left,
    p286CoordinateLieBracket_smul_right]
  module

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_eq_source_neg_point
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        FixedP506FormNativeJointActionSolvedSuccessor point =
      holonomicP286GaugeCurvatureCoordinate
        positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
        (-point) := by
  funext pair
  rw [
    holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket
      FixedP506FormNativeJointActionSolvedSuccessor point pair,
    holonomicP286GaugeCurvatureCoordinate_eq_derivative_bracket
      positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
      (-point) pair,
    fixedP506FormNativeJointActionSolvedSuccessor_connectionDerivative_eq_source_neg_point,
    fixedP506FormNativeJointActionSolvedSuccessor_connectionDerivative_eq_source_neg_point]
  have firstConnection :
      holonomicP286GaugeConnectionCoordinate
          FixedP506FormNativeJointActionSolvedSuccessor
          point (pairFirst pair) =
        -holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          (-point) (pairFirst pair) :=
    congrFun
      (fixedP506FormNativeJointActionSolvedSuccessor_connection_eq_neg_source_neg_point
        point)
      (pairFirst pair)
  have secondConnection :
      holonomicP286GaugeConnectionCoordinate
          FixedP506FormNativeJointActionSolvedSuccessor
          point (pairSecond pair) =
        -holonomicP286GaugeConnectionCoordinate
          positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual
          (-point) (pairSecond pair) :=
    congrFun
      (fixedP506FormNativeJointActionSolvedSuccessor_connection_eq_neg_source_neg_point
        point)
      (pairSecond pair)
  rw [firstConnection, secondConnection, p286CoordinateLieBracket_neg_neg]

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeCurvatureCoordinate
        FixedP506FormNativeJointActionSolvedSuccessor point =
      c3h181FullCurvatureCoordinateNormalForm (-point) := by
  rw [
    fixedP506FormNativeJointActionSolvedSuccessor_curvatureCoordinate_eq_source_neg_point,
    positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_curvatureCoordinate_normalForm]

theorem fixedP506FormNativeJointActionSolvedSuccessor_gaugeAuxiliary :
    FixedP506FormNativeJointActionSolvedSuccessor.gaugeAuxiliary =
      FixedP506JointActionSuccessor.gaugeAuxiliary := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_gaugeAuxiliary,
    fixedP506FormNativeSolvedMatterDualCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gaugeAuxiliary,
    fixedP506FormNativeSolvedPrimalMatterCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gaugeAuxiliary]
  rfl

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_auxiliaryCoordinate_normalForm
    (point : BasePoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        FixedP506FormNativeJointActionSolvedSuccessor point =
      c3h181FullAuxiliaryCoordinateNormalForm (-point) := by
  unfold holonomicP286GaugeAuxiliaryCoordinate
  rw [fixedP506FormNativeJointActionSolvedSuccessor_gaugeAuxiliary]
  change
    holonomicP286GaugeAuxiliaryCoordinate
        FixedP506JointActionSuccessor point =
      c3h181FullAuxiliaryCoordinateNormalForm (-point)
  rw [fixedP506JointActionSuccessor_auxiliaryCoordinate,
    fixedP506FormNativeJointActionAuxiliaryCoordinate_normalForm]
  rfl

theorem fixedP506FormNativeJointActionSolvedSuccessor_coframe :
    FixedP506FormNativeJointActionSolvedSuccessor.coframe =
      FixedP506JointActionSuccessor.coframe := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_coframe,
    fixedP506FormNativeSolvedMatterDualCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_coframe,
    fixedP506FormNativeSolvedPrimalMatterCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_coframe]
  rfl

theorem fixedP506FormNativeJointActionSolvedSuccessor_scalar :
    FixedP506FormNativeJointActionSolvedSuccessor.scalar =
      FixedP506JointActionSuccessor.scalar := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_scalar,
    fixedP506FormNativeSolvedMatterDualCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_scalar,
    fixedP506FormNativeSolvedPrimalMatterCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_scalar]
  rfl

theorem fixedP506FormNativeJointActionSolvedSuccessor_matter_origin :
    FixedP506FormNativeJointActionSolvedSuccessor.matter 0 =
      FixedP506JointActionSuccessor.matter 0 := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter,
    fixedP506FormNativeSolvedMatterDualCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_matter,
    fixedP506FormNativeSolvedPrimalMatterCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_matter_origin]
  rfl

theorem fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter_origin :
    FixedP506FormNativeJointActionSolvedSuccessor.conjugateMatter 0 =
      FixedP506JointActionSuccessor.conjugateMatter 0 := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    fixedP506FormNativeSolvedMatterDualCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_conjugateMatter_origin,
    fixedP506FormNativeSolvedPrimalMatterCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_conjugateMatter]
  rfl

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_gaugeConnectionCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate
        FixedP506FormNativeJointActionSolvedSuccessor 0 =
      0 := by
  funext direction
  rw [congrFun
    (fixedP506FormNativeJointActionSolvedSuccessor_connection_eq_neg_source_neg_point
      0)
    direction]
  simpa using congrArg Neg.neg
    (positiveP506MatterCurrentCompleteActionPrincipalFullSynchronizedActual_connectionCoordinate_origin_zero
      direction)

theorem fixedP506FormNativeP286SolvedReferenceActual_smooth :
    fixedP506FormNativeP286SolvedReferenceActual.Smooth :=
  installP286HolonomicConnectionSecondJet_smooth
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_smooth
    fixedP506FormNativeCompleteActionSecondJet 1

private theorem fixedP506FormNativeP286SolvedCurrent_smooth :
    fixedP506FormNativeP286SolvedCurrent.Smooth := by
  rcases fixedP506JointActionSuccessor_smooth with
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, _, gaugeAuxiliarySmooth, scalarSmooth,
      matterSmooth, conjugateMatterSmooth⟩
  rcases fixedP506FormNativeP286SolvedReferenceActual_smooth with
    ⟨_, _, _, _, gaugeConnectionSmooth, _, _, _, _⟩
  exact
    ⟨coframeSmooth, gravityConnectionSmooth, gravityAuxiliarySmooth,
      gravityMultiplierSmooth, gaugeConnectionSmooth, gaugeAuxiliarySmooth,
      scalarSmooth, matterSmooth, conjugateMatterSmooth⟩

private theorem fixedP506FormNativeP286SolvedCurrent_coframe_eq_fixedActual :
    fixedP506FormNativeP286SolvedCurrent.coframe =
      FixedP506JointActual.coframe := by
  change FixedP506JointActionSuccessor.coframe =
    FixedP506JointActual.coframe
  exact fixedP506JointActionSuccessor_coframe

private theorem
    fixedP506FormNativeP286SolvedCurrent_gravityConnection_eq_fixedActual :
    fixedP506FormNativeP286SolvedCurrent.gravityConnection =
      FixedP506JointActual.gravityConnection := by
  change FixedP506JointActionSuccessor.gravityConnection =
    FixedP506JointActual.gravityConnection
  exact fixedP506JointActionSuccessor_gravityConnection

private theorem fixedP506FormNativeP286SolvedCurrent_scalar_eq_fixedActual :
    fixedP506FormNativeP286SolvedCurrent.scalar =
      FixedP506JointActual.scalar := by
  change FixedP506JointActionSuccessor.scalar = FixedP506JointActual.scalar
  exact fixedP506JointActionSuccessor_scalar

private theorem fixedP506FormNativeP286SolvedCurrent_matter_eq_fixedActual :
    fixedP506FormNativeP286SolvedCurrent.matter =
      FixedP506JointActual.matter := by
  change FixedP506JointActionSuccessor.matter = FixedP506JointActual.matter
  exact fixedP506JointActionSuccessor_matter

private theorem
    fixedP506FormNativeP286SolvedCurrent_conjugateMatter_eq_fixedActual :
    fixedP506FormNativeP286SolvedCurrent.conjugateMatter =
      FixedP506JointActual.conjugateMatter := by
  change
    FixedP506JointActionSuccessor.conjugateMatter =
      FixedP506JointActual.conjugateMatter
  exact fixedP506JointActionSuccessor_conjugateMatter

private theorem
    fixedP506FormNativeP286SolvedCurrent_gaugeConnectionCoordinate_origin_zero :
    holonomicP286GaugeConnectionCoordinate
        fixedP506FormNativeP286SolvedCurrent 0 =
      0 := by
  change
    holonomicP286GaugeConnectionCoordinate
        fixedP506FormNativeP286SolvedReferenceActual 0 =
      0
  rw [fixedP506FormNativeP286SolvedReferenceActual,
    installP286HolonomicConnectionSecondJet_connection_origin,
    positiveP506MatterCurrentP286NonzeroCurvatureLocalActualLift_connection_normalForm]
  funext direction
  simp [c3h181U7ConnectionNormalForm]

private theorem
    fixedP506FormNativeP286SolvedCurrent_gaugeConnection_origin_eq_fixedActual :
    fixedP506FormNativeP286SolvedCurrent.gaugeConnection 0 =
      FixedP506JointActual.gaugeConnection 0 := by
  funext direction
  apply p286CoordinateEquiv.injective
  change
    holonomicP286GaugeConnectionCoordinate
        fixedP506FormNativeP286SolvedCurrent 0 direction =
      holonomicP286GaugeConnectionCoordinate
        FixedP506JointActual 0 direction
  rw [congrFun
      fixedP506FormNativeP286SolvedCurrent_gaugeConnectionCoordinate_origin_zero
      direction,
    congrFun fixedP506JointActual_gaugeConnectionCoordinate_origin_zero
      direction]

private theorem
    fixedP506FormNativeP286SolvedCurrent_matterCovariantDerivative_origin_eq_fixedActual :
    holonomicMatterCovariantDerivative
        fixedP506FormNativeP286SolvedCurrent 0 =
      holonomicMatterCovariantDerivative FixedP506JointActual 0 := by
  funext direction
  unfold holonomicMatterCovariantDerivative
  rw [fixedP506FormNativeP286SolvedCurrent_matter_eq_fixedActual,
    fixedP506FormNativeP286SolvedCurrent_gravityConnection_eq_fixedActual,
    fixedP506FormNativeP286SolvedCurrent_gaugeConnection_origin_eq_fixedActual]

private theorem
    fixedP506FormNativeP286SolvedCurrent_generatedMatterVector_origin_zero :
    generatedContinuumMatterVector positiveSmoothUnifiedSource 0 0
        (toContinuumPointField fixedP506FormNativeP286SolvedCurrent 0) =
      0 := by
  have old :=
    fixedP506JointActual_generatedContinuumMatterVector_origin_zero
  unfold generatedContinuumMatterVector at old ⊢
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    matterFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart] at old ⊢
  rw [fixedP506FormNativeP286SolvedCurrent_coframe_eq_fixedActual,
    fixedP506FormNativeP286SolvedCurrent_matterCovariantDerivative_origin_eq_fixedActual,
    fixedP506FormNativeP286SolvedCurrent_scalar_eq_fixedActual,
    fixedP506FormNativeP286SolvedCurrent_matter_eq_fixedActual]
  exact old

private theorem fixedP506FormNativeP286SolvedCurrent_primalActionLaw :
    HolonomicCurrentCoframeMatterTimeActionLaw
      fixedP506FormNativeP286SolvedCurrent 0
      (holonomicMatterCovariantDerivative
        fixedP506FormNativeP286SolvedCurrent 0
        canonicalLorentzianTimeDirection) := by
  exact
    currentCoframeActionLaw_of_generatedContinuumMatterVector_zero
      positiveSmoothUnifiedSource fixedP506FormNativeP286SolvedCurrent
      fixedP506FormNativeP286SolvedCurrent_generatedMatterVector_origin_zero

private theorem fixedP506FormNativeP286SolvedCurrent_noncharacteristic :
    coframeTemporalPrincipalScalar
        (fixedP506FormNativeP286SolvedCurrent.coframe 0) ≠
      0 := by
  rw [fixedP506FormNativeP286SolvedCurrent_coframe_eq_fixedActual,
    fixedGlobalMatterDualP286Complete_coframe_origin]
  simp

private theorem
    fixedP506FormNativeSolvedPrimalMatterCurrent_eq_solvedCurrent :
    fixedP506FormNativeSolvedPrimalMatterCurrent =
      fixedP506FormNativeP286SolvedCurrent := by
  unfold fixedP506FormNativeSolvedPrimalMatterCurrent
  apply
    (actionGeneratedCurrentCoframeMatterTimeResponseActual_eq_iff
      fixedP506FormNativeP286SolvedCurrent).2
  exact
    holonomicCurrentCoframeMatterTimeActionLaw_unique
      fixedP506FormNativeP286SolvedCurrent 0
      fixedP506FormNativeP286SolvedCurrent_noncharacteristic
      _ _
      fixedP506FormNativeP286SolvedCurrent_primalActionLaw
      (actionGeneratedHolonomicCurrentCoframeMatterTimeCovariantDerivative_satisfies_actionLaw
        fixedP506FormNativeP286SolvedCurrent 0
        fixedP506FormNativeP286SolvedCurrent_noncharacteristic)

private theorem fixedP506FormNativeP286SolvedCurrent_adjointActionLaw :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      fixedP506FormNativeP286SolvedCurrent 0
      (holonomicConjugateMatterDerivativeDual
        fixedP506FormNativeP286SolvedCurrent 0
        canonicalLorentzianTimeDirection) := by
  have derivativeEq (direction : LorentzianIndex) :
      holonomicConjugateMatterDerivativeDual
          fixedP506FormNativeP286SolvedCurrent 0 direction =
        holonomicConjugateMatterDerivativeDual
          FixedP506JointActual 0 direction := by
    unfold holonomicConjugateMatterDerivativeDual
      holonomicConjugateMatterDerivativeCoordinates
      holonomicConjugateMatterCoordinates
    rw [
      fixedP506FormNativeP286SolvedCurrent_conjugateMatter_eq_fixedActual]
  have spatialTransportEq :
      holonomicIdentityCoframeConjugateMatterSpatialTransport
          fixedP506FormNativeP286SolvedCurrent 0 =
        holonomicIdentityCoframeConjugateMatterSpatialTransport
          FixedP506JointActual 0 := by
    unfold holonomicIdentityCoframeConjugateMatterSpatialTransport
    simp_rw [derivativeEq]
  have connectionOperatorEq :
      holonomicIdentityCoframeMatterConnectionOperator
          fixedP506FormNativeP286SolvedCurrent 0 =
        holonomicIdentityCoframeMatterConnectionOperator
          FixedP506JointActual 0 := by
    funext direction
    unfold holonomicIdentityCoframeMatterConnectionOperator
    rw [
      fixedP506FormNativeP286SolvedCurrent_gravityConnection_eq_fixedActual,
      fixedP506FormNativeP286SolvedCurrent_gaugeConnection_origin_eq_fixedActual]
  have algebraicOperatorEq :
      holonomicIdentityCoframeMatterAlgebraicOperator
          fixedP506FormNativeP286SolvedCurrent 0 =
        holonomicIdentityCoframeMatterAlgebraicOperator
          FixedP506JointActual 0 := by
    unfold holonomicIdentityCoframeMatterAlgebraicOperator
    rw [connectionOperatorEq,
      fixedP506FormNativeP286SolvedCurrent_scalar_eq_fixedActual]
  have law := fixedP506JointActual_adjointActionLaw
  unfold HolonomicIdentityCoframeConjugateMatterTimeActionLaw at law ⊢
  rw [derivativeEq, spatialTransportEq,
    congrFun
      fixedP506FormNativeP286SolvedCurrent_conjugateMatter_eq_fixedActual 0,
    algebraicOperatorEq]
  exact law

private theorem
    fixedP506FormNativeSolvedMatterDualCurrent_eq_solvedCurrent :
    fixedP506FormNativeSolvedMatterDualCurrent =
      fixedP506FormNativeP286SolvedCurrent := by
  unfold fixedP506FormNativeSolvedMatterDualCurrent
  rw [fixedP506FormNativeSolvedPrimalMatterCurrent_eq_solvedCurrent]
  apply
    (actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_eq_iff
      fixedP506FormNativeP286SolvedCurrent).2
  exact
    (holonomicIdentityCoframeConjugateMatterTimeActionLaw_iff
      fixedP506FormNativeP286SolvedCurrent 0 _).1
      fixedP506FormNativeP286SolvedCurrent_adjointActionLaw

theorem fixedP506FormNativeJointActionSolvedSuccessor_matter :
    FixedP506FormNativeJointActionSolvedSuccessor.matter =
      FixedP506JointActionSuccessor.matter := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_matter,
    fixedP506FormNativeSolvedMatterDualCurrent_eq_solvedCurrent]
  rfl

theorem fixedP506FormNativeJointActionSolvedSuccessor_conjugateMatter :
    FixedP506FormNativeJointActionSolvedSuccessor.conjugateMatter =
      FixedP506JointActionSuccessor.conjugateMatter := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_conjugateMatter,
    fixedP506FormNativeSolvedMatterDualCurrent_eq_solvedCurrent]
  rfl

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_gravityConnection_origin :
    FixedP506FormNativeJointActionSolvedSuccessor.gravityConnection 0 =
      FixedP506JointActionSuccessor.gravityConnection 0 := by
  rw [FixedP506FormNativeJointActionSolvedSuccessor,
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_connection_zero,
    fixedP506FormNativeSolvedMatterDualCurrent_eq_solvedCurrent]
  rfl

theorem fixedP506FormNativeJointActionSolvedSuccessor_smooth :
    FixedP506FormNativeJointActionSolvedSuccessor.Smooth := by
  have primalSmooth :
      fixedP506FormNativeSolvedPrimalMatterCurrent.Smooth :=
    actionGeneratedCurrentCoframeMatterTimeResponseActual_smooth
      fixedP506FormNativeP286SolvedCurrent
      fixedP506FormNativeP286SolvedCurrent_smooth
  have dualSmooth :
      fixedP506FormNativeSolvedMatterDualCurrent.Smooth :=
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_smooth
      fixedP506FormNativeSolvedPrimalMatterCurrent primalSmooth
  exact
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_smooth
      positiveSmoothUnifiedSource fixedP506FormNativeSolvedMatterDualCurrent
      dualSmooth

private theorem fixedP506FormNativeP286SolvedCurrent_lorentzAdmissible :
    GravityConnectionLorentzAdmissible
      fixedP506FormNativeP286SolvedCurrent := by
  intro point
  change
    LorentzSkew (FixedP506JointActionSuccessor.gravityConnection point)
  rw [fixedP506JointActionSuccessor_gravityConnection]
  exact fixedP506JointActual_lorentzAdmissible point

theorem
    fixedP506FormNativeJointActionSolvedSuccessor_lorentzAdmissible :
    GravityConnectionLorentzAdmissible
      FixedP506FormNativeJointActionSolvedSuccessor := by
  unfold FixedP506FormNativeJointActionSolvedSuccessor
  apply
    sourceActionGeneratedDiracDualECFullCauchyLocalActualLift_lorentzAdmissible
  intro point
  rw [fixedP506FormNativeSolvedMatterDualCurrent,
    actionGeneratedIdentityCoframeConjugateMatterTimeResponseActual_gravityConnection,
    fixedP506FormNativeSolvedPrimalMatterCurrent,
    actionGeneratedCurrentCoframeMatterTimeResponseActual_gravityConnection]
  exact fixedP506FormNativeP286SolvedCurrent_lorentzAdmissible point

theorem fixedP506FormNativeJointActionSolvedSuccessor_exactLineage :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506JointActionSuccessor_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506JointActionSectionResponse

import H0mework.Realization.Relations.FintypeDerivation
import H0mework.Physics.ConnectionJets.GeneratedP286AffineConnectionGerm
import H0mework.Physics.GaugeAction.P286GaugeAuxiliaryEquation
import H0mework.Physics.GravitySource.NormalizedAffineConnectionGerm

/-!
# S9-C3h1: dependency-light source-generated partial primitive carrier

This module freezes exactly the primitive Stage-9 fields that the current
proof-free source can generate without completing a
`StageNineHolonomicConfiguration` by zero or by an arbitrary witness.

The gravity branch begins with the framework root, not with a configuration
lift.  The source determines an ambient keep `K`; the transported residual
is `Kr`, and `linearResidualTrace K r` is the uniquely forced
`(I-K)r`.  Their split derives the required origin curvature used by the
already normalized gravity connection germ.

The resulting dependency-light carrier contains six generated primitive
fields: coframe, gravity connection, gravity II+ auxiliary, P286 gauge
connection, P286 constitutive auxiliary, and root-chart scalar.  It
deliberately omits the gravity simplicity multiplier, smooth continuum matter,
and smooth continuum conjugate-matter fields.  Those omissions are represented
only as typed producer requests; no zero value, arbitrary extension, shell
equation, stationarity statement, integrability receipt, branch selector, or
endpoint-atomhood certificate fills them.

Exact P506/L0 lineage and endpoint 11 remain separate source-admission
readouts.  The positive specialization aligns both generated connections with
their already proved actual origin-curvature producers.  This is not yet a
full configuration, a local joint solution, or a stationary world.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSourceGeneratedPartialPrimitiveCarrier

open AffineRelaxation
open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageNineEnrichedProofFreeSource
open StageNineBlockwiseConstitutive
open StageNineDynamicBreakingVacuum
open StageNineGlobalConnection
open StageNineHolonomicField
open StageNineP286GaugeAuxiliaryEquation
open StageNinePositiveSourceGravityMouthObstruction
open StageNinePositiveSourceGravityMouthTransportCurvature
open StageNinePositiveSourceGravityMouthNormalizedAffineConnectionGerm
open StageNineSourceGeneratedP286AffineConnectionGerm
open SU7MotherLieAlgebra
open SU7MotherGaugeTheory
open DiracExteriorMatterAction
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

/-! ## Source-induced gravity transport data

These are derived functions of the existing source.  They are not fields of
the partial primitive carrier.  In particular, the primitive connection
below contains neither a curvature target nor a transport receipt.
-/

def sourceGravityMouthConstitutiveCurvature
    (source : SmoothUnifiedSource) : PhysicalBivector :=
  gravityInternalDualEquiv
    (physicalIIPlusBivector (source.legacy.coframeAt 0))

def sourceGravityMouthObstruction
    (source : SmoothUnifiedSource) : PhysicalBivector :=
  source.legacy.lorentzCurvatureAtOrigin -
    sourceGravityMouthConstitutiveCurvature source

/-- The actual ambient keep `K`, fixed by the source's existing `sigma`. -/
def sourceGravityMouthAmbientKeep
    (source : SmoothUnifiedSource) :
    PhysicalBivector →ₗ[ℝ] PhysicalBivector :=
  scalarKeepLinearMap source.legacy.sigma

/-- The actual Layer-0 transport formula `r' = K r`. -/
def sourceGravityMouthTransportedResidual
    (source : SmoothUnifiedSource) : PhysicalBivector :=
  sourceGravityMouthAmbientKeep source
    (sourceGravityMouthObstruction source)

theorem sourceGravityMouthTransportedResidual_eq_scalarKeep
    (source : SmoothUnifiedSource) :
    sourceGravityMouthTransportedResidual source =
      (1 - source.legacy.sigma) • sourceGravityMouthObstruction source :=
  rfl

/-- The complementary responsibility trace is forced as `(I-K)r`; it is not
an independently supplied source field. -/
def sourceGravityMouthTrace
    (source : SmoothUnifiedSource) : PhysicalBivector :=
  linearResidualTrace (sourceGravityMouthAmbientKeep source)
    (sourceGravityMouthObstruction source)

theorem sourceGravityMouthTrace_eq_scalarTrace
    (source : SmoothUnifiedSource) :
    sourceGravityMouthTrace source =
      source.legacy.sigma • sourceGravityMouthObstruction source := by
  change sourceGravityMouthObstruction source -
      (1 - source.legacy.sigma) • sourceGravityMouthObstruction source = _
  module

theorem sourceGravityMouthObstruction_split
    (source : SmoothUnifiedSource) :
    sourceGravityMouthObstruction source =
      sourceGravityMouthTransportedResidual source +
        sourceGravityMouthTrace source :=
  residualTransportCore_residual_split
    (sourceGravityMouthAmbientKeep source)
    (sourceGravityMouthObstruction source)

/-- The connection target is derived from the constitutive mouth plus `Kr`;
it is not accepted as source input. -/
def sourceGravityMouthRequiredCurvature
    (source : SmoothUnifiedSource) : PhysicalBivector :=
  sourceGravityMouthConstitutiveCurvature source +
    sourceGravityMouthTransportedResidual source

def sourceNormalizedAffineGravityConnectionField
    (source : SmoothUnifiedSource) : LorentzConnectionField :=
  normalizedAffineLorentzConnectionField
    (generatedLorentzConnectionAt source 0)
    (sourceGravityMouthRequiredCurvature source)

/-! ## Six genuinely produced primitive fields -/

/-- Dependency-light fragment of the nine-field holonomic carrier.  The
absence of the remaining three projections is intentional: this type cannot
silently install placeholders for them. -/
@[ext] structure StageNinePartialPrimitiveCarrier where
  coframe : BasePoint → LorentzianCoframe
  gravityConnection : LorentzConnectionField
  gravityAuxiliary : BasePoint → PhysicalBivector
  gaugeConnection : P286ConnectionField
  gaugeAuxiliary : BasePoint → Fin 6 → P286LieBlockData
  scalar : BasePoint → ScalarCoordinateCarrier

/-- Actual source-to-partial-carrier producer.  Chart `0` is the fixed
canonical representative of the already generated three-chart cover; it is
not a caller-supplied physical parameter. -/
def sourceGeneratedStageNinePartialPrimitiveCarrier
    (source : SmoothUnifiedSource) : StageNinePartialPrimitiveCarrier where
  coframe := source.legacy.coframeAt
  gravityConnection := sourceNormalizedAffineGravityConnectionField source
  gravityAuxiliary := fun point =>
    physicalIIPlusBivector (source.legacy.coframeAt point)
  gaugeConnection := sourceP286AffineConnectionField source.legacy
  gaugeAuxiliary := fun point =>
    generatedP286GaugeConstitutiveAuxiliary source
      (source.legacy.coframeAt point)
      (sourceP286TargetCurvature source.legacy)
  scalar := generatedLocalVacuumCoordinates source 0

@[simp] theorem sourceGeneratedStageNinePartialPrimitiveCarrier_coframe
    (source : SmoothUnifiedSource) :
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).coframe =
      source.legacy.coframeAt :=
  rfl

@[simp] theorem sourceGeneratedStageNinePartialPrimitiveCarrier_gravityConnection
    (source : SmoothUnifiedSource) :
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).gravityConnection =
      sourceNormalizedAffineGravityConnectionField source :=
  rfl

@[simp] theorem sourceGeneratedStageNinePartialPrimitiveCarrier_gravityAuxiliary
    (source : SmoothUnifiedSource) (point : BasePoint) :
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).gravityAuxiliary
        point =
      physicalIIPlusBivector (source.legacy.coframeAt point) :=
  rfl

@[simp] theorem sourceGeneratedStageNinePartialPrimitiveCarrier_gaugeConnection
    (source : SmoothUnifiedSource) :
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).gaugeConnection =
      sourceP286AffineConnectionField source.legacy :=
  rfl

@[simp] theorem sourceGeneratedStageNinePartialPrimitiveCarrier_gaugeAuxiliary
    (source : SmoothUnifiedSource) (point : BasePoint) :
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).gaugeAuxiliary
        point =
      generatedP286GaugeConstitutiveAuxiliary source
        (source.legacy.coframeAt point)
        (sourceP286TargetCurvature source.legacy) :=
  rfl

@[simp] theorem sourceGeneratedStageNinePartialPrimitiveCarrier_scalar
    (source : SmoothUnifiedSource) (point : BasePoint) :
    (sourceGeneratedStageNinePartialPrimitiveCarrier source).scalar point =
      generatedLocalVacuumCoordinates source 0 point :=
  rfl

/-! ## Positive-source specialization and admission -/

def positiveSourceStageNinePartialPrimitiveCarrier :
    StageNinePartialPrimitiveCarrier :=
  sourceGeneratedStageNinePartialPrimitiveCarrier positiveSmoothUnifiedSource

theorem positive_sourceGravityMouthConstitutiveCurvature :
    sourceGravityMouthConstitutiveCurvature positiveSmoothUnifiedSource =
      positiveSourceGravityMouthConstitutiveCurvature :=
  rfl

theorem positive_sourceGravityMouthObstruction :
    sourceGravityMouthObstruction positiveSmoothUnifiedSource =
      positiveSourceGravityMouthObstruction :=
  rfl

theorem positive_sourceGravityMouthTransportedResidual :
    sourceGravityMouthTransportedResidual positiveSmoothUnifiedSource =
      positiveSourceGravityMouthTransportedResidual := by
  rw [positiveSourceGravityMouthTransportedResidual_eq_scalarKeep]
  rfl

theorem positive_sourceGravityMouthRequiredCurvature :
    sourceGravityMouthRequiredCurvature positiveSmoothUnifiedSource =
      positiveSourceGravityMouthRequiredCurvature := by
  unfold sourceGravityMouthRequiredCurvature
    positiveSourceGravityMouthRequiredCurvature
  rw [positive_sourceGravityMouthConstitutiveCurvature,
    positive_sourceGravityMouthTransportedResidual]

theorem positive_partialGravityConnection_eq_existingProducer :
    positiveSourceStageNinePartialPrimitiveCarrier.gravityConnection =
      positiveSourceGravityMouthNormalizedAffineConnectionField := by
  unfold positiveSourceStageNinePartialPrimitiveCarrier
    sourceGeneratedStageNinePartialPrimitiveCarrier
    sourceNormalizedAffineGravityConnectionField
    positiveSourceGravityMouthNormalizedAffineConnectionField
    positiveSourceGravityMouthOriginConnectionValue
  rw [positive_sourceGravityMouthRequiredCurvature]

/-- Admission remains a theorem about the same proof-free source rather than
a certificate stored inside the primitive carrier.  No Factor atomhood
premise occurs. -/
theorem positive_partialPrimitiveProducer_exactLineage_endpointAdmission :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 :=
  ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
    positiveSmoothUnifiedSource_generates_endpoint_eleven⟩

/-- The two connection fields in the partial carrier are actual primitive
producers.  Arbitrary complete templates are used only as typed readers of
their derived curvatures; no missing field is selected here. -/
theorem positive_partialPrimitiveConnections_actualOriginCurvatures
    (gravityTemplate gaugeTemplate : StageNineHolonomicConfiguration) :
    (installPositiveSourceGravityMouthNormalizedAffineConnection
        gravityTemplate).gravityConnection =
        positiveSourceStageNinePartialPrimitiveCarrier.gravityConnection ∧
      holonomicGravityCurvature
          (installPositiveSourceGravityMouthNormalizedAffineConnection
            gravityTemplate) 0 =
        positiveSourceGravityMouthRequiredCurvature ∧
      (installSourceP286AffineConnection
        positiveSmoothUnifiedSource.legacy gaugeTemplate).gaugeConnection =
        positiveSourceStageNinePartialPrimitiveCarrier.gaugeConnection ∧
      holonomicGaugeCurvature
          (installSourceP286AffineConnection
            positiveSmoothUnifiedSource.legacy gaugeTemplate) 0 =
        sourceP286TargetCurvature positiveSmoothUnifiedSource.legacy := by
  refine ⟨?_,
    installPositiveSourceGravityMouthNormalizedAffineConnection_curvature_origin
      gravityTemplate,
    rfl,
    holonomicGaugeCurvature_installSourceP286AffineConnection_origin _ _⟩
  rw [positive_partialGravityConnection_eq_existingProducer]
  rfl

/-! ## Exact typed boundary for the remaining producers -/

/-- These are the only primitive projections absent from the partial carrier.
This inductive is a producer-request boundary, not a theorem that no future
source-derived producer can exist. -/
inductive PendingStageNinePrimitiveProducer where
  | gravitySimplicityMultiplier
  | continuumMatter
  | continuumConjugateMatter
deriving DecidableEq, FintypeViaProxy

/-- Exact target type of each still-pending producer.  No value of any target
type is supplied here. -/
def PendingStageNinePrimitiveProducer.Target :
    PendingStageNinePrimitiveProducer → Type
  | .gravitySimplicityMultiplier => BasePoint → PhysicalBivector
  | .continuumMatter => BasePoint → DiracExteriorMatterCarrier
  | .continuumConjugateMatter =>
      BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier

def pendingStageNinePrimitiveProducers :
    Finset PendingStageNinePrimitiveProducer :=
  Finset.univ

@[simp] theorem mem_pendingStageNinePrimitiveProducers
    (slot : PendingStageNinePrimitiveProducer) :
    slot ∈ pendingStageNinePrimitiveProducers :=
  Finset.mem_univ slot

end

end SaturationMonoid.PhysicsCore.StageNineSourceGeneratedPartialPrimitiveCarrier

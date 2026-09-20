import H0mework.Physics.Matter.GeneratedMatter
import H0mework.Physics.Matter.SU7ExteriorMatterAnomalyRunning
import H0mework.Physics.Matter.SU7ExteriorMatterFullVariations

/-!
# Source-generated Stage-8 gravity--gauge--matter joint credential

The Stage-8 mouth is one proof-free source.  Its physical projection already
generates the Stage-6 mother credential; its actual P506/L0 projection must
equal the canonical observable lineage, and the endpoint is then a downstream
grammar readout.  No endpoint or exact-lineage certificate is accepted by the
canonical producer.

The same source also generates the matter link jet.  One joint `Λ⁴V` scalar
is installed in the actual joint configuration, and both the mass map and the
finite mixing matrix are definitionally read from that configuration's scalar.
The final nonzero current is therefore evaluated on the source-generated
matter state, not on a separately supplied probe.

No reference-SM running table, endpoint atomhood, Boolean atomicity, primitive
law, or FactorHolonomy certificate is a field of this structure.
-/

namespace SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential

open EmpiricalReferenceScaleCouplingBoundary
open SU7MotherLieAlgebra
open SU7MotherGaugeAction
open SU7MotherSourceConfiguration
open SU7MotherPhysicalUnifiedAdmission
open SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open SU7ExteriorMatterAnomalyRunning
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open PointwiseDiracSpinConnectionLift
open SU7ExteriorBreakingYukawa
open SU7ExteriorYukawaMassSpectrum
open SU7ExteriorMatterFullVariations
open StageEightProofFreeSource
open StageEightSourceGeneratedMatter
open RepresentationArithmeticAtomProjectionDefect
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StandardModelConstraint

noncomputable section

def stageEightCredentialGeometry
    {stageSource : StageEightProofFreeSource.Source}
    {boundary : EmpiricalReferenceScaleCouplings}
    (stageSix :
      SU7MotherPhysicalUnifiedAdmissionCredential
        stageSource.toPhysicalSource boundary) :
    PointwiseLorentzianCoframeJet :=
  stageSix.stageFive.stageFour.output.geometry.jet

theorem stageEightCredentialGeometry_eq_source
    {stageSource : StageEightProofFreeSource.Source}
    {boundary : EmpiricalReferenceScaleCouplings}
    (stageSix :
      SU7MotherPhysicalUnifiedAdmissionCredential
        stageSource.toPhysicalSource boundary) :
    stageEightCredentialGeometry stageSix =
      stageSource.toPhysicalSource.jetAt 0 := by
  rw [stageEightCredentialGeometry,
    stageSix.stageFive.stageFour.output_eq]
  rfl

/-- The only final Stage-8 matter configuration: source-generated matter,
the Stage-6 geometry and connection, and one joint breaking scalar. -/
def stageEightJointMatterConfiguration
    (stageSource : StageEightProofFreeSource.Source)
    {boundary : EmpiricalReferenceScaleCouplings}
    (stageSix :
      SU7MotherPhysicalUnifiedAdmissionCredential
        stageSource.toPhysicalSource boundary) :
    StageEightVariationConfiguration :=
  sourceGeneratedCurrentConfigurationAt stageSource
    (stageEightCredentialGeometry stageSix)
    stageSix.sourceMother.gauge.connection
    finiteGenerationJointBreakingScalar

/-- Final corrected Stage-8 credential.  All equalities are outputs of the
canonical root constructor below; that constructor accepts no lineage,
endpoint, scalar, matter-state, mass-map, mixing, or current certificate. -/
structure StageEightGravityGaugeMatterCredential
    (stageSource : StageEightProofFreeSource.Source)
    {boundary : EmpiricalReferenceScaleCouplings}
    (stageSix :
      SU7MotherPhysicalUnifiedAdmissionCredential
        stageSource.toPhysicalSource boundary) : Type where
  sourceMother_eq_generated :
    stageSix.sourceMother =
      sourceGeneratedMotherUnifiedConfiguration
        stageSource.toPhysicalSource boundary
  exactP506L0Lineage :
    stageSource.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference
  stageSeven : SU7ExteriorMatterStageSevenComputationReceipt
  stageEightARegression : StageEightACovariantMatterReceipt
  matterRepresentation :
    Representation ℂ SU7MotherGroup SU7ExteriorSpinorMatterCarrier
  matterRepresentation_eq_actual :
    matterRepresentation = su7ExteriorSpinorMatterRepresentation
  breakingRepresentation :
    Representation ℂ SU7MotherGroup ExteriorBreakingScalarCarrier
  breakingRepresentation_eq_actual :
    breakingRepresentation = exteriorBreakingScalarRepresentation
  yukawaAction : ExteriorBreakingScalarCarrier → DiracMatterEnd
  yukawaAction_eq_actual : yukawaAction = chiralExteriorYukawaAction
  matterJet : DiracExteriorMatterLinkJet
  matterJet_eq_sourceGenerated :
    matterJet = sourceGeneratedMatterJet stageSource
  jointBreakingScalar : ExteriorBreakingScalarCarrier
  jointBreakingScalar_eq_generated :
    jointBreakingScalar = finiteGenerationJointBreakingScalar
  jointBreakingScalar_nonzero : jointBreakingScalar ≠ 0
  actualMotherElement_moves_jointBreakingScalar :
    exteriorBreakingScalarRepresentation hyperchargeQuarterTurn
        jointBreakingScalar ≠ jointBreakingScalar
  matterConfiguration : StageEightVariationConfiguration
  matterConfiguration_eq_actual :
    matterConfiguration =
      stageEightJointMatterConfiguration stageSource stageSix
  jointBreakingScalar_eq_matterConfiguration :
    jointBreakingScalar = matterConfiguration.breakingScalar
  generatedMassMap :
    ExteriorDegreeTwoMatterCarrier →ₗ[ℂ] ExteriorDegreeSixMatterCarrier
  generatedMassMap_eq_matterConfiguration :
    generatedMassMap =
      exteriorYukawaMassMap matterConfiguration.breakingScalar
  generatedMixing : Matrix (Fin 2) (Fin 2) ℂ
  generatedMixing_eq_matterConfiguration :
    generatedMixing =
      finiteGenerationMassMatrixOfScalar matterConfiguration.breakingScalar
  generatedMixing_eq_joint :
    generatedMixing = finiteGenerationJointMassMatrix
  sameSourceGeometry :
    matterConfiguration.geometry =
      stageEightGeometryReadoutOfActual
        (stageEightCredentialGeometry stageSix)
  sameMotherConnection :
    matterConfiguration.motherTransport =
      fun direction =>
        diracExteriorLinkAction
          (motherLinkFamilyOfConnection
            stageSix.sourceMother.gauge.connection direction)
  localGaugeKineticInvariant : ∀ gauge : LocalSU7GaugeJet,
    diracExteriorMatterLinkActionDensity
        (stageEightCredentialGeometry stageSix)
        (localGaugeTransformLinkFamily gauge
          (motherLinkFamilyOfConnection
            stageSix.sourceMother.gauge.connection))
        (localGaugeTransformMatterLinkJet gauge matterJet) =
      diracExteriorMatterLinkActionDensity
        (stageEightCredentialGeometry stageSix)
        (motherLinkFamilyOfConnection
          stageSix.sourceMother.gauge.connection)
        matterJet
  geometryGammaCompatible : ∀ direction coordinate : LorentzianIndex,
    coframeDiracGammaCovariantDerivative
      (stageEightCredentialGeometry stageSix) direction coordinate = 0
  usesSameMotherConnection :
    diracExteriorMatterLinkActionDensity
        (stageEightCredentialGeometry stageSix)
        (motherLinkFamilyOfConnection
          stageSix.sourceMother.gauge.connection)
        matterJet =
      diracExteriorMatterLinkActionDensity
        (stageEightCredentialGeometry stageSix)
        (fun direction =>
          1 + (stageSix.sourceMother.gauge.connection.potential direction :
            Matrix SU7MotherIndex SU7MotherIndex ℂ))
        matterJet
  stageEightB : StageEightBJointBreakingYukawaReceipt
  stageEightC : StageEightCJointMassMixingReceipt
  stageEightD : StageEightDExactVariationLawReceipt
  nonzeroCurrentOnJointConfiguration :
    stageEightMotherCurrent matterConfiguration
      stageEightIdentityMotherVariation ≠ 0

theorem StageEightGravityGaugeMatterCredential.generatedLineage_height_pos
    {stageSource : StageEightProofFreeSource.Source}
    {boundary : EmpiricalReferenceScaleCouplings}
    {stageSix :
      SU7MotherPhysicalUnifiedAdmissionCredential
        stageSource.toPhysicalSource boundary}
    (credential :
      StageEightGravityGaugeMatterCredential stageSource stageSix) :
    0 < su7A6SignedHeight
      stageSource.generatedP506L0Lineage.sourceLabel := by
  rw [credential.exactP506L0Lineage]
  exact canonicalP506SourceAffineL0ObservableLineageReference_height_pos

/-- Endpoint is a derived grammar readout, not stored credential data. -/
def StageEightGravityGaugeMatterCredential.selectedEndpoint
    {stageSource : StageEightProofFreeSource.Source}
    {boundary : EmpiricalReferenceScaleCouplings}
    {stageSix :
      SU7MotherPhysicalUnifiedAdmissionCredential
        stageSource.toPhysicalSource boundary}
    (credential :
      StageEightGravityGaugeMatterCredential stageSource stageSix) : Nat :=
  stageSource.generatedSelectedEndpoint
    credential.generatedLineage_height_pos

@[simp] theorem StageEightGravityGaugeMatterCredential.selectedEndpoint_eq_eleven
    {stageSource : StageEightProofFreeSource.Source}
    {boundary : EmpiricalReferenceScaleCouplings}
    {stageSix :
      SU7MotherPhysicalUnifiedAdmissionCredential
        stageSource.toPhysicalSource boundary}
    (credential :
      StageEightGravityGaugeMatterCredential stageSource stageSix) :
    credential.selectedEndpoint = 11 := by
  simp [StageEightGravityGaugeMatterCredential.selectedEndpoint,
    StageEightProofFreeSource.Source.generatedSelectedEndpoint,
    credential.exactP506L0Lineage]

/-- Actual root producer.  Every proof field is discharged from the one
canonical proof-free source and previously proved generic laws. -/
def canonicalStageEightGravityGaugeMatterCredential :
    StageEightGravityGaugeMatterCredential
      canonicalSource canonicalPhysicalStageSix where
  sourceMother_eq_generated :=
    canonicalPhysicalStageSix.sourceMother_eq_generated
  exactP506L0Lineage := canonicalSource_generates_exactP506L0Lineage
  stageSeven := su7ExteriorMatterStageSevenComputationReceipt
  stageEightARegression := stageEightACovariantMatterReceipt
  matterRepresentation := su7ExteriorSpinorMatterRepresentation
  matterRepresentation_eq_actual := rfl
  breakingRepresentation := exteriorBreakingScalarRepresentation
  breakingRepresentation_eq_actual := rfl
  yukawaAction := chiralExteriorYukawaAction
  yukawaAction_eq_actual := rfl
  matterJet := sourceGeneratedMatterJet canonicalSource
  matterJet_eq_sourceGenerated := rfl
  jointBreakingScalar := finiteGenerationJointBreakingScalar
  jointBreakingScalar_eq_generated := rfl
  jointBreakingScalar_nonzero := finiteGenerationJointBreakingScalar_ne_zero
  actualMotherElement_moves_jointBreakingScalar :=
    finiteGenerationJointBreakingScalar_is_genuinely_broken
  matterConfiguration :=
    stageEightJointMatterConfiguration canonicalSource
      canonicalPhysicalStageSix
  matterConfiguration_eq_actual := rfl
  jointBreakingScalar_eq_matterConfiguration := rfl
  generatedMassMap :=
    exteriorYukawaMassMap finiteGenerationJointBreakingScalar
  generatedMassMap_eq_matterConfiguration := rfl
  generatedMixing := finiteGenerationJointMassMatrix
  generatedMixing_eq_matterConfiguration := rfl
  generatedMixing_eq_joint := rfl
  sameSourceGeometry := rfl
  sameMotherConnection := rfl
  localGaugeKineticInvariant := fun gauge =>
    diracExteriorMatterLinkActionDensity_localGauge_invariant gauge
      (stageEightCredentialGeometry canonicalPhysicalStageSix)
      (motherLinkFamilyOfConnection
        canonicalPhysicalStageSix.sourceMother.gauge.connection)
      (sourceGeneratedMatterJet canonicalSource)
  geometryGammaCompatible := fun direction coordinate =>
    diracExteriorMatterJointLink_geometryGammaCompatible
      (stageEightCredentialGeometry canonicalPhysicalStageSix)
      canonicalPhysicalStageSix.stageFive.stageFour.geometry_nondegenerate
      direction coordinate
  usesSameMotherConnection :=
    diracExteriorMatterLinkAction_uses_same_motherConnection
      (stageEightCredentialGeometry canonicalPhysicalStageSix)
      canonicalPhysicalStageSix.sourceMother.gauge.connection
      (sourceGeneratedMatterJet canonicalSource)
  stageEightB := stageEightBJointBreakingYukawaReceipt
  stageEightC := stageEightCJointMassMixingReceipt
  stageEightD := stageEightDExactVariationLawReceipt
  nonzeroCurrentOnJointConfiguration := by
    have coframe_eq_one :
        (stageEightCredentialGeometry canonicalPhysicalStageSix).coframe = 1 := by
      rw [stageEightCredentialGeometry_eq_source canonicalPhysicalStageSix,
        canonicalPhysicalSource.jetAt_zero_coframe]
    change
      stageEightMotherCurrent
          (sourceGeneratedCurrentConfigurationAt canonicalSource
            (stageEightCredentialGeometry canonicalPhysicalStageSix)
            canonicalPhysicalStageSix.sourceMother.gauge.connection
            finiteGenerationJointBreakingScalar)
          stageEightIdentityMotherVariation ≠ 0
    rw [canonicalSource_generatedMotherCurrent_eq_I
      (stageEightCredentialGeometry canonicalPhysicalStageSix)
      canonicalPhysicalStageSix.sourceMother.gauge.connection
      finiteGenerationJointBreakingScalar coframe_eq_one]
    exact Complex.I_ne_zero

theorem canonicalSource_generates_correctedStageEightGravityGaugeMatterCredential :
    Nonempty
      (StageEightGravityGaugeMatterCredential
        canonicalSource canonicalPhysicalStageSix) :=
  ⟨canonicalStageEightGravityGaugeMatterCredential⟩

/-- The endpoint-11 zero-phase lookalike remains rejected by exact lineage,
even if a caller hypothetically supplied a Stage-6 physical credential for
its physical projection. -/
theorem zeroPhaseSource_rejects_stageEightGravityGaugeMatterCredential :
    ¬ Nonempty
      (Σ stageSix :
          SU7MotherPhysicalUnifiedAdmissionCredential
            zeroPhaseSource.toPhysicalSource unitBoundary,
        StageEightGravityGaugeMatterCredential zeroPhaseSource stageSix) := by
  rintro ⟨⟨_, credential⟩⟩
  exact zeroPhaseSource_generatedLineage_ne_canonical
    credential.exactP506L0Lineage

/-- Legacy Stage-8 configuration: fixed probe plus the old one-channel
breaking scalar.  It remains only as a negative regression. -/
def legacyFixedProbeMatterConfiguration : StageEightVariationConfiguration :=
  stageEightVariationConfigurationOfActual
    (stageEightCredentialGeometry canonicalPhysicalStageSix)
    canonicalPhysicalStageSix.sourceMother.gauge.connection
    nonzeroLocalLinkMatterJet exteriorBreakingScalar

theorem legacyFixedProbeMatterConfiguration_ne_generated :
    legacyFixedProbeMatterConfiguration ≠
      stageEightJointMatterConfiguration canonicalSource
        canonicalPhysicalStageSix := by
  intro equality
  have scalarEquality := congrArg
    (fun configuration : StageEightVariationConfiguration =>
      configuration.breakingScalar) equality
  exact exteriorBreakingScalar_ne_finiteGenerationJointBreakingScalar
    (by simpa [legacyFixedProbeMatterConfiguration,
      stageEightJointMatterConfiguration,
      sourceGeneratedCurrentConfigurationAt,
      stageEightVariationConfigurationOfActual] using scalarEquality)

theorem mismatchedMatterConfiguration_rejected
    {stageSource : StageEightProofFreeSource.Source}
    {boundary : EmpiricalReferenceScaleCouplings}
    {stageSix :
      SU7MotherPhysicalUnifiedAdmissionCredential
        stageSource.toPhysicalSource boundary}
    (credential :
      StageEightGravityGaugeMatterCredential stageSource stageSix)
    (candidate : StageEightVariationConfiguration)
    (mismatch :
      candidate ≠ stageEightJointMatterConfiguration stageSource stageSix) :
    candidate ≠ credential.matterConfiguration := by
  intro candidate_eq
  exact mismatch
    (candidate_eq.trans credential.matterConfiguration_eq_actual)

theorem legacyFixedProbeMatterConfiguration_rejected :
    legacyFixedProbeMatterConfiguration ≠
      canonicalStageEightGravityGaugeMatterCredential.matterConfiguration :=
  mismatchedMatterConfiguration_rejected
    canonicalStageEightGravityGaugeMatterCredential
    legacyFixedProbeMatterConfiguration
    legacyFixedProbeMatterConfiguration_ne_generated

end
end SaturationMonoid.PhysicsCore.SU7GravityGaugeMatterJointCredential

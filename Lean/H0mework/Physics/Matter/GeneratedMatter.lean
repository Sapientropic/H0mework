import H0mework.Physics.Source.ProofFreeSource
import H0mework.Physics.Matter.SU7ExteriorMatterVariationRegressions

/-!
# Stage-8 matter jet generated from the common source phase

The former joint credential inserted `nonzeroLocalLinkMatterJet` directly.
Here the distinguished L0 edge of the proof-free Stage-8 source generates a
complex matter amplitude.  That amplitude scales both the target state and
its conjugate coordinate, so the entire finite link jet is a source output.
The canonical source reproduces the previous nonzero calculation; a zero-L0
source generates a zero current.  Thus nonzero current is no longer a fixed
probe premise.
-/

namespace SaturationMonoid.PhysicsCore.StageEightSourceGeneratedMatter

open StageEightProofFreeSource
open SU7MotherGaugeTheory
open DiracExteriorMatterAction
open DiracExteriorMatterLocalGaugeLink
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterFullVariations
open RepresentationArithmeticAtomProjectionDefect
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StandardModelConstraint

noncomputable section

/-- Matter amplitude read from the same source phase edge used by the
physical projection. -/
def sourceMatterAmplitude
    (source : StageEightProofFreeSource.Source) : ℂ :=
  source.physicalPhaseAmplitude

/-- Actual finite-link matter state generated from the source amplitude. -/
def sourceGeneratedMatterJet
    (source : StageEightProofFreeSource.Source) :
    DiracExteriorMatterLinkJet where
  sourceField := 0
  targetField := fun direction =>
    if direction = 0 then
      sourceMatterAmplitude source • diracSpinTwoMatterProbe
    else 0
  sourceConjugateField :=
    sourceMatterAmplitude source • diracSpinZeroMatterCoordinate

theorem canonicalSource_generatedMatterJet_eq_nonzeroProbe :
    sourceGeneratedMatterJet canonicalSource =
      nonzeroLocalLinkMatterJet := by
  cases canonicalSource_physicalPhaseAmplitude
  simp [sourceGeneratedMatterJet, sourceMatterAmplitude,
    nonzeroLocalLinkMatterJet]

theorem diracSpinTwoMatterProbe_nonzero :
    diracSpinTwoMatterProbe ≠ 0 := by
  intro zero
  have coordinateZero := congrArg
    (fun field : DiracExteriorMatterCarrier =>
      hyperchargeDegreeTwoMatterCoordinate (field 2)) zero
  norm_num [diracSpinTwoMatterProbe,
    hyperchargeDegreeTwoMatterCoordinate_probe] at coordinateZero

theorem canonicalSource_generatedMatterJet_nonzero :
    sourceGeneratedMatterJet canonicalSource ≠
      { sourceField := 0
        targetField := fun _ => 0
        sourceConjugateField := 0 } := by
  intro equality
  have atDirection := congrArg
    (fun jet : DiracExteriorMatterLinkJet => jet.targetField 0) equality
  rw [canonicalSource_generatedMatterJet_eq_nonzeroProbe] at atDirection
  change diracSpinTwoMatterProbe = 0 at atDirection
  exact diracSpinTwoMatterProbe_nonzero atDirection

/-- Joint current configuration with no independent matter-state argument. -/
def sourceGeneratedCurrentConfigurationAt
    (source : StageEightProofFreeSource.Source)
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (breakingScalar : ExteriorBreakingScalarCarrier) :
    StageEightVariationConfiguration :=
  stageEightVariationConfigurationOfActual geometry connection
    (sourceGeneratedMatterJet source) breakingScalar

/-- Third corrected producer nail: the canonical proof-free source generates
the matter jet whose current is nonzero on every identity-coframe geometry,
independently of the selected mother connection and breaking scalar. -/
theorem canonicalSource_generatedMotherCurrent_eq_I
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (breakingScalar : ExteriorBreakingScalarCarrier)
    (coframe_eq_one : geometry.coframe = 1) :
    stageEightMotherCurrent
        (sourceGeneratedCurrentConfigurationAt canonicalSource
          geometry connection breakingScalar)
        stageEightIdentityMotherVariation = Complex.I := by
  rw [sourceGeneratedCurrentConfigurationAt,
    canonicalSource_generatedMatterJet_eq_nonzeroProbe]
  exact stageEightNonzeroMotherCurrentAt_eq_I
    geometry connection breakingScalar coframe_eq_one

def zeroPhaseSource : StageEightProofFreeSource.Source :=
  { canonicalSource with p506PhasePotential := fun _ => 0 }

@[simp] theorem zeroPhaseSource_physicalPhaseAmplitude :
    zeroPhaseSource.physicalPhaseAmplitude = 0 := by
  rfl

theorem zeroPhaseSource_generatedLineage_eq_lookalike :
    zeroPhaseSource.generatedP506L0Lineage =
      p506EndpointElevenZeroPhaseLineageLookalike := by
  apply P506SourceAffineL0ObservableLineageReference.ext
  · rfl
  · simp [StageEightProofFreeSource.Source.generatedP506L0Lineage,
      zeroPhaseSource, canonicalSource,
      p506EndpointElevenZeroPhaseLineageLookalike,
      canonicalP506SourceAffineL0ObservableLineageReference,
      p506SourceAffineL0ObservableLineageReferenceOfTrace,
      canonicalP506SourceAffineL0LineageReference,
      n10FiveSevenObservedTrace]
  · simp [StageEightProofFreeSource.Source.generatedP506L0Lineage,
      zeroPhaseSource, canonicalSource,
      p506EndpointElevenZeroPhaseLineageLookalike]
  · rfl
  · rfl
  · rfl
  · funext initial terminal
    simp [StageEightProofFreeSource.Source.generatedP506L0Lineage,
      StageEightProofFreeSource.Source.p506PhaseCochain, zeroPhaseSource,
      p506EndpointElevenZeroPhaseLineageLookalike]
  · norm_num [StageEightProofFreeSource.Source.generatedP506L0Lineage,
      StageEightProofFreeSource.Source.toPhysicalSource,
      ProofFreeRicherAnholonomicSource.Source.sigma,
      zeroPhaseSource, canonicalSource,
      p506EndpointElevenZeroPhaseLineageLookalike,
      canonicalP506SourceAffineL0ObservableLineageReference,
      p506SourceAffineL0ObservableLineageReferenceOfTrace,
      canonicalP506SourceAffineL0LineageReference,
      n10FiveSevenObservedTrace]

theorem zeroPhaseSource_generatedLineage_height_pos :
    0 < su7A6SignedHeight
      zeroPhaseSource.generatedP506L0Lineage.sourceLabel := by
  rw [zeroPhaseSource_generatedLineage_eq_lookalike]
  exact p506EndpointElevenZeroPhaseLineageLookalike_height_pos

@[simp] theorem zeroPhaseSource_still_generates_endpoint_eleven :
    zeroPhaseSource.generatedSelectedEndpoint
        zeroPhaseSource_generatedLineage_height_pos = 11 := by
  unfold StageEightProofFreeSource.Source.generatedSelectedEndpoint
  simpa only [zeroPhaseSource_generatedLineage_eq_lookalike] using
    p506EndpointElevenZeroPhaseLineageLookalike_selectedEndpoint

theorem zeroPhaseSource_generatedLineage_ne_canonical :
    zeroPhaseSource.generatedP506L0Lineage ≠
      canonicalP506SourceAffineL0ObservableLineageReference := by
  rw [zeroPhaseSource_generatedLineage_eq_lookalike]
  exact p506EndpointElevenZeroPhaseLineageLookalike_ne_canonical

theorem zeroPhaseSource_generatedMatterJet_zero :
    sourceGeneratedMatterJet zeroPhaseSource =
      { sourceField := 0
        targetField := fun _ => 0
        sourceConjugateField := 0 } := by
  simp [sourceGeneratedMatterJet, sourceMatterAmplitude]

/-- Negative regression: erasing the source phase erases the generated
matter state and every mother-current readout. -/
theorem zeroPhaseSource_generatedMotherCurrent_eq_zero
    (geometry : PointwiseLorentzianCoframeJet)
    (connection : SU7MotherGaugeConnection)
    (breakingScalar : ExteriorBreakingScalarCarrier)
    (variation : LorentzianIndex → DiracMatterEnd) :
    stageEightMotherCurrent
        (sourceGeneratedCurrentConfigurationAt zeroPhaseSource
          geometry connection breakingScalar) variation = 0 := by
  simp [stageEightMotherCurrent, sourceGeneratedCurrentConfigurationAt,
    stageEightVariationConfigurationOfActual,
    zeroPhaseSource_generatedMatterJet_zero]

end

end SaturationMonoid.PhysicsCore.StageEightSourceGeneratedMatter

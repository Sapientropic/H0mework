import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface.SourceNativeM14InstitutionalSpan
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication.SourceGeneratedM12AestheticPublicCommunication

/-!
# Source-native coordinates for one M14 platform teaching contact

The teaching source is the already generated renewed platform material action,
not the distinct paid platform occurrence.  At that exact action depth the
existing M14 culture chart supplies its `t0 -> t1` contact, while the existing
M12 publication supplies the coarse-to-refined aesthetic context transport.

This interface fixes only source coordinates.  It introduces no education
label, student registry, culture quotient, root installation, or successor.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Teaching
namespace Interface

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ProcessGame.Society.M14EssentialAccessRelationFixture
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle
open ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual
open ProcessGame.Society.M14SourceGeneratedActualRelationRoleReflexiveRing
open ProcessGame.Society.M14SourceGeneratedTenureQueueAppendRuntime
open ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend
open ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendPresentation
open ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendRuntime
open ProcessGame.Society.M14SourceGeneratedPlatformGateRenewedActualService
open ProcessGame.Society.M14ProofCarryingPlatformGateFullAdmission
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Communication
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface

noncomputable section

/-- The teaching contact starts at the renewed material action itself. -/
def m14TeachingDepthAt (boundary : Nat) : Nat :=
  platformGateMaterialDepthAt boundary

abbrev M14TeachingMaterialOccurrenceAt (boundary : Nat) :=
  M14InstitutionalMaterialOccurrenceAt boundary

def m14TeachingMaterialOccurrenceAt (boundary : Nat) :
    M14TeachingMaterialOccurrenceAt boundary :=
  m14InstitutionalMaterialOccurrenceAt boundary

/-- The actual contact emitted by the material action is the first edge of
the renewed three-cycle. -/
def m14TeachingCultureContactAt (boundary : Nat) :
    SourceGeneratedM14CultureContactEventAt (m14TeachingDepthAt boundary) :=
  sourceGeneratedM14CultureContactEventAt (m14TeachingDepthAt boundary) .t0

@[simp] theorem m14TeachingDepth_material_exact (boundary : Nat) :
    m14TeachingDepthAt boundary = platformGateMaterialDepthAt boundary :=
  rfl

@[simp] theorem m14TeachingContact_support_exact (boundary : Nat) :
    (m14TeachingCultureContactAt boundary).support = .t0 :=
  rfl

/-- Exact action-occurrence identity: both sides are indexed by the renewed
material depth, not merely by the same platform seed. -/
theorem m14TeachingContact_actionOccurrence_exact (boundary : Nat) :
    (crossCompilerActionPresentationAt
      (actualRelationCycleDepthAt (m14TeachingDepthAt boundary) .t0)).erase =
    (crossCompilerActionPresentationAt
      (platformGateMaterialDepthAt boundary)).erase :=
  rfl

/-- The culture contact's source runtime is the very source action retained
by full admission's material service. -/
theorem m14TeachingContact_sourceActionRuntime
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      (proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary
        ).materialFulfillment.materialService.sourceAction
      runtime (crossActionRuntimeDepth (m14TeachingDepthAt boundary)) := by
  change SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
    (generatedCrossCompilerRelationAppendActionAt
      (platformGateMaterialDepthAt boundary)) runtime
    (crossActionRuntimeDepth (platformGateMaterialDepthAt boundary))
  exact (m14TeachingCultureContactAt boundary).macroEdge.sourceActionRuntime

/-- The exact source actor of the teaching contact is the admitted gate
actor; no teacher tag is supplied. -/
theorem m14TeachingSourceActor_gate_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    actualRelationCycleActorAt (m14TeachingDepthAt boundary) .t0 =
      (proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary
        ).materialFulfillment.materialService.gateIncidence.gate.actor := by
  change actualRelationActorAt (platformGateMaterialDepthAt boundary) = _
  unfold actualRelationActorAt
  rw [platformGateMaterialSeed_platform]
  rw [(proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary
    ).materialFulfillment.materialService.gateIncidence.gate.actor_eq_platformActor]
  rfl

/-- The medium received at the target support is generated by the platform
edge's target role. -/
@[simp] theorem m14TeachingTargetMedium_platformProvider
    (boundary : Nat) :
    (culturePracticeMediumAt (m14TeachingDepthAt boundary) .t1).1 =
      EssentialAccessRole.platformProvider := by
  change actualRelationCycleTargetRoleAt
    (platformGateMaterialDepthAt boundary)
      (actualRelationIncomingIndex .t1) = .platformProvider
  change actualRelationTargetRoleAt (platformGateMaterialDepthAt boundary) =
    .platformProvider
  unfold actualRelationTargetRoleAt actualRelationAt
  rw [platformGateMaterialSeed_platform]
  rfl

/-- The M12 side is the canonical honest publication occurrence. -/
@[simp] theorem m14TeachingPublication_refinement_exact :
    sourceGeneratedM12PublicationContact.refinement =
      coarseMiddleKernelRefinement :=
  rfl

end
end Interface
end Teaching
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Interface.m14TeachingContact_actionOccurrence_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Interface.m14TeachingContact_sourceActionRuntime
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Interface.m14TeachingSourceActor_gate_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Interface.m14TeachingTargetMedium_platformProvider

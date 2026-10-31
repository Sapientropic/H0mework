import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface.SourceNativeM14InstitutionalSpan
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.Source.SourceGeneratedM12BeautyMaterial
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication.SourceGeneratedM12AestheticPublicCommunication

/-!
# Source-native coordinates for M14 art production

Art production is anchored at the renewed platform material action.  Its raw
work is the source-generated M12 coarse aesthetic object, and its refinement
event is the honest M12 publication contact.  The paid platform occurrence is
not identified with this distinct material-action occurrence.

This file exposes only source coordinates and a low-universe work readout.
The actual progress process and write-back are constructed in the source
module.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ArtProduction
namespace Interface

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ConstructiveRoot.RootInquiryCompletion
open ProcessGame.Society.M14EssentialAccessRelationFixture
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedActualRelationThreeCycle
open ProcessGame.Society.M14ProofCarryingActualRelationThreeCycleResidual
open ProcessGame.Society.M14SourceGeneratedTenureQueueAppendRuntime
open ProcessGame.Society.M14SourceGeneratedSequentialCrossCompilerRelationAppend
open ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendPresentation
open ProcessGame.Society.M14SourceGeneratedCrossCompilerRelationAppendRuntime
open ProcessGame.Society.M14SourceGeneratedPlatformGateRenewedActualService
open ProcessGame.Society.M14ProofCarryingPlatformGateFullAdmission
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12.SharedKernel.Communication
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface

noncomputable section

def m14ArtProductionDepthAt (boundary : Nat) : Nat :=
  platformGateMaterialDepthAt boundary

abbrev M14ArtProductionMaterialOccurrenceAt (boundary : Nat) :=
  M14InstitutionalMaterialOccurrenceAt boundary

def m14ArtProductionMaterialOccurrenceAt (boundary : Nat) :
    M14ArtProductionMaterialOccurrenceAt boundary :=
  m14InstitutionalMaterialOccurrenceAt boundary

/-- Low-universe exact source occurrence.  High full-admission and material
receipts are recovered from this occurrence's fixed indices. -/
inductive SourceGeneratedM14ArtProductionSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type
  | private generated

def sourceGeneratedM14ArtProductionSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex boundary :=
  .generated

namespace SourceGeneratedM14ArtProductionSourceAt

variable {oldVisit : OldVisit} {sourceIndex boundary : Nat}
  (source : SourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
    boundary)

def fullAdmission : ProofCarryingPlatformGateFullAdmissionAt oldVisit
    sourceIndex boundary := by
  cases source
  exact proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary

def materialService : SourceGeneratedPlatformGateRenewedActualServiceAt
    oldVisit sourceIndex boundary :=
  (fullAdmission source).materialFulfillment.materialService

def materialDebit : ActualMaintenanceDebit platformGateMaterialServiceProcess
    platformGateMaterialBudgetAt
    (platformGateMaterialMaintenanceEdgeAt boundary) .debt :=
  (materialService source).maintenanceDebit

def rawMaterial : SourceGeneratedM12BeautyMaterialAt .coarse := by
  cases source
  exact sourceGeneratedM12BeautyMaterialAt .coarse

def publicationContact : SourceGeneratedM12PublicationContact := by
  cases source
  exact sourceGeneratedM12PublicationContact

@[simp] theorem fullAdmission_exact :
    fullAdmission source =
      proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary := by
  cases source
  rfl

@[simp] theorem materialService_exact :
    materialService source =
      sourceGeneratedPlatformGateRenewedActualServiceAt oldVisit sourceIndex
        boundary := by
  cases source
  rfl

@[simp] theorem materialDebit_exact :
    materialDebit source = platformGateMaterialMaintenanceDebitAt boundary := by
  cases source
  rfl

@[simp] theorem rawMaterial_exact :
    rawMaterial source = sourceGeneratedM12BeautyMaterialAt .coarse := by
  cases source
  rfl

@[simp] theorem publicationContact_exact :
    publicationContact source = sourceGeneratedM12PublicationContact := by
  cases source
  rfl

end SourceGeneratedM14ArtProductionSourceAt

def m14ArtProductionRawOccurrence :
    SourceGeneratedM12AestheticContextOccurrence :=
  .coarse

def m14ArtProductionWorkOccurrence :
    SourceGeneratedM12AestheticContextOccurrence :=
  contextSwap m14ArtProductionRawOccurrence

@[simp] theorem m14ArtProductionWorkOccurrence_exact :
    m14ArtProductionWorkOccurrence = .refined :=
  rfl

structure M14ArtWorkReadout where
  object : M12AestheticObjectReadout
  context : M12AestheticContextReadout
  alignment : M12AestheticAlignmentReadout

def m14ArtWorkReadAt
    (occurrence : SourceGeneratedM12AestheticContextOccurrence) :
    M14ArtWorkReadout where
  object := sourceObjectRead occurrence
  context := sourceContextRead occurrence
  alignment := sourceAlignmentRead occurrence

theorem m14ArtWork_object_preserved :
    (m14ArtWorkReadAt m14ArtProductionRawOccurrence).object =
      (m14ArtWorkReadAt m14ArtProductionWorkOccurrence).object := by
  simpa only [m14ArtProductionRawOccurrence, m14ArtProductionWorkOccurrence,
    contextSwap, m14ArtWorkReadAt, m12BeautyFaceRead]
    using m12Beauty_object_preserved

theorem m14ArtWork_alignment_changes :
    (m14ArtWorkReadAt m14ArtProductionRawOccurrence).alignment ≠
      (m14ArtWorkReadAt m14ArtProductionWorkOccurrence).alignment := by
  simpa only [m14ArtProductionRawOccurrence, m14ArtProductionWorkOccurrence,
    contextSwap, m14ArtWorkReadAt, m12BeautyFaceRead]
    using m12Beauty_alignment_differs

theorem m14ArtWork_transformation_nontrivial :
    m14ArtWorkReadAt m14ArtProductionRawOccurrence ≠
      m14ArtWorkReadAt m14ArtProductionWorkOccurrence := by
  intro equality
  exact m14ArtWork_alignment_changes
    (congrArg M14ArtWorkReadout.alignment equality)

theorem m14ArtProduction_actionOccurrence_exact (boundary : Nat) :
    (crossCompilerActionPresentationAt
      (m14ArtProductionDepthAt boundary)).erase =
      (crossCompilerActionPresentationAt
        (platformGateMaterialDepthAt boundary)).erase :=
  rfl

theorem m14ArtProduction_sourceActionRuntime
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let source := sourceGeneratedM14ArtProductionSourceAt oldVisit sourceIndex
      boundary
    SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
      source.materialService.sourceAction runtime
      (crossActionRuntimeDepth (m14ArtProductionDepthAt boundary)) := by
  dsimp
  change SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
    (generatedCrossCompilerRelationAppendActionAt
      (platformGateMaterialDepthAt boundary)) runtime
    (crossActionRuntimeDepth (platformGateMaterialDepthAt boundary))
  exact (sourceGeneratedActualRelationMacroEdgeAt
    (platformGateMaterialDepthAt boundary)).sourceActionRuntime

end
end Interface
end ArtProduction
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface.m14ArtWork_transformation_nontrivial
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface.m14ArtProduction_actionOccurrence_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface.m14ArtProduction_sourceActionRuntime

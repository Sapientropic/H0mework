import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer.IndependentM14InstitutionalAuthorityConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Source.SourceGeneratedM14CultureMaterial

/-!
# Source-generated institutional culture material

The revised face joins the already complete relation-side culture history to
one independently generated institutional-authority readout.  Its occurrence
domain is the platform revision candidate emitted by the cycle-memory
obstruction.  High-universe provenance retains the relation-centered span,
actual paid U8, full admission, and renewed material service; none of these is
accepted from a caller or cached in the low-universe face.

No consumer coverage, quotient, factorization, root installation, or
successor is a source field.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Institution
namespace Source

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8
open ProcessGame.Society.M14SourceGeneratedPlatformChannelRevisionCandidate
open ProcessGame.Society.M14SourceGeneratedPlatformGateRenewedActualService
open ProcessGame.Society.M14SourceGeneratedPlatformGateTwoSlotMaterialNoGo
open ProcessGame.Society.M14ProofCarryingPlatformGateMaterialFulfillment
open ProcessGame.Society.M14ProofCarryingPlatformGateFullAdmission
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer

noncomputable section

/-- Low-universe dependent face over the exact source-generated channel
occurrence. -/
structure SourceGeneratedM14InstitutionalCultureFaceAt (base : Nat) : Type where
  cultureHistory : SourceGeneratedM14CultureFaceAt base
  institutionalAuthority : M14InstitutionalAuthorityReadout

def m14InstitutionalCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    SourceGeneratedM14InstitutionalCultureFaceAt
      (m14InstitutionalBaseAt boundary) where
  cultureHistory := m14CultureFaceReadAt (m14InstitutionalBaseAt boundary)
    (m14InstitutionalOldCultureViewAt boundary channel)
  institutionalAuthority :=
    m14InstitutionalAuthorityReadAt oldVisit sourceIndex boundary channel

/-- Private face seal indexed by the actual institutional channel. -/
inductive SourceGeneratedM14InstitutionalCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) : Type
  | private generated

def generateM14InstitutionalCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    SourceGeneratedM14InstitutionalCultureFaceTokenAt oldVisit sourceIndex
      boundary channel :=
  .generated

namespace SourceGeneratedM14InstitutionalCultureFaceTokenAt

def read
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {channel : M14InstitutionalChannelOccurrenceAt boundary}
    (_token : SourceGeneratedM14InstitutionalCultureFaceTokenAt oldVisit
      sourceIndex boundary channel) :
    SourceGeneratedM14InstitutionalCultureFaceAt
      (m14InstitutionalBaseAt boundary) :=
  m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary channel

end SourceGeneratedM14InstitutionalCultureFaceTokenAt

/-- High source mouth.  The actual U8 and full admission are generated from
the same boundary span; target representation facts are absent. -/
structure SourceGeneratedM14InstitutionalCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) : Type 32 where
  private mk ::
  face : SourceGeneratedM14InstitutionalCultureFaceTokenAt oldVisit
    sourceIndex boundary channel
  faceExact : face = generateM14InstitutionalCultureFaceTokenAt oldVisit
    sourceIndex boundary channel
  span : SourceGeneratedM14InstitutionalSpanAt oldVisit sourceIndex boundary
  spanExact : span = sourceGeneratedM14InstitutionalSpanAt oldVisit
    sourceIndex boundary
  candidate : SourceGeneratedPlatformChannelRevisionCandidateAt boundary
  candidateExact : candidate =
    sourceGeneratedPlatformChannelRevisionCandidateAt boundary
  paidU8 : ProofCarryingCycleMemoryPlatformGateActualPaidU8UpdateAt oldVisit
    sourceIndex boundary
  paidU8Exact : paidU8 =
    proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
      sourceIndex boundary
  fullAdmission : ProofCarryingPlatformGateFullAdmissionAt oldVisit
    sourceIndex boundary
  fullAdmissionExact : fullAdmission =
    proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary
  newPlatformSeedNoOldRepresentation : IsEmpty
    { oldChannel :
        ProcessGame.Society.M14SourceGeneratedContributionCapacityEssentialAccessChannel.EssentialAccessChannel //
      ProcessGame.Society.M14SourceGeneratedContributionCapacityEssentialAccessChannel.channelSeed
          oldChannel =
        revisedChannelSeed (obstruction := candidate.obstruction)
          (.inr candidate.gate) }
  materialCannotDisplaceOldPaidSlots : IsEmpty
    (RenewedPlatformMaterialServiceAt oldVisit sourceIndex boundary →
      ExistingTwoSlotPlatformMaterialAdmissionAt oldVisit sourceIndex
        boundary)

def sourceGeneratedM14InstitutionalCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    SourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
      boundary channel :=
  let candidate := sourceGeneratedPlatformChannelRevisionCandidateAt boundary
  let admission :=
    proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary
  { face := generateM14InstitutionalCultureFaceTokenAt oldVisit sourceIndex
      boundary channel
    faceExact := rfl
    span := sourceGeneratedM14InstitutionalSpanAt oldVisit sourceIndex boundary
    spanExact := rfl
    candidate := candidate
    candidateExact := rfl
    paidU8 := proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
      sourceIndex boundary
    paidU8Exact := rfl
    fullAdmission := admission
    fullAdmissionExact := rfl
    newPlatformSeedNoOldRepresentation :=
      candidate.newSeedNoOldRepresentation
    materialCannotDisplaceOldPaidSlots :=
      admission.materialCannotDisplaceOldSlots }

@[simp] theorem m14InstitutionalCultureMaterial_faceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    (sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
      boundary channel).face.read =
      m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
        channel :=
  rfl

/-- The kernel-escape domain, Payment transporter, paid U8, and full
admission all consume the same source-generated platform candidate. -/
@[simp] theorem m14InstitutionalCultureMaterial_spanCandidate_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    (sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
      boundary channel).span.paymentTransport.candidate =
      (sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
        boundary channel).candidate :=
  rfl

@[simp] theorem m14InstitutionalCultureMaterial_admissionCandidate_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    ((sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
      boundary channel).fullAdmission.materialFulfillment.materialService
        ).gateIncidence.candidate =
      (sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
        boundary channel).candidate :=
  rfl

@[simp] theorem m14InstitutionalCultureMaterial_service_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    (sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
      boundary channel).fullAdmission.materialFulfillment.materialService =
      (sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
        boundary channel).span.materialService :=
  rfl

theorem sourceGeneratedM14InstitutionalCultureMaterial_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    let material := sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit
      sourceIndex boundary channel
    Nonempty (SourceGeneratedM14InstitutionalCultureMaterialAt oldVisit
        sourceIndex boundary channel) ∧
      material.face.read =
        m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
          channel ∧
      material.span =
        sourceGeneratedM14InstitutionalSpanAt oldVisit sourceIndex boundary ∧
      material.candidate =
        sourceGeneratedPlatformChannelRevisionCandidateAt boundary ∧
      material.paidU8 =
        proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
          sourceIndex boundary ∧
      material.fullAdmission =
        proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary ∧
      material.span.paymentTransport.candidate = material.candidate ∧
      (material.fullAdmission.materialFulfillment.materialService
        ).gateIncidence.candidate = material.candidate ∧
      material.fullAdmission.materialFulfillment.materialService =
        material.span.materialService ∧
      type_of% (sourceGeneratedM14InstitutionalSpan_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (m14InstitutionalAuthorityConsumer_grounded oldVisit
        sourceIndex boundary) ∧
      type_of% material.newPlatformSeedNoOldRepresentation ∧
      type_of% material.materialCannotDisplaceOldPaidSlots := by
  let material := sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit
    sourceIndex boundary channel
  exact ⟨⟨material⟩, rfl, material.spanExact, material.candidateExact,
    material.paidU8Exact, material.fullAdmissionExact,
    m14InstitutionalCultureMaterial_spanCandidate_exact oldVisit sourceIndex
      boundary channel,
    m14InstitutionalCultureMaterial_admissionCandidate_exact oldVisit
      sourceIndex boundary channel,
    m14InstitutionalCultureMaterial_service_exact oldVisit sourceIndex
      boundary channel,
    sourceGeneratedM14InstitutionalSpan_directConsumer oldVisit sourceIndex
      boundary,
    m14InstitutionalAuthorityConsumer_grounded oldVisit sourceIndex boundary,
    material.newPlatformSeedNoOldRepresentation,
    material.materialCannotDisplaceOldPaidSlots⟩

end
end Source
end Institution
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source.m14InstitutionalCultureMaterial_faceRead_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source.m14InstitutionalCultureMaterial_spanCandidate_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source.m14InstitutionalCultureMaterial_admissionCandidate_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source.sourceGeneratedM14InstitutionalCultureMaterial_directConsumer

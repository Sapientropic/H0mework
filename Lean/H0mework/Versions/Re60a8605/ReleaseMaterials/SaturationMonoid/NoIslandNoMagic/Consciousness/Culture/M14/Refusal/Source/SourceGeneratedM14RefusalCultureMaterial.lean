import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer.IndependentM14RefusalSuccessorConsumer
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source.SourceGeneratedM14InstitutionalCultureMaterial

/-!
# Source-generated refusal culture material

The refusal face joins the canonical installed-platform culture face to the
actual paid-successor authority readout.  Its high source retains the exact
anti-retaliation certificate, the existing institutional material at the
platform channel, and the right-Payment old-channel successor seam.  Source
and target outer occurrences remain different actual authorities.

No consumer coverage, quotient, factorization, cross-root installation, or
future value is a producer argument.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Refusal
namespace Source

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer

noncomputable section

structure SourceGeneratedM14RefusalCultureFaceAt (base : Nat) : Type where
  institutionalCulture : SourceGeneratedM14InstitutionalCultureFaceAt base
  refusalSuccessor : M14RefusalAuthorityReadout

def m14RefusalCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14RefusalCultureFaceAt
      (m14InstitutionalBaseAt boundary) where
  institutionalCulture :=
    m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
      (m14RefusalOldInstitutionalViewAt oldVisit sourceIndex boundary
        occurrence)
  refusalSuccessor :=
    m14RefusalAuthorityReadAt oldVisit sourceIndex boundary occurrence

inductive SourceGeneratedM14RefusalCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) : Type
  | private generated

def generateM14RefusalCultureFaceTokenAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14RefusalCultureFaceTokenAt oldVisit sourceIndex boundary
      occurrence :=
  .generated

namespace SourceGeneratedM14RefusalCultureFaceTokenAt

def read
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary}
    (_token : SourceGeneratedM14RefusalCultureFaceTokenAt oldVisit sourceIndex
      boundary occurrence) :
    SourceGeneratedM14RefusalCultureFaceAt
      (m14InstitutionalBaseAt boundary) :=
  m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary occurrence

end SourceGeneratedM14RefusalCultureFaceTokenAt

structure SourceGeneratedM14RefusalCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    Type 32 where
  private mk ::
  face : SourceGeneratedM14RefusalCultureFaceTokenAt oldVisit sourceIndex
    boundary occurrence
  faceExact : face = generateM14RefusalCultureFaceTokenAt oldVisit sourceIndex
    boundary occurrence
  institutionalMaterial :
    SourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
      boundary (m14InstitutionalPlatformOccurrenceAt boundary)
  institutionalMaterialExact : institutionalMaterial =
    sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
      boundary (m14InstitutionalPlatformOccurrenceAt boundary)
  antiRetaliation :
    SourceGeneratedPaidSuccessorAfterRefusalAntiRetaliationAt oldVisit
      sourceIndex (m14RefusalSuccessorIndexAt boundary)
  antiRetaliationExact : antiRetaliation =
    m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
  sourceCurrentIsRightPayment :
    antiRetaliation.standingRenewal.sourceAuthorityCurrent =
      ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightCurrentAt
        oldVisit sourceIndex boundary
  platformChannelNextIsTargetOuter :
    type_of% (m14RefusalPlatformChannelNext_isTargetOuterOccurrence oldVisit
      sourceIndex boundary)
  noPowerMinting :
    type_of% (m14RefusalNoPowerMinting_directConsumer oldVisit sourceIndex
      boundary)

def sourceGeneratedM14RefusalCultureMaterialAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    SourceGeneratedM14RefusalCultureMaterialAt oldVisit sourceIndex boundary
      occurrence where
  face := generateM14RefusalCultureFaceTokenAt oldVisit sourceIndex boundary
    occurrence
  faceExact := rfl
  institutionalMaterial :=
    sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
      boundary (m14InstitutionalPlatformOccurrenceAt boundary)
  institutionalMaterialExact := rfl
  antiRetaliation := m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
  antiRetaliationExact := rfl
  sourceCurrentIsRightPayment :=
    m14RefusalSourceCurrent_eq_rightPaymentCurrent oldVisit sourceIndex
      boundary
  platformChannelNextIsTargetOuter :=
    m14RefusalPlatformChannelNext_isTargetOuterOccurrence oldVisit sourceIndex
      boundary
  noPowerMinting :=
    m14RefusalNoPowerMinting_directConsumer oldVisit sourceIndex boundary

@[simp] theorem m14RefusalCultureMaterial_faceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    (sourceGeneratedM14RefusalCultureMaterialAt oldVisit sourceIndex boundary
      occurrence).face.read =
      m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary occurrence :=
  rfl

theorem sourceGeneratedM14RefusalCultureMaterial_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    let material := sourceGeneratedM14RefusalCultureMaterialAt oldVisit
      sourceIndex boundary occurrence
    Nonempty (SourceGeneratedM14RefusalCultureMaterialAt oldVisit sourceIndex
        boundary occurrence) ∧
      material.face.read =
        m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary occurrence ∧
      material.institutionalMaterial =
        sourceGeneratedM14InstitutionalCultureMaterialAt oldVisit sourceIndex
          boundary (m14InstitutionalPlatformOccurrenceAt boundary) ∧
      material.antiRetaliation =
        m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary ∧
      type_of% (sourceGeneratedM14RefusalSuccessor_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (m14RefusalSuccessorConsumer_grounded oldVisit sourceIndex
        boundary) ∧
      type_of% material.platformChannelNextIsTargetOuter ∧
      type_of% material.noPowerMinting := by
  let material := sourceGeneratedM14RefusalCultureMaterialAt oldVisit
    sourceIndex boundary occurrence
  exact ⟨⟨material⟩, rfl, material.institutionalMaterialExact,
    material.antiRetaliationExact,
    sourceGeneratedM14RefusalSuccessor_directConsumer oldVisit sourceIndex
      boundary,
    m14RefusalSuccessorConsumer_grounded oldVisit sourceIndex boundary,
    material.platformChannelNextIsTargetOuter,
    material.noPowerMinting⟩

end
end Source
end Refusal
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source.m14RefusalCultureMaterial_faceRead_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source.sourceGeneratedM14RefusalCultureMaterial_directConsumer

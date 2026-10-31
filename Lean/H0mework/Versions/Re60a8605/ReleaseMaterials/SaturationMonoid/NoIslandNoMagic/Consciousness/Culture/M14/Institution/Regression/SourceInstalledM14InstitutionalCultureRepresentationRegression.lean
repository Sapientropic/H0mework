import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation.SourceInstalledM14InstitutionalCultureFace

/-!
# Whole regression for the institutional culture U8 revision

This regression closes the relation-centered source span, independent
institutional kernel escape, actual paid U8/full admission, updated consumer
quotient, and exact root installation together.  The old complete culture
face—not merely a language label—collides on tenure/platform authority.  The
new source-generated readout separates them and factors uniquely only through
the revised face.

The platform-root next and the distinct material-action next are both
retained with their native types; no Payment-to-material occurrence equality
or successor collapse is asserted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Institution
namespace Regression

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8
open ProcessGame.Society.M14ProofCarryingPlatformGateFullAdmission
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation

noncomputable section

def rootInstalledM14InstitutionalCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :=
  ((m14InstitutionalCulturePayloadAt oldVisit sourceIndex boundary).2
    channel).read

@[simp] theorem rootInstalledM14InstitutionalCultureFaceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    rootInstalledM14InstitutionalCultureFaceReadAt oldVisit sourceIndex
        boundary channel =
      m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
        channel :=
  rfl

theorem rootInstalledM14InstitutionalCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary)
      (rootInstalledM14InstitutionalCultureFaceReadAt oldVisit sourceIndex
        boundary) := by
  intro left right
  simpa only [rootInstalledM14InstitutionalCultureFaceRead_exact] using
    m14InstitutionalCultureKernelExactAt oldVisit sourceIndex boundary left
      right

noncomputable def rootInstalledM14InstitutionalCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
      ).Quotient ≃
      Set.range
        (rootInstalledM14InstitutionalCultureFaceReadAt oldVisit sourceIndex
          boundary) :=
  (rootInstalledM14InstitutionalCultureKernelExactAt oldVisit sourceIndex
    boundary).quotientEquivRange

theorem rootInstalledM14InstitutionalCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer :
      (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
        ).Consumer) :
    ∃! factor :
        Set.range
            (rootInstalledM14InstitutionalCultureFaceReadAt oldVisit
              sourceIndex boundary) →
          (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
            ).Output consumer,
      ∀ occurrence,
        factor
            ⟨rootInstalledM14InstitutionalCultureFaceReadAt oldVisit
                sourceIndex boundary occurrence,
              occurrence, rfl⟩ =
          (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
            ).read consumer occurrence :=
  (rootInstalledM14InstitutionalCultureKernelExactAt oldVisit sourceIndex
    boundary).everyConsumer_unique_factorization consumer

theorem rootInstalledM14InstitutionalCulture_uniqueSourceIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range
            (m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range
            (rootInstalledM14InstitutionalCultureFaceReadAt oldVisit
              sourceIndex boundary),
      ∀ occurrence,
        equivalence
            ⟨m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
                occurrence,
              occurrence, rfl⟩ =
          ⟨rootInstalledM14InstitutionalCultureFaceReadAt oldVisit
              sourceIndex boundary occurrence,
            occurrence, rfl⟩ :=
  m14InstitutionalCultureCompleteCarrier_uniqueIsoAt oldVisit sourceIndex
    boundary
    (rootInstalledM14InstitutionalCultureFaceReadAt oldVisit sourceIndex
      boundary)
    (rootInstalledM14InstitutionalCultureKernelExactAt oldVisit sourceIndex
      boundary)

/-- The exact same source span supplies old-kernel escape and actual U8
authority; neither is a caller-provided pairing. -/
theorem m14InstitutionalCulture_escapeSharesSourceWithActualPaidU8
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (m14InstitutionalCultureKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14InstitutionalCulture_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (sourceGeneratedM14InstitutionalSpan_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (proofCarryingCycleMemoryPlatformGateActualPaidU8Update
        oldVisit sourceIndex boundary) ∧
      type_of% (platformGateFullAdmission_directConsumer oldVisit sourceIndex
        boundary) :=
  ⟨m14InstitutionalCultureKernelEscapeAt oldVisit sourceIndex boundary,
    m14InstitutionalCulture_oldFactorization_isEmpty oldVisit sourceIndex
      boundary,
    sourceGeneratedM14InstitutionalSpan_directConsumer oldVisit sourceIndex
      boundary,
    proofCarryingCycleMemoryPlatformGateActualPaidU8Update oldVisit
      sourceIndex boundary,
    platformGateFullAdmission_directConsumer oldVisit sourceIndex boundary⟩

/-- Both inherited faces remain installed through the new projection coface. -/
theorem m14InstitutionalCulture_inheritedPlatformObserverFaces
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nonempty (type_of% (m14InstitutionalCulturePlatformInstallationAt
        oldVisit sourceIndex boundary)) ∧
      Nonempty (type_of% (m14InstitutionalCultureObserverInstallationAt
        oldVisit sourceIndex boundary)) ∧
      Function.Injective
        (m14InstitutionalCultureInheritedInstallationAt oldVisit sourceIndex
          boundary).embed :=
  ⟨⟨m14InstitutionalCulturePlatformInstallationAt oldVisit sourceIndex
      boundary⟩,
    ⟨m14InstitutionalCultureObserverInstallationAt oldVisit sourceIndex
      boundary⟩,
    (m14InstitutionalCultureInheritedInstallationAt oldVisit sourceIndex
      boundary).embed_injective⟩

/-- Root continuation and material-action continuation remain two native,
typed outputs of the forked source. -/
theorem m14InstitutionalCulture_twoGeneratedNexts
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (m14InstitutionalCulture_generatedNextCurrentAt_eq oldVisit
        sourceIndex boundary 0) ∧
      let admission := proofCarryingPlatformGateFullAdmission oldVisit
        sourceIndex boundary
      admission.materialFulfillment.materialService.generatedNext =
        ⟨admission.materialFulfillment.materialService.sourceAction.target.TargetV,
          admission.materialFulfillment.materialService.sourceAction.target.targetRoot.toAuthoritativeRoot,
          admission.materialFulfillment.materialService.sourceAction.target.targetVisit⟩ :=
  ⟨m14InstitutionalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
      boundary 0,
    (proofCarryingPlatformGateFullAdmission oldVisit sourceIndex boundary
      ).materialActionNext⟩

/- Root face tokens contain no high-universe producer or theorem outputs. -/
/-- error: Invalid field `fullAdmission` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14InstitutionalCulturePayloadAt oldVisit 0 0).2
    (m14InstitutionalPlatformOccurrenceAt 0)).fullAdmission

/-- error: Invalid field `quotient` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14InstitutionalCulturePayloadAt oldVisit 0 0).2
    (m14InstitutionalPlatformOccurrenceAt 0)).quotient

/-- error: Invalid field `factorization` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14InstitutionalCulturePayloadAt oldVisit 0 0).2
    (m14InstitutionalPlatformOccurrenceAt 0)).factorization

/-- error: Invalid field `generatedNext` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14InstitutionalCulturePayloadAt oldVisit 0 0).2
    (m14InstitutionalPlatformOccurrenceAt 0)).generatedNext

theorem sourceInstalledM14InstitutionalCultureRepresentation_wholeRegression
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceGeneratedM14InstitutionalSpan_directConsumer oldVisit
      sourceIndex boundary) ∧
      type_of% (m14InstitutionalAuthorityConsumer_grounded oldVisit
        sourceIndex boundary) ∧
      type_of% (sourceGeneratedM14InstitutionalCultureMaterial_directConsumer
        oldVisit sourceIndex boundary
          (m14InstitutionalPlatformOccurrenceAt boundary)) ∧
      type_of% (m14InstitutionalCultureRepresentation_directConsumer oldVisit
        sourceIndex boundary
          (m14InstitutionalPlatformOccurrenceAt boundary)) ∧
      type_of% (m14InstitutionalCulture_escapeSharesSourceWithActualPaidU8 oldVisit
        sourceIndex boundary) ∧
      type_of% (sourceInstalledM14InstitutionalCultureFace_directConsumer
        oldVisit sourceIndex boundary) ∧
      type_of% (rootInstalledM14InstitutionalCultureKernelExactAt oldVisit
        sourceIndex boundary) ∧
      Nonempty
        ((m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary
          ).Quotient ≃
          Set.range
            (rootInstalledM14InstitutionalCultureFaceReadAt oldVisit
              sourceIndex boundary)) ∧
      (∀ consumer,
        type_of%
          (rootInstalledM14InstitutionalCultureEveryConsumer_uniqueFactorizationAt
            oldVisit sourceIndex boundary consumer)) ∧
      type_of% (rootInstalledM14InstitutionalCulture_uniqueSourceIsoAt
        oldVisit sourceIndex boundary) ∧
      type_of% (m14InstitutionalCulture_inheritedPlatformObserverFaces
        oldVisit sourceIndex boundary) ∧
      type_of% (m14InstitutionalCulture_twoGeneratedNexts oldVisit sourceIndex
        boundary) :=
  ⟨sourceGeneratedM14InstitutionalSpan_directConsumer oldVisit sourceIndex
      boundary,
    m14InstitutionalAuthorityConsumer_grounded oldVisit sourceIndex boundary,
    sourceGeneratedM14InstitutionalCultureMaterial_directConsumer oldVisit
      sourceIndex boundary (m14InstitutionalPlatformOccurrenceAt boundary),
    m14InstitutionalCultureRepresentation_directConsumer oldVisit sourceIndex
      boundary (m14InstitutionalPlatformOccurrenceAt boundary),
    m14InstitutionalCulture_escapeSharesSourceWithActualPaidU8 oldVisit sourceIndex
      boundary,
    sourceInstalledM14InstitutionalCultureFace_directConsumer oldVisit
      sourceIndex boundary,
    rootInstalledM14InstitutionalCultureKernelExactAt oldVisit sourceIndex
      boundary,
    ⟨rootInstalledM14InstitutionalCultureQuotientEquivRangeAt oldVisit
      sourceIndex boundary⟩,
    rootInstalledM14InstitutionalCultureEveryConsumer_uniqueFactorizationAt
      oldVisit sourceIndex boundary,
    rootInstalledM14InstitutionalCulture_uniqueSourceIsoAt oldVisit
      sourceIndex boundary,
    m14InstitutionalCulture_inheritedPlatformObserverFaces oldVisit
      sourceIndex boundary,
    m14InstitutionalCulture_twoGeneratedNexts oldVisit sourceIndex boundary⟩

end
end Regression
end Institution
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Regression.m14InstitutionalCulture_escapeSharesSourceWithActualPaidU8
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Regression.m14InstitutionalCulture_inheritedPlatformObserverFaces
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Regression.m14InstitutionalCulture_twoGeneratedNexts
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Regression.sourceInstalledM14InstitutionalCultureRepresentation_wholeRegression

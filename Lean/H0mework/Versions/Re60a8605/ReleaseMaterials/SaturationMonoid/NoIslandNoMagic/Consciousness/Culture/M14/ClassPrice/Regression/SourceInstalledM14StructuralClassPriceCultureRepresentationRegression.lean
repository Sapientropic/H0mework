import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation.SourceInstalledM14StructuralClassPriceCultureFace

/-!
# Whole regression for the structural class-price culture face

This checkpoint joins the exact refusal-target Payment recurrence, periodic
structural rent, root-independent control/debt asymmetry, two independent
consumers, updated quotient and the current-`2` root installation.  The
controller and affected faces share one Payment, relationship event and
complete refusal carrier; generated class and price positions separate them.

The refusal root current `2` and external Payment remain different ambient
occurrences connected only by the source-generated singleton presentation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ClassPrice
namespace Regression

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Transport
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation

noncomputable section

def rootInstalledM14StructuralClassPriceCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :=
  ((m14StructuralClassPriceCulturePayloadAt oldVisit sourceIndex boundary).2
    occurrence).read

@[simp] theorem rootInstalledM14StructuralClassPriceCultureFaceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
        boundary occurrence =
      m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex boundary
        occurrence :=
  rfl

theorem rootInstalledM14StructuralClassPriceCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14StructuralClassPriceConsumersAt oldVisit sourceIndex boundary)
      (rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit
        sourceIndex boundary) := by
  intro left right
  simpa only [rootInstalledM14StructuralClassPriceCultureFaceRead_exact] using
    m14StructuralClassPriceCultureKernelExactAt oldVisit sourceIndex boundary
      left right

noncomputable def rootInstalledM14StructuralClassPriceCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPriceConsumersAt oldVisit sourceIndex
      boundary).Quotient ≃
      Set.range
        (rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit
          sourceIndex boundary) :=
  (rootInstalledM14StructuralClassPriceCultureKernelExactAt oldVisit
    sourceIndex boundary).quotientEquivRange

theorem rootInstalledM14StructuralClassPriceCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer :
      (m14StructuralClassPriceConsumersAt oldVisit sourceIndex
        boundary).Consumer) :
    ∃! factor :
        Set.range
            (rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit
              sourceIndex boundary) →
          (m14StructuralClassPriceConsumersAt oldVisit sourceIndex
            boundary).Output consumer,
      ∀ occurrence,
        factor
            ⟨rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit
                sourceIndex boundary occurrence,
              occurrence, rfl⟩ =
          (m14StructuralClassPriceConsumersAt oldVisit sourceIndex
            boundary).read consumer occurrence :=
  (rootInstalledM14StructuralClassPriceCultureKernelExactAt oldVisit
    sourceIndex boundary).everyConsumer_unique_factorization consumer

theorem rootInstalledM14StructuralClassPriceCulture_uniqueSourceIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range (m14StructuralClassPriceCultureFaceReadAt oldVisit
          sourceIndex boundary) ≃
          Set.range
            (rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit
              sourceIndex boundary),
      ∀ occurrence,
        equivalence
            ⟨m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex
                boundary occurrence,
              occurrence, rfl⟩ =
          ⟨rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit
              sourceIndex boundary occurrence,
            occurrence, rfl⟩ :=
  m14StructuralClassPriceCompleteCarrier_uniqueIsoAt oldVisit sourceIndex
    boundary
      (rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit
        sourceIndex boundary)
      (rootInstalledM14StructuralClassPriceCultureKernelExactAt oldVisit
        sourceIndex boundary)

/-- The current-1 refusal component survives with its exact payload. -/
theorem m14StructuralClassPriceCultureInheritedRefusalOutcome_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
      boundary).projectionOutcomeAt
        ((m14StructuralClassPriceCultureRefusalInstallationAt oldVisit
          sourceIndex boundary).embed PUnit.unit) 1 =
      .inl ⟨m14RefusalCultureActiveAt oldVisit sourceIndex boundary,
        m14RefusalCulturePayloadAt oldVisit sourceIndex boundary⟩ :=
  rfl

theorem m14StructuralClassPriceCulture_sourceTargetHostile
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (m14StructuralClassPriceOccurrences_samePaymentAndEvent oldVisit
      sourceIndex boundary) ∧
      m14StructuralClassPriceOldRefusalFaceReadAt oldVisit sourceIndex boundary
          (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex
            boundary) =
        m14StructuralClassPriceOldRefusalFaceReadAt oldVisit sourceIndex
          boundary
            (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
              boundary) ∧
      m14StructuralClassReadAt
          (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex
            boundary) ≠
        m14StructuralClassReadAt
          (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
            boundary) ∧
      m14StructuralPriceReadAt
          (m14StructuralClassPriceSourceOccurrenceAt oldVisit sourceIndex
            boundary) ≠
        m14StructuralPriceReadAt
          (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
            boundary) ∧
      type_of% (m14StructuralClassPriceCultureKernelEscapeAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceNoForgery_directConsumer oldVisit
        sourceIndex boundary) :=
  ⟨m14StructuralClassPriceOccurrences_samePaymentAndEvent oldVisit sourceIndex
      boundary,
    m14StructuralClassPriceOldRefusalFace_source_eq_target oldVisit sourceIndex
      boundary,
    (m14StructuralClassPriceRead_hasActualDifference oldVisit sourceIndex
      boundary).1,
    (m14StructuralClassPriceRead_hasActualDifference oldVisit sourceIndex
      boundary).2,
    m14StructuralClassPriceCultureKernelEscapeAt oldVisit sourceIndex boundary,
    m14StructuralClassPriceNoForgery_directConsumer oldVisit sourceIndex
      boundary⟩

/- Private root tokens contain none of the high source or downstream facts. -/
/-- error: Invalid field `periodicRent` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14StructuralClassPriceCulturePayloadAt oldVisit 0 0).2
    (m14StructuralClassPriceTargetOccurrenceAt oldVisit 0 0)).periodicRent

/-- error: Invalid field `exploitationWitness` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14StructuralClassPriceCulturePayloadAt oldVisit 0 0).2
    (m14StructuralClassPriceTargetOccurrenceAt oldVisit 0 0)
      ).exploitationWitness

/-- error: Invalid field `factorization` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14StructuralClassPriceCulturePayloadAt oldVisit 0 0).2
    (m14StructuralClassPriceTargetOccurrenceAt oldVisit 0 0)).factorization

/-- error: Invalid field `generatedNext` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14StructuralClassPriceCulturePayloadAt oldVisit 0 0).2
    (m14StructuralClassPriceTargetOccurrenceAt oldVisit 0 0)).generatedNext

theorem sourceInstalledM14StructuralClassPriceCultureRepresentation_wholeRegression
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceNativeM14StructuralClassPriceCoordinates_directConsumer
      oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceConsumer_grounded oldVisit sourceIndex
        boundary) ∧
      type_of%
        (sourceGeneratedM14StructuralClassPriceCultureMaterial_directConsumer
          oldVisit sourceIndex boundary
            (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
              boundary)) ∧
      type_of% (m14StructuralClassPriceCultureRepresentation_directConsumer
        oldVisit sourceIndex boundary
          (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
            boundary)) ∧
      type_of%
        (sourceGeneratedM14RefusalStructuralClassPriceNextTransport_directConsumer
          oldVisit sourceIndex boundary) ∧
      type_of%
        (sourceInstalledM14StructuralClassPriceCultureFace_directConsumer
          oldVisit sourceIndex boundary) ∧
      type_of% (rootInstalledM14StructuralClassPriceCultureKernelExactAt
        oldVisit sourceIndex boundary) ∧
      Nonempty
        ((m14StructuralClassPriceConsumersAt oldVisit sourceIndex
          boundary).Quotient ≃
          Set.range
            (rootInstalledM14StructuralClassPriceCultureFaceReadAt oldVisit
              sourceIndex boundary)) ∧
      (∀ consumer,
        type_of%
          (rootInstalledM14StructuralClassPriceCultureEveryConsumer_uniqueFactorizationAt
            oldVisit sourceIndex boundary consumer)) ∧
      type_of% (rootInstalledM14StructuralClassPriceCulture_uniqueSourceIsoAt
        oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceCultureInheritedRefusalOutcome_exact
        oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceCulture_sourceTargetHostile oldVisit
        sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceCulture_generatedNextCurrentAt_eq
        oldVisit sourceIndex boundary 2) :=
  ⟨sourceNativeM14StructuralClassPriceCoordinates_directConsumer oldVisit
      sourceIndex boundary,
    m14StructuralClassPriceConsumer_grounded oldVisit sourceIndex boundary,
    sourceGeneratedM14StructuralClassPriceCultureMaterial_directConsumer
      oldVisit sourceIndex boundary
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary),
    m14StructuralClassPriceCultureRepresentation_directConsumer oldVisit
      sourceIndex boundary
        (m14StructuralClassPriceTargetOccurrenceAt oldVisit sourceIndex
          boundary),
    sourceGeneratedM14RefusalStructuralClassPriceNextTransport_directConsumer
      oldVisit sourceIndex boundary,
    sourceInstalledM14StructuralClassPriceCultureFace_directConsumer oldVisit
      sourceIndex boundary,
    rootInstalledM14StructuralClassPriceCultureKernelExactAt oldVisit
      sourceIndex boundary,
    ⟨rootInstalledM14StructuralClassPriceCultureQuotientEquivRangeAt oldVisit
      sourceIndex boundary⟩,
    rootInstalledM14StructuralClassPriceCultureEveryConsumer_uniqueFactorizationAt
      oldVisit sourceIndex boundary,
    rootInstalledM14StructuralClassPriceCulture_uniqueSourceIsoAt oldVisit
      sourceIndex boundary,
    m14StructuralClassPriceCultureInheritedRefusalOutcome_exact oldVisit
      sourceIndex boundary,
    m14StructuralClassPriceCulture_sourceTargetHostile oldVisit sourceIndex
      boundary,
    m14StructuralClassPriceCulture_generatedNextCurrentAt_eq oldVisit
      sourceIndex boundary 2⟩

end
end Regression
end ClassPrice
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Regression.m14StructuralClassPriceCultureInheritedRefusalOutcome_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Regression.m14StructuralClassPriceCulture_sourceTargetHostile
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Regression.sourceInstalledM14StructuralClassPriceCultureRepresentation_wholeRegression

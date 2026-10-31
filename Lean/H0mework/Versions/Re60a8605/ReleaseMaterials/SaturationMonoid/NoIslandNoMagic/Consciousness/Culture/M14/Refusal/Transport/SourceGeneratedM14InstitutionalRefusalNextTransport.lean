import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation.SourceGeneratedM14RefusalCultureRepresentation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation.SourceInstalledM14InstitutionalCultureFace

/-!
# Source-generated cross-root refusal-next transport

The institutional root's current `1` occurrence and the anti-retaliation
target outer occurrence belong to different roots.  They are not identified.
Both are generated from the same exact right Payment: the platform paid U8
generates the widened institutional continuation, while that Payment's paid
successor generates the post-settlement target outer occurrence.

This file packages the two exact singleton restrictions, their constructive
presentation, and both native successor receipts.  The presentation is legal
because its source record retains the common Payment and does not claim an
ambient occurrence equality.  No projection coface or revised quotient is
created here.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Refusal
namespace Transport

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation

noncomputable section

abbrev M14InstitutionalRefusalSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence :
      (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).toRoot.actual.OccurrenceAt (1 : Nat) //
    occurrence =
      (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted 1 }

def m14InstitutionalRefusalSourceNextOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14InstitutionalRefusalSourceNextOccurrenceAt oldVisit sourceIndex
      boundary :=
  ⟨(m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).emitted 1, rfl⟩

def m14InstitutionalRefusalTargetRestrictionAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary :=
  ⟨(m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
    ).standingRenewal.targetOuterAuthority, rfl⟩

def m14InstitutionalRefusalNextPresentationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ConstructivePresentation
      (M14InstitutionalRefusalSourceNextOccurrenceAt oldVisit sourceIndex
        boundary)
      (M14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary) where
  forward := fun _source =>
    ⟨(m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary
      ).standingRenewal.targetOuterAuthority, rfl⟩
  backward := fun _target =>
    m14InstitutionalRefusalSourceNextOccurrenceAt oldVisit sourceIndex
      boundary
  backward_forward := by
    intro source
    apply Subtype.ext
    exact source.property.symm
  forward_backward := by
    intro target
    apply Subtype.ext
    exact target.property.symm

structure SourceGeneratedM14InstitutionalRefusalNextTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) : Type 32 where
  private mk ::
  institutionalNext :
    M14InstitutionalRefusalSourceNextOccurrenceAt oldVisit sourceIndex boundary
  institutionalNextExact : institutionalNext =
    m14InstitutionalRefusalSourceNextOccurrenceAt oldVisit sourceIndex
      boundary
  refusalTarget : M14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary
  refusalTargetExact : refusalTarget =
    m14InstitutionalRefusalTargetRestrictionAt oldVisit sourceIndex boundary
  occurrencePresentation : ConstructivePresentation
    (M14InstitutionalRefusalSourceNextOccurrenceAt oldVisit sourceIndex
      boundary)
    (M14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary)
  occurrencePresentationExact : occurrencePresentation =
    m14InstitutionalRefusalNextPresentationAt oldVisit sourceIndex boundary
  commonRightPayment : type_of%
    (ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightReplayAt
      oldVisit sourceIndex boundary).2.payment
  refusalSourcePaymentExact :
    (m14RefusalAntiRetaliationAt oldVisit sourceIndex boundary).sourcePayment =
      commonRightPayment
  institutionalNextGenerated : type_of%
    (m14InstitutionalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
      boundary 0)
  refusalTargetGenerated : type_of%
    (m14RefusalPlatformChannelNext_isTargetOuterOccurrence oldVisit sourceIndex
      boundary)

def sourceGeneratedM14InstitutionalRefusalNextTransportAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceGeneratedM14InstitutionalRefusalNextTransportAt oldVisit sourceIndex
      boundary :=
  let target : M14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary :=
    m14InstitutionalRefusalTargetRestrictionAt oldVisit sourceIndex boundary
  { institutionalNext :=
      m14InstitutionalRefusalSourceNextOccurrenceAt oldVisit sourceIndex
        boundary
    institutionalNextExact := rfl
    refusalTarget := target
    refusalTargetExact := rfl
    occurrencePresentation :=
      m14InstitutionalRefusalNextPresentationAt oldVisit sourceIndex boundary
    occurrencePresentationExact := rfl
    commonRightPayment :=
      (ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8.rightReplayAt
        oldVisit sourceIndex boundary).2.payment
    refusalSourcePaymentExact :=
      m14RefusalSourcePayment_eq_rightPayment oldVisit sourceIndex boundary
    institutionalNextGenerated :=
      m14InstitutionalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
        boundary 0
    refusalTargetGenerated :=
      m14RefusalPlatformChannelNext_isTargetOuterOccurrence oldVisit
        sourceIndex boundary }

@[simp] theorem m14InstitutionalRefusalNextPresentation_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14InstitutionalRefusalNextPresentationAt oldVisit sourceIndex boundary
      ).forward
        (m14InstitutionalRefusalSourceNextOccurrenceAt oldVisit sourceIndex
          boundary) =
      (sourceGeneratedM14InstitutionalRefusalNextTransportAt oldVisit
        sourceIndex boundary).refusalTarget :=
  rfl

theorem sourceGeneratedM14InstitutionalRefusalNextTransport_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let transport :=
      sourceGeneratedM14InstitutionalRefusalNextTransportAt oldVisit
        sourceIndex boundary
    Nonempty (SourceGeneratedM14InstitutionalRefusalNextTransportAt oldVisit
        sourceIndex boundary) ∧
      transport.occurrencePresentation.forward transport.institutionalNext =
        transport.refusalTarget ∧
      transport.refusalSourcePaymentExact =
        m14RefusalSourcePayment_eq_rightPayment oldVisit sourceIndex boundary ∧
      type_of% transport.institutionalNextGenerated ∧
      type_of% transport.refusalTargetGenerated ∧
      type_of% (m14RefusalCultureRepresentation_directConsumer oldVisit
        sourceIndex boundary
          (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary)) := by
  let transport :=
    sourceGeneratedM14InstitutionalRefusalNextTransportAt oldVisit sourceIndex
      boundary
  exact ⟨⟨transport⟩, rfl, rfl,
    transport.institutionalNextGenerated,
    transport.refusalTargetGenerated,
    m14RefusalCultureRepresentation_directConsumer oldVisit sourceIndex
      boundary (m14RefusalTargetOccurrenceAt oldVisit sourceIndex boundary)⟩

end
end Transport
end Refusal
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Transport.m14InstitutionalRefusalNextPresentationAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Transport.m14InstitutionalRefusalNextPresentation_commutes
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Transport.sourceGeneratedM14InstitutionalRefusalNextTransport_directConsumer

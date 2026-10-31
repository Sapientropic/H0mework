import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Installation.SourceInstalledM14UrbanCultureFace

/-!
# Whole regression for the urban culture face

The exact periodic route root, blocked/restored restrictions, independent
accessibility/capacity consumers, updated quotient and current-`5` coface are
checked together.  Retyping controls reject fake repairs and the root token
stores no route receipt, whole-ledger proof, factorization or next.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Urban
namespace Regression

open ProcessGame Society
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Transport
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Installation

noncomputable section

def rootInstalledM14UrbanCultureFaceReadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :=
  ((m14UrbanCulturePayloadAt oldVisit sourceIndex boundary).2 occurrence
    ).read occurrence

@[simp] theorem rootInstalledM14UrbanCultureFaceRead_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    rootInstalledM14UrbanCultureFaceReadAt oldVisit sourceIndex boundary
        occurrence =
      m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence :=
  rfl

theorem rootInstalledM14UrbanCultureKernelExactAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14UrbanConsumersAt oldVisit sourceIndex boundary)
      (rootInstalledM14UrbanCultureFaceReadAt oldVisit sourceIndex
        boundary) := by
  intro left right
  simpa only [rootInstalledM14UrbanCultureFaceRead_exact] using
    m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary left right

noncomputable def rootInstalledM14UrbanCultureQuotientEquivRangeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14UrbanConsumersAt oldVisit sourceIndex boundary).Quotient ≃
      Set.range (rootInstalledM14UrbanCultureFaceReadAt oldVisit sourceIndex
        boundary) :=
  (rootInstalledM14UrbanCultureKernelExactAt oldVisit sourceIndex boundary
    ).quotientEquivRange

theorem rootInstalledM14UrbanCultureEveryConsumer_uniqueFactorizationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (consumer : (m14UrbanConsumersAt oldVisit sourceIndex boundary).Consumer) :
    ∃! factor :
        Set.range (rootInstalledM14UrbanCultureFaceReadAt oldVisit sourceIndex
          boundary) →
          (m14UrbanConsumersAt oldVisit sourceIndex boundary).Output consumer,
      ∀ occurrence,
        factor
            ⟨rootInstalledM14UrbanCultureFaceReadAt oldVisit sourceIndex
                boundary occurrence,
              occurrence, rfl⟩ =
          (m14UrbanConsumersAt oldVisit sourceIndex boundary).read consumer
            occurrence :=
  (rootInstalledM14UrbanCultureKernelExactAt oldVisit sourceIndex boundary
    ).everyConsumer_unique_factorization consumer

theorem rootInstalledM14UrbanCulture_uniqueSourceIsoAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ∃! equivalence :
        Set.range (m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary) ≃
          Set.range (rootInstalledM14UrbanCultureFaceReadAt oldVisit
            sourceIndex boundary),
      ∀ occurrence,
        equivalence
            ⟨m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence,
              occurrence, rfl⟩ =
          ⟨rootInstalledM14UrbanCultureFaceReadAt oldVisit sourceIndex boundary
              occurrence,
            occurrence, rfl⟩ :=
  m14UrbanCompleteCarrier_uniqueIsoAt oldVisit sourceIndex boundary
    (rootInstalledM14UrbanCultureFaceReadAt oldVisit sourceIndex boundary)
    (rootInstalledM14UrbanCultureKernelExactAt oldVisit sourceIndex boundary)

theorem m14UrbanCultureInheritedArtProductionOutcome_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).projectionOutcomeAt
        ((m14UrbanCultureArtProductionInstallationAt oldVisit sourceIndex
          boundary).embed PUnit.unit) 4 =
      .inl ⟨m14ArtProductionCultureActiveAt oldVisit sourceIndex boundary,
        m14ArtProductionCulturePayloadAt oldVisit sourceIndex boundary⟩ :=
  rfl

theorem m14UrbanCulture_blockedRestoredHostile
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (m14UrbanSpatialOccurrences_sameRootAndCrossing oldVisit
      sourceIndex boundary) ∧
      m14UrbanOldArtProductionFaceReadAt oldVisit sourceIndex boundary
          (m14UrbanBlockedOccurrenceAt oldVisit sourceIndex boundary) =
        m14UrbanOldArtProductionFaceReadAt oldVisit sourceIndex boundary
          (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary) ∧
      m14UrbanAccessibilityReadAt
          (m14UrbanBlockedOccurrenceAt oldVisit sourceIndex boundary) ≠
        m14UrbanAccessibilityReadAt
          (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary) ∧
      m14UrbanCapacityReadAt
          (m14UrbanBlockedOccurrenceAt oldVisit sourceIndex boundary) ≠
        m14UrbanCapacityReadAt
          (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary) ∧
      type_of% (m14UrbanRetypingNoForgery_directConsumer oldVisit sourceIndex
        boundary) ∧
      type_of% (m14UrbanCultureKernelEscapeAt oldVisit sourceIndex boundary) :=
  ⟨m14UrbanSpatialOccurrences_sameRootAndCrossing oldVisit sourceIndex
      boundary,
    m14UrbanOldArtProductionFace_blocked_eq_restored oldVisit sourceIndex
      boundary,
    (m14UrbanSpatialRead_blocked_ne_restored oldVisit sourceIndex boundary).1,
    (m14UrbanSpatialRead_blocked_ne_restored oldVisit sourceIndex boundary).2,
    m14UrbanRetypingNoForgery_directConsumer oldVisit sourceIndex boundary,
    m14UrbanCultureKernelEscapeAt oldVisit sourceIndex boundary⟩

/- Root tokens contain none of the high route source or downstream results. -/
/-- error: Invalid field `routeReceipt` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14UrbanCulturePayloadAt oldVisit 0 0).2
    (m14UrbanRestoredOccurrenceAt oldVisit 0 0)).routeReceipt

/-- error: Invalid field `rootOccurrence` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14UrbanCulturePayloadAt oldVisit 0 0).2
    (m14UrbanRestoredOccurrenceAt oldVisit 0 0)).rootOccurrence

/-- error: Invalid field `wholeLedger` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14UrbanCulturePayloadAt oldVisit 0 0).2
    (m14UrbanRestoredOccurrenceAt oldVisit 0 0)).wholeLedger

/-- error: Invalid field `factorization` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14UrbanCulturePayloadAt oldVisit 0 0).2
    (m14UrbanRestoredOccurrenceAt oldVisit 0 0)).factorization

/-- error: Invalid field `generatedNext` -/
#guard_msgs (substring := true) in
#check fun (oldVisit : OldVisit) =>
  ((m14UrbanCulturePayloadAt oldVisit 0 0).2
    (m14UrbanRestoredOccurrenceAt oldVisit 0 0)).generatedNext

theorem sourceInstalledM14UrbanCultureRepresentation_wholeRegression
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceNativeM14UrbanSpatialCoordinates_directConsumer oldVisit
      sourceIndex boundary) ∧
      type_of% (m14UrbanSpatialConsumer_grounded oldVisit sourceIndex
        boundary) ∧
      type_of% (sourceGeneratedM14UrbanCultureMaterial_directConsumer oldVisit
        sourceIndex boundary
          (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary)) ∧
      type_of% (m14UrbanCultureRepresentation_directConsumer oldVisit
        sourceIndex boundary
          (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary)) ∧
      type_of% (sourceGeneratedM14ArtUrbanRouteTransport_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (sourceInstalledM14UrbanCultureFace_directConsumer oldVisit
        sourceIndex boundary) ∧
      type_of% (rootInstalledM14UrbanCultureKernelExactAt oldVisit sourceIndex
        boundary) ∧
      Nonempty
        ((m14UrbanConsumersAt oldVisit sourceIndex boundary).Quotient ≃
          Set.range (rootInstalledM14UrbanCultureFaceReadAt oldVisit sourceIndex
            boundary)) ∧
      (∀ consumer,
        type_of% (rootInstalledM14UrbanCultureEveryConsumer_uniqueFactorizationAt
          oldVisit sourceIndex boundary consumer)) ∧
      type_of% (rootInstalledM14UrbanCulture_uniqueSourceIsoAt oldVisit
        sourceIndex boundary) ∧
      type_of% (m14UrbanCultureInheritedArtProductionOutcome_exact oldVisit
        sourceIndex boundary) ∧
      type_of% (m14UrbanCulture_blockedRestoredHostile oldVisit sourceIndex
        boundary) ∧
      type_of% (m14UrbanCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
        boundary 5) :=
  ⟨sourceNativeM14UrbanSpatialCoordinates_directConsumer oldVisit sourceIndex
      boundary,
    m14UrbanSpatialConsumer_grounded oldVisit sourceIndex boundary,
    sourceGeneratedM14UrbanCultureMaterial_directConsumer oldVisit sourceIndex
      boundary (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary),
    m14UrbanCultureRepresentation_directConsumer oldVisit sourceIndex boundary
      (m14UrbanRestoredOccurrenceAt oldVisit sourceIndex boundary),
    sourceGeneratedM14ArtUrbanRouteTransport_directConsumer oldVisit
      sourceIndex boundary,
    sourceInstalledM14UrbanCultureFace_directConsumer oldVisit sourceIndex
      boundary,
    rootInstalledM14UrbanCultureKernelExactAt oldVisit sourceIndex boundary,
    ⟨rootInstalledM14UrbanCultureQuotientEquivRangeAt oldVisit sourceIndex
      boundary⟩,
    rootInstalledM14UrbanCultureEveryConsumer_uniqueFactorizationAt oldVisit
      sourceIndex boundary,
    rootInstalledM14UrbanCulture_uniqueSourceIsoAt oldVisit sourceIndex
      boundary,
    m14UrbanCultureInheritedArtProductionOutcome_exact oldVisit sourceIndex
      boundary,
    m14UrbanCulture_blockedRestoredHostile oldVisit sourceIndex boundary,
    m14UrbanCulture_generatedNextCurrentAt_eq oldVisit sourceIndex boundary
      5⟩

end
end Regression
end Urban
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Regression.m14UrbanCultureInheritedArtProductionOutcome_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Regression.m14UrbanCulture_blockedRestoredHostile
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Regression.sourceInstalledM14UrbanCultureRepresentation_wholeRegression

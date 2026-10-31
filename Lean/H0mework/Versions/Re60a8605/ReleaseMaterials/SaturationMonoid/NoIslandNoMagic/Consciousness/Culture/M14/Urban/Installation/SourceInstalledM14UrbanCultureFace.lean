import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Transport.SourceGeneratedM14ArtUrbanRouteTransport

/-!
# Urban culture face installed at art-production current five

The base is the art-production culture authority source.  A projection coface
active only at current `5` stores canonical whole-ledger evolution and the
private Type-0 urban face family.  All earlier inventory is inherited and the
widened root generates current `6`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Urban
namespace Installation

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Transport

noncomputable section

abbrev M14UrbanCultureBaseAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  m14ArtProductionCultureAuthoritySourceAt oldVisit sourceIndex boundary

abbrev M14UrbanCultureBaseLedgerSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14UrbanCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).restructuringSource.toLedgerSource

abbrev RootGeneratedM14UrbanCultureFamilyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary →
    SourceGeneratedM14UrbanCultureFaceTokenAt oldVisit sourceIndex boundary

def m14UrbanCultureProjectionLawAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw
      (M14UrbanCultureBaseLedgerSourceAt oldVisit sourceIndex boundary) where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (current = (5 : Nat))
  InactiveAt := fun _ {current} _occurrence => PLift (current ≠ (5 : Nat))
  classify := by
    intro _ current _occurrence
    by_cases currentExact : current = (5 : Nat)
    · exact .inl ⟨currentExact⟩
    · exact .inr ⟨currentExact⟩
  PayloadAt := fun _ {_current} occurrence _active =>
    SourceNativeLedgerEvolutionAt
        (M14UrbanCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
          ).source occurrence ×
      RootGeneratedM14UrbanCultureFamilyAt oldVisit sourceIndex boundary
  project := fun _ {_current} occurrence _active =>
    ⟨(M14UrbanCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
      ).ledgerCompiler.compile occurrence,
      fun urbanOccurrence =>
        generateM14UrbanCultureFaceTokenAt oldVisit sourceIndex boundary
          urbanOccurrence⟩

def m14UrbanCultureAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14UrbanCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).withProjectionCoface
      (m14UrbanCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14UrbanCultureComponentInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (m14UrbanCultureProjectionLawAt oldVisit sourceIndex boundary)
      (m14UrbanCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (M14UrbanCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (m14UrbanCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14UrbanCultureInheritedInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (M14UrbanCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw
      (m14UrbanCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (M14UrbanCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (m14UrbanCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14UrbanCultureArtProductionInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionCultureComponentInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14UrbanCultureTeachingInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionCultureTeachingInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14UrbanCultureClassPriceInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionCultureClassPriceInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14UrbanCultureRefusalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionCultureRefusalInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14UrbanCultureInstitutionalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionCultureInstitutionalInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14UrbanCulturePlatformInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionCulturePlatformInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14UrbanCultureObserverInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionCultureObserverInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14UrbanCultureAuthoritativeRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source := m14UrbanCultureAuthoritySourceAt oldVisit sourceIndex boundary
  emitted := (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex
    boundary).emitted
  compiler_commutes :=
    (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).compiler_commutes

def m14UrbanCultureLivingRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  (m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem m14UrbanCulture_emitted_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted current =
      (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted current :=
  rfl

def m14UrbanCultureActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14UrbanCultureProjectionLawAt oldVisit sourceIndex boundary).ActiveAt
      PUnit.unit
      ((m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted 5) :=
  ⟨rfl⟩

def m14UrbanCulturePayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14UrbanCultureProjectionLawAt oldVisit sourceIndex boundary).project
    PUnit.unit
    ((m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted 5)
    (m14UrbanCultureActiveAt oldVisit sourceIndex boundary)

@[simp] theorem m14UrbanCulturePayload_wholeLedger_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14UrbanCulturePayloadAt oldVisit sourceIndex boundary).1 =
      (M14UrbanCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
        ).ledgerCompiler.compile
          ((m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary
            ).emitted 5) :=
  rfl

@[simp] theorem m14UrbanCulturePayload_face_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14UrbanSpatialOccurrenceAt oldVisit sourceIndex boundary) :
    ((m14UrbanCulturePayloadAt oldVisit sourceIndex boundary).2 occurrence
      ).read occurrence =
      m14UrbanCultureFaceReadAt oldVisit sourceIndex boundary occurrence :=
  rfl

theorem m14UrbanCulturePayload_kernelExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14UrbanConsumersAt oldVisit sourceIndex boundary)
      (fun occurrence =>
        ((m14UrbanCulturePayloadAt oldVisit sourceIndex boundary).2 occurrence
          ).read occurrence) := by
  intro left right
  simpa only [m14UrbanCulturePayload_face_exact] using
    m14UrbanCultureKernelExactAt oldVisit sourceIndex boundary left right

theorem m14UrbanCultureComponentOutcome_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).projectionOutcomeAt
        ((m14UrbanCultureComponentInstallationAt oldVisit sourceIndex boundary
          ).embed PUnit.unit) 5 =
      .inl ⟨m14UrbanCultureActiveAt oldVisit sourceIndex boundary,
        m14UrbanCulturePayloadAt oldVisit sourceIndex boundary⟩ :=
  rfl

def m14UrbanCultureVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nat → RootVisit
      (m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary).toRoot
  | 0 =>
      (m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.initialVisit
  | index + 1 =>
      (m14UrbanCultureVisitAt oldVisit sourceIndex boundary index).next rfl

def m14UrbanCultureTemporalVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (m14UrbanCultureLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (m14UrbanCultureVisitAt oldVisit sourceIndex boundary index)

theorem m14UrbanCulture_generatedNextCurrentAt_eq
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (m14UrbanCultureLivingRootAt oldVisit sourceIndex boundary
      ).generatedNextCurrentAt
        (m14UrbanCultureTemporalVisitAt oldVisit sourceIndex boundary index) =
      ⟨AugmentedNewVAt oldVisit sourceIndex boundary,
        m14UrbanCultureAuthoritativeRootAt oldVisit sourceIndex boundary,
        m14UrbanCultureTemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)⟩ := by
  cases index <;> rfl

theorem sourceInstalledM14UrbanCultureFace_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceGeneratedM14ArtUrbanRouteTransport_directConsumer oldVisit
      sourceIndex boundary) ∧
      type_of% (m14UrbanCultureComponentOutcome_exact oldVisit sourceIndex
        boundary) ∧
      Function.Injective
        (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary
          ).embed ∧
      type_of% (m14UrbanCulturePayload_kernelExact oldVisit sourceIndex
        boundary) ∧
      (∀ occurrence,
        type_of% (m14UrbanCulturePayload_face_exact oldVisit sourceIndex
          boundary occurrence)) ∧
      type_of% (m14UrbanCulturePayload_wholeLedger_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14UrbanCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
        boundary 5) :=
  ⟨sourceGeneratedM14ArtUrbanRouteTransport_directConsumer oldVisit sourceIndex
      boundary,
    m14UrbanCultureComponentOutcome_exact oldVisit sourceIndex boundary,
    (m14UrbanCultureInheritedInstallationAt oldVisit sourceIndex boundary
      ).embed_injective,
    m14UrbanCulturePayload_kernelExact oldVisit sourceIndex boundary,
    m14UrbanCulturePayload_face_exact oldVisit sourceIndex boundary,
    m14UrbanCulturePayload_wholeLedger_exact oldVisit sourceIndex boundary,
    m14UrbanCulture_generatedNextCurrentAt_eq oldVisit sourceIndex boundary
      5⟩

end
end Installation
end Urban
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Installation.m14UrbanCultureComponentOutcome_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Installation.m14UrbanCulturePayload_kernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Installation.m14UrbanCulture_generatedNextCurrentAt_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Urban.Installation.sourceInstalledM14UrbanCultureFace_directConsumer

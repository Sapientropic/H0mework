import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Transport.SourceGeneratedM14TeachingArtProductionMaterialTransport

/-!
# Art-production culture face installed at teaching current four

The base is the teaching culture authority source.  A projection coface active
only at current `4` stores the canonical whole-ledger evolution and private
low-universe art-production face family.  All prior inventory is inherited;
the widened root generates current `5`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ArtProduction
namespace Installation

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Transport

noncomputable section

abbrev M14ArtProductionCultureBaseAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  m14TeachingCultureAuthoritySourceAt oldVisit sourceIndex boundary

abbrev M14ArtProductionCultureBaseLedgerSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14ArtProductionCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).restructuringSource.toLedgerSource

abbrev RootGeneratedM14ArtProductionCultureFamilyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary →
    SourceGeneratedM14ArtProductionCultureFaceTokenAt oldVisit sourceIndex
      boundary

def m14ArtProductionCultureProjectionLawAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw
      (M14ArtProductionCultureBaseLedgerSourceAt oldVisit sourceIndex
        boundary) where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (current = (4 : Nat))
  InactiveAt := fun _ {current} _occurrence => PLift (current ≠ (4 : Nat))
  classify := by
    intro _ current _occurrence
    by_cases currentExact : current = (4 : Nat)
    · exact .inl ⟨currentExact⟩
    · exact .inr ⟨currentExact⟩
  PayloadAt := fun _ {_current} occurrence _active =>
    SourceNativeLedgerEvolutionAt
        (M14ArtProductionCultureBaseLedgerSourceAt oldVisit sourceIndex
          boundary).source occurrence ×
      RootGeneratedM14ArtProductionCultureFamilyAt oldVisit sourceIndex
        boundary
  project := fun _ {_current} occurrence _active =>
    ⟨(M14ArtProductionCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
      ).ledgerCompiler.compile occurrence,
      fun artOccurrence =>
        generateM14ArtProductionCultureFaceTokenAt oldVisit sourceIndex
          boundary artOccurrence⟩

def m14ArtProductionCultureAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14ArtProductionCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).withProjectionCoface
      (m14ArtProductionCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14ArtProductionCultureComponentInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (m14ArtProductionCultureProjectionLawAt oldVisit sourceIndex boundary)
      (m14ArtProductionCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (M14ArtProductionCultureBaseAuthoritySourceAt oldVisit sourceIndex
      boundary)
    (m14ArtProductionCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14ArtProductionCultureInheritedInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (M14ArtProductionCultureBaseAuthoritySourceAt oldVisit sourceIndex
        boundary).projectionLaw
      (m14ArtProductionCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (M14ArtProductionCultureBaseAuthoritySourceAt oldVisit sourceIndex
      boundary)
    (m14ArtProductionCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14ArtProductionCultureTeachingInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingCultureComponentInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14ArtProductionCultureInheritedInstallationAt oldVisit sourceIndex
        boundary)

def m14ArtProductionCultureClassPriceInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingCultureClassPriceInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14ArtProductionCultureInheritedInstallationAt oldVisit sourceIndex
        boundary)

def m14ArtProductionCultureRefusalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingCultureRefusalInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14ArtProductionCultureInheritedInstallationAt oldVisit sourceIndex
        boundary)

def m14ArtProductionCultureInstitutionalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingCultureInstitutionalInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14ArtProductionCultureInheritedInstallationAt oldVisit sourceIndex
        boundary)

def m14ArtProductionCulturePlatformInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingCulturePlatformInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14ArtProductionCultureInheritedInstallationAt oldVisit sourceIndex
        boundary)

def m14ArtProductionCultureObserverInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingCultureObserverInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14ArtProductionCultureInheritedInstallationAt oldVisit sourceIndex
        boundary)

def m14ArtProductionCultureAuthoritativeRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source := m14ArtProductionCultureAuthoritySourceAt oldVisit sourceIndex
    boundary
  emitted :=
    (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted
  compiler_commutes :=
    (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).compiler_commutes

def m14ArtProductionCultureLivingRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem m14ArtProductionCulture_emitted_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted current =
      (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted current :=
  rfl

def m14ArtProductionCultureActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtProductionCultureProjectionLawAt oldVisit sourceIndex boundary
      ).ActiveAt PUnit.unit
      ((m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted 4) :=
  ⟨rfl⟩

def m14ArtProductionCulturePayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionCultureProjectionLawAt oldVisit sourceIndex boundary
    ).project PUnit.unit
      ((m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted 4)
      (m14ArtProductionCultureActiveAt oldVisit sourceIndex boundary)

@[simp] theorem m14ArtProductionCulturePayload_wholeLedger_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtProductionCulturePayloadAt oldVisit sourceIndex boundary).1 =
      (M14ArtProductionCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
        ).ledgerCompiler.compile
          ((m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex
            boundary).emitted 4) :=
  rfl

@[simp] theorem m14ArtProductionCulturePayload_face_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) :
    ((m14ArtProductionCulturePayloadAt oldVisit sourceIndex boundary).2
      occurrence).read occurrence =
      m14ArtProductionCultureFaceReadAt oldVisit sourceIndex boundary
        occurrence :=
  rfl

theorem m14ArtProductionCulturePayload_kernelExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14ArtProductionConsumersAt oldVisit sourceIndex boundary)
      (fun occurrence =>
        ((m14ArtProductionCulturePayloadAt oldVisit sourceIndex boundary).2
          occurrence).read occurrence) := by
  intro left right
  simpa only [m14ArtProductionCulturePayload_face_exact] using
    m14ArtProductionCultureKernelExactAt oldVisit sourceIndex boundary left
      right

theorem m14ArtProductionCultureComponentOutcome_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).projectionOutcomeAt
        ((m14ArtProductionCultureComponentInstallationAt oldVisit sourceIndex
          boundary).embed PUnit.unit) 4 =
      .inl ⟨m14ArtProductionCultureActiveAt oldVisit sourceIndex boundary,
        m14ArtProductionCulturePayloadAt oldVisit sourceIndex boundary⟩ :=
  rfl

def m14ArtProductionCultureVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nat → RootVisit
      (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot
  | 0 =>
      (m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.initialVisit
  | index + 1 =>
      (m14ArtProductionCultureVisitAt oldVisit sourceIndex boundary index
        ).next rfl

def m14ArtProductionCultureTemporalVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (m14ArtProductionCultureLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (m14ArtProductionCultureVisitAt oldVisit sourceIndex boundary index)

theorem m14ArtProductionCulture_generatedNextCurrentAt_eq
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (m14ArtProductionCultureLivingRootAt oldVisit sourceIndex boundary
      ).generatedNextCurrentAt
        (m14ArtProductionCultureTemporalVisitAt oldVisit sourceIndex boundary
          index) =
      ⟨AugmentedNewVAt oldVisit sourceIndex boundary,
        m14ArtProductionCultureAuthoritativeRootAt oldVisit sourceIndex
          boundary,
        m14ArtProductionCultureTemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)⟩ := by
  cases index <;> rfl

theorem sourceInstalledM14ArtProductionCultureFace_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of%
        (sourceGeneratedM14TeachingArtProductionMaterialTransport_directConsumer
          oldVisit sourceIndex boundary) ∧
      type_of% (m14ArtProductionCultureComponentOutcome_exact oldVisit
        sourceIndex boundary) ∧
      Function.Injective
        (m14ArtProductionCultureInheritedInstallationAt oldVisit sourceIndex
          boundary).embed ∧
      type_of% (m14ArtProductionCulturePayload_kernelExact oldVisit
        sourceIndex boundary) ∧
      (∀ occurrence,
        type_of% (m14ArtProductionCulturePayload_face_exact oldVisit
          sourceIndex boundary occurrence)) ∧
      type_of% (m14ArtProductionCulturePayload_wholeLedger_exact oldVisit
        sourceIndex boundary) ∧
      type_of% (m14ArtProductionCulture_generatedNextCurrentAt_eq oldVisit
        sourceIndex boundary 4) :=
  ⟨sourceGeneratedM14TeachingArtProductionMaterialTransport_directConsumer
      oldVisit sourceIndex boundary,
    m14ArtProductionCultureComponentOutcome_exact oldVisit sourceIndex
      boundary,
    (m14ArtProductionCultureInheritedInstallationAt oldVisit sourceIndex
      boundary).embed_injective,
    m14ArtProductionCulturePayload_kernelExact oldVisit sourceIndex boundary,
    m14ArtProductionCulturePayload_face_exact oldVisit sourceIndex boundary,
    m14ArtProductionCulturePayload_wholeLedger_exact oldVisit sourceIndex
      boundary,
    m14ArtProductionCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
      boundary 4⟩

end
end Installation
end ArtProduction
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Installation.m14ArtProductionCultureComponentOutcome_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Installation.m14ArtProductionCulturePayload_kernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Installation.m14ArtProductionCulture_generatedNextCurrentAt_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Installation.sourceInstalledM14ArtProductionCultureFace_directConsumer

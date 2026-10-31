import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Transport.SourceGeneratedM14ClassPriceTeachingMaterialTransport

/-!
# Teaching culture face installed at class-price current three

The base is the class-price culture authority source.  A new projection
coface, active only at current `3`, stores the canonical whole-ledger evolution
and a private low-universe teaching face family.  All previous inventory and
root compilation are inherited; the widened root generates current `4`.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Teaching
namespace Installation

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Transport

noncomputable section

abbrev M14TeachingCultureBaseAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  m14StructuralClassPriceCultureAuthoritySourceAt oldVisit sourceIndex
    boundary

abbrev M14TeachingCultureBaseLedgerSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14TeachingCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).restructuringSource.toLedgerSource

abbrev RootGeneratedM14TeachingCultureFamilyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14TeachingOccurrenceAt oldVisit sourceIndex boundary →
    SourceGeneratedM14TeachingCultureFaceTokenAt oldVisit sourceIndex boundary

def m14TeachingCultureProjectionLawAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw
      (M14TeachingCultureBaseLedgerSourceAt oldVisit sourceIndex boundary) where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (current = (3 : Nat))
  InactiveAt := fun _ {current} _occurrence => PLift (current ≠ (3 : Nat))
  classify := by
    intro _ current _occurrence
    by_cases currentExact : current = (3 : Nat)
    · exact .inl ⟨currentExact⟩
    · exact .inr ⟨currentExact⟩
  PayloadAt := fun _ {_current} occurrence _active =>
    SourceNativeLedgerEvolutionAt
        (M14TeachingCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
          ).source occurrence ×
      RootGeneratedM14TeachingCultureFamilyAt oldVisit sourceIndex boundary
  project := fun _ {_current} occurrence _active =>
    ⟨(M14TeachingCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
      ).ledgerCompiler.compile occurrence,
      fun teachingOccurrence =>
        generateM14TeachingCultureFaceTokenAt oldVisit sourceIndex boundary
          teachingOccurrence⟩

def m14TeachingCultureAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14TeachingCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).withProjectionCoface
      (m14TeachingCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14TeachingCultureComponentInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (m14TeachingCultureProjectionLawAt oldVisit sourceIndex boundary)
      (m14TeachingCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (M14TeachingCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (m14TeachingCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14TeachingCultureInheritedInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (M14TeachingCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw
      (m14TeachingCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (M14TeachingCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (m14TeachingCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14TeachingCultureClassPriceInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceCultureComponentInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14TeachingCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14TeachingCultureRefusalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceCultureRefusalInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14TeachingCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14TeachingCultureInstitutionalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceCultureInstitutionalInstallationAt oldVisit
    sourceIndex boundary).trans
      (m14TeachingCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14TeachingCulturePlatformInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceCulturePlatformInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14TeachingCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14TeachingCultureObserverInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceCultureObserverInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14TeachingCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14TeachingCultureAuthoritativeRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source := m14TeachingCultureAuthoritySourceAt oldVisit sourceIndex boundary
  emitted := (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit
    sourceIndex boundary).emitted
  compiler_commutes :=
    (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
      boundary).compiler_commutes

def m14TeachingCultureLivingRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem m14TeachingCulture_emitted_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted current =
      (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted current :=
  rfl

def m14TeachingCultureActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14TeachingCultureProjectionLawAt oldVisit sourceIndex boundary).ActiveAt
      PUnit.unit
      ((m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted 3) :=
  ⟨rfl⟩

def m14TeachingCulturePayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingCultureProjectionLawAt oldVisit sourceIndex boundary).project
    PUnit.unit
    ((m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted 3)
    (m14TeachingCultureActiveAt oldVisit sourceIndex boundary)

@[simp] theorem m14TeachingCulturePayload_wholeLedger_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14TeachingCulturePayloadAt oldVisit sourceIndex boundary).1 =
      (M14TeachingCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
        ).ledgerCompiler.compile
          ((m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
            ).emitted 3) :=
  rfl

@[simp] theorem m14TeachingCulturePayload_face_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14TeachingOccurrenceAt oldVisit sourceIndex boundary) :
    ((m14TeachingCulturePayloadAt oldVisit sourceIndex boundary).2 occurrence
      ).read occurrence =
      m14TeachingCultureFaceReadAt oldVisit sourceIndex boundary occurrence :=
  rfl

theorem m14TeachingCulturePayload_kernelExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14TeachingConsumersAt oldVisit sourceIndex boundary)
      (fun occurrence =>
        ((m14TeachingCulturePayloadAt oldVisit sourceIndex boundary).2
          occurrence).read occurrence) := by
  intro left right
  simpa only [m14TeachingCulturePayload_face_exact] using
    m14TeachingCultureKernelExactAt oldVisit sourceIndex boundary left right

theorem m14TeachingCultureComponentOutcome_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).projectionOutcomeAt
        ((m14TeachingCultureComponentInstallationAt oldVisit sourceIndex
          boundary).embed PUnit.unit) 3 =
      .inl ⟨m14TeachingCultureActiveAt oldVisit sourceIndex boundary,
        m14TeachingCulturePayloadAt oldVisit sourceIndex boundary⟩ :=
  rfl

def m14TeachingCultureVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nat → RootVisit
      (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot
  | 0 =>
      (m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.initialVisit
  | index + 1 =>
      (m14TeachingCultureVisitAt oldVisit sourceIndex boundary index).next rfl

def m14TeachingCultureTemporalVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (m14TeachingCultureLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (m14TeachingCultureVisitAt oldVisit sourceIndex boundary index)

theorem m14TeachingCulture_generatedNextCurrentAt_eq
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (m14TeachingCultureLivingRootAt oldVisit sourceIndex boundary
      ).generatedNextCurrentAt
        (m14TeachingCultureTemporalVisitAt oldVisit sourceIndex boundary
          index) =
      ⟨AugmentedNewVAt oldVisit sourceIndex boundary,
        m14TeachingCultureAuthoritativeRootAt oldVisit sourceIndex boundary,
        m14TeachingCultureTemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)⟩ := by
  cases index <;> rfl

theorem sourceInstalledM14TeachingCultureFace_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of%
        (sourceGeneratedM14ClassPriceTeachingMaterialTransport_directConsumer
          oldVisit sourceIndex boundary) ∧
      type_of% (m14TeachingCultureComponentOutcome_exact oldVisit sourceIndex
        boundary) ∧
      Function.Injective
        (m14TeachingCultureInheritedInstallationAt oldVisit sourceIndex
          boundary).embed ∧
      type_of% (m14TeachingCulturePayload_kernelExact oldVisit sourceIndex
        boundary) ∧
      (∀ occurrence,
        type_of% (m14TeachingCulturePayload_face_exact oldVisit sourceIndex
          boundary occurrence)) ∧
      type_of% (m14TeachingCulturePayload_wholeLedger_exact oldVisit
        sourceIndex boundary) ∧
      type_of% (m14TeachingCulture_generatedNextCurrentAt_eq oldVisit
        sourceIndex boundary 3) :=
  ⟨sourceGeneratedM14ClassPriceTeachingMaterialTransport_directConsumer
      oldVisit sourceIndex boundary,
    m14TeachingCultureComponentOutcome_exact oldVisit sourceIndex boundary,
    (m14TeachingCultureInheritedInstallationAt oldVisit sourceIndex boundary
      ).embed_injective,
    m14TeachingCulturePayload_kernelExact oldVisit sourceIndex boundary,
    m14TeachingCulturePayload_face_exact oldVisit sourceIndex boundary,
    m14TeachingCulturePayload_wholeLedger_exact oldVisit sourceIndex boundary,
    m14TeachingCulture_generatedNextCurrentAt_eq oldVisit sourceIndex boundary
      3⟩

end
end Installation
end Teaching
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Installation.m14TeachingCultureComponentOutcome_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Installation.m14TeachingCulturePayload_kernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Installation.m14TeachingCulture_generatedNextCurrentAt_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Installation.sourceInstalledM14TeachingCultureFace_directConsumer

import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Transport.SourceGeneratedM14RefusalStructuralClassPriceNextTransport

/-!
# Structural class-price culture face installed at refusal current two

The base is the refusal culture authority source.  Its native current `2`,
generated after the refusal coface at current `1`, is presented to the exact
next-cycle target Payment.  A new projection coface stores only the canonical
whole-ledger evolution and a private family of low-universe class-price face
tokens.

All previous projection inventory, emitter, ledger compiler and law surface
are inherited.  The widened root then generates current `3` natively.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ClassPrice
namespace Installation

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Transport

noncomputable section

abbrev M14StructuralClassPriceCultureBaseAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  m14RefusalCultureAuthoritySourceAt oldVisit sourceIndex boundary

abbrev M14StructuralClassPriceCultureBaseLedgerSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14StructuralClassPriceCultureBaseAuthoritySourceAt oldVisit sourceIndex
    boundary).restructuringSource.toLedgerSource

abbrev RootGeneratedM14StructuralClassPriceCultureFamilyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
    boundary) →
    SourceGeneratedM14StructuralClassPriceCultureFaceTokenAt oldVisit
      sourceIndex boundary occurrence

def m14StructuralClassPriceCultureProjectionLawAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw
      (M14StructuralClassPriceCultureBaseLedgerSourceAt oldVisit sourceIndex
        boundary) where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (current = (2 : Nat))
  InactiveAt := fun _ {current} _occurrence => PLift (current ≠ (2 : Nat))
  classify := by
    intro _ current _occurrence
    by_cases currentExact : current = (2 : Nat)
    · exact .inl ⟨currentExact⟩
    · exact .inr ⟨currentExact⟩
  PayloadAt := fun _ {_current} occurrence _active =>
    SourceNativeLedgerEvolutionAt
        (M14StructuralClassPriceCultureBaseLedgerSourceAt oldVisit sourceIndex
          boundary).source occurrence ×
      RootGeneratedM14StructuralClassPriceCultureFamilyAt oldVisit sourceIndex
        boundary
  project := fun _ {_current} occurrence _active =>
    ⟨(M14StructuralClassPriceCultureBaseLedgerSourceAt oldVisit sourceIndex
      boundary).ledgerCompiler.compile occurrence,
      fun classOccurrence =>
        generateM14StructuralClassPriceCultureFaceTokenAt oldVisit sourceIndex
          boundary classOccurrence⟩

def m14StructuralClassPriceCultureAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14StructuralClassPriceCultureBaseAuthoritySourceAt oldVisit sourceIndex
    boundary).withProjectionCoface
      (m14StructuralClassPriceCultureProjectionLawAt oldVisit sourceIndex
        boundary)

def m14StructuralClassPriceCultureComponentInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (m14StructuralClassPriceCultureProjectionLawAt oldVisit sourceIndex
        boundary)
      (m14StructuralClassPriceCultureAuthoritySourceAt oldVisit sourceIndex
        boundary).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (M14StructuralClassPriceCultureBaseAuthoritySourceAt oldVisit sourceIndex
      boundary)
    (m14StructuralClassPriceCultureProjectionLawAt oldVisit sourceIndex
      boundary)

def m14StructuralClassPriceCultureInheritedInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (M14StructuralClassPriceCultureBaseAuthoritySourceAt oldVisit sourceIndex
        boundary).projectionLaw
      (m14StructuralClassPriceCultureAuthoritySourceAt oldVisit sourceIndex
        boundary).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (M14StructuralClassPriceCultureBaseAuthoritySourceAt oldVisit sourceIndex
      boundary)
    (m14StructuralClassPriceCultureProjectionLawAt oldVisit sourceIndex
      boundary)

def m14StructuralClassPriceCultureRefusalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14RefusalCultureComponentInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14StructuralClassPriceCultureInheritedInstallationAt oldVisit
        sourceIndex boundary)

def m14StructuralClassPriceCultureInstitutionalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14RefusalCultureInstitutionalInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14StructuralClassPriceCultureInheritedInstallationAt oldVisit
        sourceIndex boundary)

def m14StructuralClassPriceCulturePlatformInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14RefusalCulturePlatformInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14StructuralClassPriceCultureInheritedInstallationAt oldVisit
        sourceIndex boundary)

def m14StructuralClassPriceCultureObserverInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14RefusalCultureObserverInstallationAt oldVisit sourceIndex boundary
    ).trans
      (m14StructuralClassPriceCultureInheritedInstallationAt oldVisit
        sourceIndex boundary)

def m14StructuralClassPriceCultureAuthoritativeRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source := m14StructuralClassPriceCultureAuthoritySourceAt oldVisit
    sourceIndex boundary
  emitted :=
    (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary).emitted
  compiler_commutes :=
    (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).compiler_commutes

def m14StructuralClassPriceCultureLivingRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
    boundary).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem m14StructuralClassPriceCulture_emitted_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
      boundary).emitted current =
      (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted current :=
  rfl

@[simp] theorem m14StructuralClassPriceCulture_generatedLedger_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
      boundary).generatedLedgerAt current =
      (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).generatedLedgerAt current :=
  rfl

def m14StructuralClassPriceCultureActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPriceCultureProjectionLawAt oldVisit sourceIndex
      boundary).ActiveAt PUnit.unit
      ((m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted 2) :=
  ⟨rfl⟩

def m14StructuralClassPriceCulturePayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14StructuralClassPriceCultureProjectionLawAt oldVisit sourceIndex
    boundary).project PUnit.unit
      ((m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted 2)
      (m14StructuralClassPriceCultureActiveAt oldVisit sourceIndex boundary)

@[simp] theorem m14StructuralClassPriceCulturePayload_wholeLedger_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPriceCulturePayloadAt oldVisit sourceIndex boundary).1 =
      (M14StructuralClassPriceCultureBaseLedgerSourceAt oldVisit sourceIndex
        boundary).ledgerCompiler.compile
          ((m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit
            sourceIndex boundary).emitted 2) :=
  rfl

@[simp] theorem m14StructuralClassPriceCulturePayload_face_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14StructuralClassPriceOccurrenceAt oldVisit sourceIndex
      boundary) :
    ((m14StructuralClassPriceCulturePayloadAt oldVisit sourceIndex boundary).2
      occurrence).read =
      m14StructuralClassPriceCultureFaceReadAt oldVisit sourceIndex boundary
        occurrence :=
  rfl

theorem m14StructuralClassPriceCulturePayload_kernelExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14StructuralClassPriceConsumersAt oldVisit sourceIndex boundary)
      (fun occurrence =>
        ((m14StructuralClassPriceCulturePayloadAt oldVisit sourceIndex
          boundary).2 occurrence).read) := by
  intro left right
  simpa only [m14StructuralClassPriceCulturePayload_face_exact] using
    m14StructuralClassPriceCultureKernelExactAt oldVisit sourceIndex boundary
      left right

theorem m14StructuralClassPriceCultureComponentOutcome_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
      boundary).projectionOutcomeAt
        ((m14StructuralClassPriceCultureComponentInstallationAt oldVisit
          sourceIndex boundary).embed PUnit.unit) 2 =
      .inl ⟨m14StructuralClassPriceCultureActiveAt oldVisit sourceIndex
          boundary,
        m14StructuralClassPriceCulturePayloadAt oldVisit sourceIndex boundary⟩ :=
  rfl

def m14StructuralClassPriceCultureVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nat → RootVisit
      (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).toRoot
  | 0 =>
      (m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).toRoot.initialVisit
  | index + 1 =>
      (m14StructuralClassPriceCultureVisitAt oldVisit sourceIndex boundary
        index).next rfl

def m14StructuralClassPriceCultureTemporalVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (m14StructuralClassPriceCultureLivingRootAt oldVisit sourceIndex
        boundary).toAuthoritativeRoot.toLedgerRoot :=
  .finite (m14StructuralClassPriceCultureVisitAt oldVisit sourceIndex boundary
    index)

theorem m14StructuralClassPriceCulture_generatedNextCurrentAt_eq
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (m14StructuralClassPriceCultureLivingRootAt oldVisit sourceIndex boundary
      ).generatedNextCurrentAt
        (m14StructuralClassPriceCultureTemporalVisitAt oldVisit sourceIndex
          boundary index) =
      ⟨AugmentedNewVAt oldVisit sourceIndex boundary,
        m14StructuralClassPriceCultureAuthoritativeRootAt oldVisit sourceIndex
          boundary,
        m14StructuralClassPriceCultureTemporalVisitAt oldVisit sourceIndex
          boundary (index + 1)⟩ := by
  cases index <;> rfl

theorem sourceInstalledM14StructuralClassPriceCultureFace_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of%
        (sourceGeneratedM14RefusalStructuralClassPriceNextTransport_directConsumer
          oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceCultureComponentOutcome_exact oldVisit
        sourceIndex boundary) ∧
      Function.Injective
        (m14StructuralClassPriceCultureInheritedInstallationAt oldVisit
          sourceIndex boundary).embed ∧
      type_of% (m14StructuralClassPriceCulturePayload_kernelExact oldVisit
        sourceIndex boundary) ∧
      (∀ occurrence,
        type_of% (m14StructuralClassPriceCulturePayload_face_exact oldVisit
          sourceIndex boundary occurrence)) ∧
      type_of% (m14StructuralClassPriceCulturePayload_wholeLedger_exact
        oldVisit sourceIndex boundary) ∧
      type_of% (m14StructuralClassPriceCulture_generatedNextCurrentAt_eq
        oldVisit sourceIndex boundary 2) :=
  ⟨sourceGeneratedM14RefusalStructuralClassPriceNextTransport_directConsumer
      oldVisit sourceIndex boundary,
    m14StructuralClassPriceCultureComponentOutcome_exact oldVisit sourceIndex
      boundary,
    (m14StructuralClassPriceCultureInheritedInstallationAt oldVisit
      sourceIndex boundary).embed_injective,
    m14StructuralClassPriceCulturePayload_kernelExact oldVisit sourceIndex
      boundary,
    m14StructuralClassPriceCulturePayload_face_exact oldVisit sourceIndex
      boundary,
    m14StructuralClassPriceCulturePayload_wholeLedger_exact oldVisit
      sourceIndex boundary,
    m14StructuralClassPriceCulture_generatedNextCurrentAt_eq oldVisit
      sourceIndex boundary 2⟩

end
end Installation
end ClassPrice
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation.m14StructuralClassPriceCultureComponentOutcome_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation.m14StructuralClassPriceCulturePayload_kernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation.m14StructuralClassPriceCulture_generatedNextCurrentAt_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ClassPrice.Installation.sourceInstalledM14StructuralClassPriceCultureFace_directConsumer

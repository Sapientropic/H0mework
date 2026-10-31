import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Transport.SourceGeneratedM14InstitutionalRefusalNextTransport

/-!
# Refusal culture face installed at institutional current one

The source-generated cross-root transport presents the institutional root's
exact current-`1` singleton as the distinct post-settlement refusal target
occurrence.  The refusal representation is therefore installed as a new
projection coface active only at current `1`.

The base is the already widened institutional culture authority source.  Its
current-`0` institutional face, platform/observer inventory, emitter, ledger
compiler, and temporal evolution are inherited injectively.  The new payload
is the canonical whole-ledger evolution together with a private Type-0 family
of refusal culture face tokens; no high-universe anti-retaliation certificate
is stored in the root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Refusal
namespace Installation

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Transport

noncomputable section

abbrev M14RefusalCultureBaseAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  m14InstitutionalCultureAuthoritySourceAt oldVisit sourceIndex boundary

abbrev M14RefusalCultureBaseLedgerSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14RefusalCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).restructuringSource.toLedgerSource

abbrev RootGeneratedM14RefusalCultureFamilyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) →
    SourceGeneratedM14RefusalCultureFaceTokenAt oldVisit sourceIndex boundary
      occurrence

def m14RefusalCultureProjectionLawAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw
      (M14RefusalCultureBaseLedgerSourceAt oldVisit sourceIndex boundary) where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (current = (1 : Nat))
  InactiveAt := fun _ {current} _occurrence => PLift (current ≠ (1 : Nat))
  classify := by
    intro _ current _occurrence
    by_cases currentExact : current = (1 : Nat)
    · exact .inl ⟨currentExact⟩
    · exact .inr ⟨currentExact⟩
  PayloadAt := fun _ {_current} occurrence _active =>
    SourceNativeLedgerEvolutionAt
        (M14RefusalCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
          ).source occurrence ×
      RootGeneratedM14RefusalCultureFamilyAt oldVisit sourceIndex boundary
  project := fun _ {_current} occurrence _active =>
    ⟨(M14RefusalCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
      ).ledgerCompiler.compile occurrence,
      fun refusalOccurrence => generateM14RefusalCultureFaceTokenAt oldVisit
        sourceIndex boundary refusalOccurrence⟩

def m14RefusalCultureAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14RefusalCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).withProjectionCoface
      (m14RefusalCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14RefusalCultureComponentInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (m14RefusalCultureProjectionLawAt oldVisit sourceIndex boundary)
      (m14RefusalCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (M14RefusalCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (m14RefusalCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14RefusalCultureInheritedInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (M14RefusalCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw
      (m14RefusalCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (M14RefusalCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary)
    (m14RefusalCultureProjectionLawAt oldVisit sourceIndex boundary)

/-- The current-0 institutional culture component survives the successor
installation. -/
def m14RefusalCultureInstitutionalInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14InstitutionalCultureComponentInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14RefusalCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14RefusalCulturePlatformInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14InstitutionalCulturePlatformInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14RefusalCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14RefusalCultureObserverInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14InstitutionalCultureObserverInstallationAt oldVisit sourceIndex
    boundary).trans
      (m14RefusalCultureInheritedInstallationAt oldVisit sourceIndex boundary)

def m14RefusalCultureAuthoritativeRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source := m14RefusalCultureAuthoritySourceAt oldVisit sourceIndex boundary
  emitted :=
    (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted
  compiler_commutes :=
    (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).compiler_commutes

def m14RefusalCultureLivingRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem m14RefusalCulture_emitted_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted current =
      (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted current :=
  rfl

@[simp] theorem m14RefusalCulture_generatedLedger_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).generatedLedgerAt current =
      (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).generatedLedgerAt current :=
  rfl

def m14RefusalCultureActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14RefusalCultureProjectionLawAt oldVisit sourceIndex boundary).ActiveAt
      PUnit.unit
      ((m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted 1) :=
  ⟨rfl⟩

def m14RefusalCulturePayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14RefusalCultureProjectionLawAt oldVisit sourceIndex boundary).project
    PUnit.unit
    ((m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted 1)
    (m14RefusalCultureActiveAt oldVisit sourceIndex boundary)

@[simp] theorem m14RefusalCulturePayload_wholeLedger_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14RefusalCulturePayloadAt oldVisit sourceIndex boundary).1 =
      (M14RefusalCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
        ).ledgerCompiler.compile
          ((m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
            ).emitted 1) :=
  rfl

@[simp] theorem m14RefusalCulturePayload_face_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (occurrence : M14RefusalOccurrenceAt oldVisit sourceIndex boundary) :
    ((m14RefusalCulturePayloadAt oldVisit sourceIndex boundary).2 occurrence
      ).read =
      m14RefusalCultureFaceReadAt oldVisit sourceIndex boundary occurrence :=
  rfl

theorem m14RefusalCulturePayload_kernelExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14RefusalCultureConsumersAt oldVisit sourceIndex boundary)
      (fun occurrence =>
        ((m14RefusalCulturePayloadAt oldVisit sourceIndex boundary).2
          occurrence).read) := by
  intro left right
  simpa only [m14RefusalCulturePayload_face_exact] using
    m14RefusalCultureKernelExactAt oldVisit sourceIndex boundary left right

theorem m14RefusalCultureComponentOutcome_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).projectionOutcomeAt
        ((m14RefusalCultureComponentInstallationAt oldVisit sourceIndex
          boundary).embed PUnit.unit) 1 =
      .inl ⟨m14RefusalCultureActiveAt oldVisit sourceIndex boundary,
        m14RefusalCulturePayloadAt oldVisit sourceIndex boundary⟩ :=
  rfl

def m14RefusalCultureVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nat → RootVisit
      (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot
  | 0 =>
      (m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
        ).toRoot.initialVisit
  | index + 1 =>
      (m14RefusalCultureVisitAt oldVisit sourceIndex boundary index).next rfl

def m14RefusalCultureTemporalVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (m14RefusalCultureLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite (m14RefusalCultureVisitAt oldVisit sourceIndex boundary index)

theorem m14RefusalCulture_generatedNextCurrentAt_eq
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (m14RefusalCultureLivingRootAt oldVisit sourceIndex boundary
      ).generatedNextCurrentAt
        (m14RefusalCultureTemporalVisitAt oldVisit sourceIndex boundary index) =
      ⟨AugmentedNewVAt oldVisit sourceIndex boundary,
        m14RefusalCultureAuthoritativeRootAt oldVisit sourceIndex boundary,
        m14RefusalCultureTemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)⟩ := by
  cases index <;> rfl

theorem sourceInstalledM14RefusalCultureFace_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceGeneratedM14InstitutionalRefusalNextTransport_directConsumer
      oldVisit sourceIndex boundary) ∧
      type_of% (m14RefusalCultureComponentOutcome_exact oldVisit sourceIndex
        boundary) ∧
      Function.Injective
        (m14RefusalCultureInheritedInstallationAt oldVisit sourceIndex
          boundary).embed ∧
      type_of% (m14RefusalCulturePayload_kernelExact oldVisit sourceIndex
        boundary) ∧
      (∀ occurrence,
        type_of% (m14RefusalCulturePayload_face_exact oldVisit sourceIndex
          boundary occurrence)) ∧
      type_of% (m14RefusalCulturePayload_wholeLedger_exact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14RefusalCulture_generatedNextCurrentAt_eq oldVisit
        sourceIndex boundary 1) :=
  ⟨sourceGeneratedM14InstitutionalRefusalNextTransport_directConsumer oldVisit
      sourceIndex boundary,
    m14RefusalCultureComponentOutcome_exact oldVisit sourceIndex boundary,
    (m14RefusalCultureInheritedInstallationAt oldVisit sourceIndex boundary
      ).embed_injective,
    m14RefusalCulturePayload_kernelExact oldVisit sourceIndex boundary,
    m14RefusalCulturePayload_face_exact oldVisit sourceIndex boundary,
    m14RefusalCulturePayload_wholeLedger_exact oldVisit sourceIndex boundary,
    m14RefusalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex boundary
      1⟩

end
end Installation
end Refusal
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation.m14RefusalCultureComponentOutcome_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation.m14RefusalCulturePayload_kernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation.m14RefusalCulture_generatedNextCurrentAt_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Refusal.Installation.sourceInstalledM14RefusalCultureFace_directConsumer

import H0mework.Realization.Faces.ProjectionCoface
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation.SourceGeneratedM14InstitutionalCultureRepresentation
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Installation.Runtime.Authority.SourceGeneratedCycleMemoryPlatformGateRevisedAuthority

/-!
# Institutional culture face installed on the paid platform U8 root

The existing platform-gate authority source already owns the exact
right-Payment occurrence, new-only first row, paid U8, observer-submission
face, platform-renewal face, and generated next.  This file adds one projection
coface whose low-universe payload is the canonical whole-ledger evolution and
a private family of source-generated institutional culture faces.

The component is active only at the actual revised current `0`.  The complete
old projection inventory is inherited injectively; emitter, restructuring
compiler, law surface, whole ledger, and temporal evolution are unchanged.
The high-universe full admission remains producer provenance rather than root
payload.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace Institution
namespace Installation

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open ProcessGame.Society.M14SourceGeneratedPostSettlementObserverSubmissionU8
open ProcessGame.Society.M14SourceGeneratedCycleMemoryPlatformGateU8
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Representation

noncomputable section

abbrev M14InstitutionalCultureBaseAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  platformGateAuthoritySourceAt oldVisit sourceIndex boundary

abbrev M14InstitutionalCultureBaseLedgerSourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14InstitutionalCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).restructuringSource.toLedgerSource

/-- Private Type-0 family indexed by the actual revised channels. -/
abbrev RootGeneratedM14InstitutionalCultureFamilyAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (channel : M14InstitutionalChannelOccurrenceAt boundary) →
    SourceGeneratedM14InstitutionalCultureFaceTokenAt oldVisit sourceIndex
      boundary channel

def m14InstitutionalCultureProjectionLawAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw
      (M14InstitutionalCultureBaseLedgerSourceAt oldVisit sourceIndex
        boundary) where
  Projection := PUnit
  ActiveAt := fun _ {current} _occurrence => PLift (current = (0 : Nat))
  InactiveAt := fun _ {current} _occurrence => PLift (current ≠ (0 : Nat))
  classify := by
    intro _ current _occurrence
    by_cases currentExact : current = (0 : Nat)
    · exact .inl ⟨currentExact⟩
    · exact .inr ⟨currentExact⟩
  PayloadAt := fun _ {_current} occurrence _active =>
    SourceNativeLedgerEvolutionAt
        (M14InstitutionalCultureBaseLedgerSourceAt oldVisit sourceIndex
          boundary).source occurrence ×
      RootGeneratedM14InstitutionalCultureFamilyAt oldVisit sourceIndex
        boundary
  project := fun _ {_current} occurrence _active =>
    ⟨(M14InstitutionalCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
      ).ledgerCompiler.compile occurrence,
      fun channel => generateM14InstitutionalCultureFaceTokenAt oldVisit
        sourceIndex boundary channel⟩

def m14InstitutionalCultureAuthoritySourceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (M14InstitutionalCultureBaseAuthoritySourceAt oldVisit sourceIndex boundary
    ).withProjectionCoface
      (m14InstitutionalCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14InstitutionalCultureComponentInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (m14InstitutionalCultureProjectionLawAt oldVisit sourceIndex boundary)
      (m14InstitutionalCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.componentCoface
    (M14InstitutionalCultureBaseAuthoritySourceAt oldVisit sourceIndex
      boundary)
    (m14InstitutionalCultureProjectionLawAt oldVisit sourceIndex boundary)

def m14InstitutionalCultureInheritedInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeProjectionLaw.InstallationAt
      (M14InstitutionalCultureBaseAuthoritySourceAt oldVisit sourceIndex
        boundary).projectionLaw
      (m14InstitutionalCultureAuthoritySourceAt oldVisit sourceIndex boundary
        ).projectionLaw :=
  SourceNativeProjectionLaw.InstallationAt.inheritedCoface
    (M14InstitutionalCultureBaseAuthoritySourceAt oldVisit sourceIndex
      boundary)
    (m14InstitutionalCultureProjectionLawAt oldVisit sourceIndex boundary)

/-- The existing platform renewal face remains directly installed. -/
def m14InstitutionalCulturePlatformInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (platformGateInstallationAt oldVisit sourceIndex boundary).trans
    (m14InstitutionalCultureInheritedInstallationAt oldVisit sourceIndex
      boundary)

/-- The prior observer-submission face remains directly installed. -/
def m14InstitutionalCultureObserverInstallationAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (inheritedSubmissionInstallationAt oldVisit sourceIndex boundary).trans
    (m14InstitutionalCultureInheritedInstallationAt oldVisit sourceIndex
      boundary)

def m14InstitutionalCultureAuthoritativeRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeAuthoritativeRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) where
  source :=
    m14InstitutionalCultureAuthoritySourceAt oldVisit sourceIndex boundary
  emitted :=
    (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted
  compiler_commutes :=
    (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
      ).compiler_commutes

def m14InstitutionalCultureLivingRootAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    SourceNativeLivingRootClosure
      (AugmentedNewNAt oldVisit sourceIndex boundary)
      (AugmentedNewVAt oldVisit sourceIndex boundary) :=
  (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
    ).toLivingWithoutFaithfulTerminal
      (fun _ => ⟨fun terminal => nomatch terminal⟩)

@[simp] theorem m14InstitutionalCulture_emitted_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).emitted current =
      (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).emitted current :=
  rfl

@[simp] theorem m14InstitutionalCulture_lawSurface_commutes
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14InstitutionalCultureAuthoritySourceAt oldVisit sourceIndex boundary
      ).lawSurface =
      (M14InstitutionalCultureBaseAuthoritySourceAt oldVisit sourceIndex
        boundary).lawSurface :=
  rfl

@[simp] theorem m14InstitutionalCulture_generatedLedger_commutes
    (oldVisit : OldVisit) (sourceIndex boundary current : Nat) :
    (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).generatedLedgerAt current =
      (platformGateRevisedAuthoritativeRootAt oldVisit sourceIndex boundary
        ).generatedLedgerAt current :=
  rfl

def m14InstitutionalCultureActiveAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14InstitutionalCultureProjectionLawAt oldVisit sourceIndex boundary
      ).ActiveAt PUnit.unit
      ((m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted 0) :=
  ⟨rfl⟩

def m14InstitutionalCulturePayloadAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14InstitutionalCultureProjectionLawAt oldVisit sourceIndex boundary
    ).project PUnit.unit
      ((m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).emitted 0)
      (m14InstitutionalCultureActiveAt oldVisit sourceIndex boundary)

@[simp] theorem m14InstitutionalCulturePayload_wholeLedger_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14InstitutionalCulturePayloadAt oldVisit sourceIndex boundary).1 =
      (M14InstitutionalCultureBaseLedgerSourceAt oldVisit sourceIndex boundary
        ).ledgerCompiler.compile
          ((m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex
            boundary).emitted 0) :=
  rfl

@[simp] theorem m14InstitutionalCulturePayload_face_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat)
    (channel : M14InstitutionalChannelOccurrenceAt boundary) :
    ((m14InstitutionalCulturePayloadAt oldVisit sourceIndex boundary).2
      channel).read =
      m14InstitutionalCultureFaceReadAt oldVisit sourceIndex boundary
        channel :=
  rfl

theorem m14InstitutionalCulturePayload_kernelExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelExactAt
      (m14InstitutionalCultureConsumersAt oldVisit sourceIndex boundary)
      (fun channel =>
        ((m14InstitutionalCulturePayloadAt oldVisit sourceIndex boundary).2
          channel).read) := by
  intro left right
  simpa only [m14InstitutionalCulturePayload_face_exact] using
    m14InstitutionalCultureKernelExactAt oldVisit sourceIndex boundary left
      right

theorem m14InstitutionalCultureComponentOutcome_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex boundary
      ).projectionOutcomeAt
        ((m14InstitutionalCultureComponentInstallationAt oldVisit sourceIndex
          boundary).embed PUnit.unit) 0 =
      .inl ⟨m14InstitutionalCultureActiveAt oldVisit sourceIndex boundary,
        m14InstitutionalCulturePayloadAt oldVisit sourceIndex boundary⟩ :=
  rfl

/-! ## Native temporal continuation of the widened root -/

def m14InstitutionalCultureVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Nat → RootVisit
      (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).toRoot
  | 0 =>
      (m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex
        boundary).toRoot.initialVisit
  | index + 1 =>
      (m14InstitutionalCultureVisitAt oldVisit sourceIndex boundary index
        ).next rfl

def m14InstitutionalCultureTemporalVisitAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    SourceNativeTemporalVisitAt
      (m14InstitutionalCultureLivingRootAt oldVisit sourceIndex boundary
        ).toAuthoritativeRoot.toLedgerRoot :=
  .finite
    (m14InstitutionalCultureVisitAt oldVisit sourceIndex boundary index)

theorem m14InstitutionalCultureNextEqAt
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    ((m14InstitutionalCultureLivingRootAt oldVisit sourceIndex boundary
      ).toAuthoritativeRoot.toRoot.evolutionAt
        (m14InstitutionalCultureVisitAt oldVisit sourceIndex boundary index
          ).current).nextCurrent? =
      some
        (m14InstitutionalCultureVisitAt oldVisit sourceIndex boundary
          (index + 1)).current :=
  rfl

theorem m14InstitutionalCulture_generatedNextCurrentAt_eq
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (m14InstitutionalCultureLivingRootAt oldVisit sourceIndex boundary
      ).generatedNextCurrentAt
        (m14InstitutionalCultureTemporalVisitAt oldVisit sourceIndex boundary
          index) =
      ⟨AugmentedNewVAt oldVisit sourceIndex boundary,
        m14InstitutionalCultureAuthoritativeRootAt oldVisit sourceIndex
          boundary,
        m14InstitutionalCultureTemporalVisitAt oldVisit sourceIndex boundary
          (index + 1)⟩ := by
  cases index <;> rfl

@[simp] theorem m14InstitutionalCultureVisit_current_exact
    (oldVisit : OldVisit) (sourceIndex boundary index : Nat) :
    (show Nat from
      (m14InstitutionalCultureVisitAt oldVisit sourceIndex boundary index
        ).current) = index := by
  induction index with
  | zero => rfl
  | succ index ih =>
      change
        (show Nat from
          (m14InstitutionalCultureVisitAt oldVisit sourceIndex boundary index
            ).current) + 1 = index + 1
      rw [ih]

theorem sourceInstalledM14InstitutionalCultureFace_directConsumer
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (m14InstitutionalCultureComponentOutcome_exact oldVisit
      sourceIndex boundary) ∧
      Function.Injective
        (m14InstitutionalCultureInheritedInstallationAt oldVisit sourceIndex
          boundary).embed ∧
      type_of% (m14InstitutionalCulturePayload_kernelExact oldVisit
        sourceIndex boundary) ∧
      (∀ channel,
        type_of% (m14InstitutionalCulturePayload_face_exact oldVisit
          sourceIndex boundary channel)) ∧
      type_of% (m14InstitutionalCulturePayload_wholeLedger_exact oldVisit
        sourceIndex boundary) ∧
      type_of% (platformGateInstalled_completeExistingFirstRow oldVisit
        sourceIndex boundary) ∧
      type_of% (sourceGeneratedM14InstitutionalFullAdmission_directConsumer
        oldVisit sourceIndex boundary) ∧
      type_of% (m14InstitutionalCulture_generatedNextCurrentAt_eq oldVisit
        sourceIndex boundary 0) :=
  ⟨m14InstitutionalCultureComponentOutcome_exact oldVisit sourceIndex
      boundary,
    (m14InstitutionalCultureInheritedInstallationAt oldVisit sourceIndex
      boundary).embed_injective,
    m14InstitutionalCulturePayload_kernelExact oldVisit sourceIndex boundary,
    m14InstitutionalCulturePayload_face_exact oldVisit sourceIndex boundary,
    m14InstitutionalCulturePayload_wholeLedger_exact oldVisit sourceIndex
      boundary,
    platformGateInstalled_completeExistingFirstRow oldVisit sourceIndex
      boundary,
    sourceGeneratedM14InstitutionalFullAdmission_directConsumer oldVisit
      sourceIndex boundary,
    m14InstitutionalCulture_generatedNextCurrentAt_eq oldVisit sourceIndex
      boundary 0⟩

end
end Installation
end Institution
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation.m14InstitutionalCultureComponentOutcome_exact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation.m14InstitutionalCulturePayload_kernelExact
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation.m14InstitutionalCulture_generatedNextCurrentAt_eq
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Institution.Installation.sourceInstalledM14InstitutionalCultureFace_directConsumer

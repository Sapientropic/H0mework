import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccess.ActualUpdate.Selection.Append.CrossCompiler.Readout.Recognition.Admission.Constitution.RootLaw.Completion.Bridge.Source.SourceGeneratedCanonicalSocietyExternalRootLawBridge
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Consumer.Root.Universal.Observer.ProofCarryingUniversalObserverConsumerExhaustionRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Root.Universal.Observer.Action.Consumer.ProofCarryingObserverConsumerRootLawCompletion

/-!
# Proof-carrying raw-attempt root-law exhaustion

Every source-generated submission at an installed universal-Society visit has
one four-class final disposition: presentation, typed rejection, installed
rooted action, or exact external U8.  Presentation and rejection retain the
empty same-occurrence legislation fibre; rejection exposes the exact generated
submission as residual bearer.  Consequently the local action class is empty
at this root, while rooted authority enters the existing cross-occurrence
Payment bridge, whose consumer writes the whole ledger, generates runtime next
and keeps the exact failure/self-U8 repair available.

The bridge target is source generated and its constructor is private.  This
file therefore adds neither a local legislation row nor a fifth disposition.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Observer UniversalRootGrammar
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedUniversalSocietyRootGrammar
open M14ProofCarryingUniversalObserverConsumerExhaustionRegression
open M14SourceGeneratedPostSettlementObserverSubmissionU8
open M14SourceGeneratedCanonicalSocietyExternalRootLawBridge

universe uVisible uOutput uEffect

/-- Raw presentation is lawful but cannot write a same-occurrence law row. -/
structure RawLawfulPresentationNoWriteAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    Type (max 31 (uVisible + 1) (uOutput + 1) (uEffect + 1)) where
  dispositionExact :
    (compileSourceNativeObserverConsumerSubmissionAt generated
      ).useDisposition = .presentation
  sourceRootLedgerAndNext : type_of% generated.rootLedgerAndNext_factorize
  sameOccurrenceLegislationEmpty :
    IsEmpty (SourceNativeObserverConsumerSameOccurrenceLegislationAt generated)

/-- Typed rejection keeps the rejected occurrence itself visible as residual
bearer; the bearer still factors through the root ledger and generated next. -/
structure RawTypedRejectionVisibleResidualAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    Type (max 31 (uVisible + 1) (uOutput + 1) (uEffect + 1)) where
  rejection : SourceNativeObserverConsumerRejectionAt generated
  dispositionExact :
    (compileSourceNativeObserverConsumerSubmissionAt generated
      ).useDisposition = .rejected rejection
  residualBearer : AnySourceGeneratedObserverConsumerSubmissionAt attempt
  residualBearerExact : residualBearer =
    SourceNativeObserverConsumerRejectionAt.residualBearer
      (generated := generated)
  sourceRootLedgerAndNext : type_of% generated.rootLedgerAndNext_factorize
  sameOccurrenceLegislationEmpty :
    IsEmpty (SourceNativeObserverConsumerSameOccurrenceLegislationAt generated)

/-- The third final class is an installed rooted action with its exact first
whole-ledger successor and generated next.  At the current M14 root this type
is empty because the local legislation fibre is empty; keeping the class in
the eliminator makes the final law stable under future source-installed roots
without fabricating such a program here. -/
structure RawRootedInstalledActionWholeLedgerNextAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    Type (max 31 (uVisible + 1) (uOutput + 1) (uEffect + 1)) where
  localLegislation :
    SourceNativeObserverConsumerSameOccurrenceLegislationAt generated
  action :
    Nonempty
      (RootedActionWholeLedgerNextAt
        (compileSourceNativeObserverConsumerLegislationAt
          localLegislation.2))

/-- A rooted raw submission has no local legislation row.  It enters the
source-owned external Payment occurrence, whose already installed consumer
delivers whole-ledger write-back, runtime next and exact same-occurrence U8. -/
structure RawRootedExternalWholeLedgerU8At
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    Type (max 31 (uVisible + 1) (uOutput + 1) (uEffect + 1)) where
  private mk ::
  rooted : SourceNativeObserverConsumerRootedAuthorityAt generated
  dispositionExact :
    (compileSourceNativeObserverConsumerSubmissionAt generated
      ).useDisposition = .rooted rooted
  bridge : SourceGeneratedCanonicalSocietyExternalRootLawBridgeAt
    generated rooted

/-- Direct consumer of the sole rooted/external bridge producer. -/
def rawRootedExternalWholeLedgerU8_directConsumer
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material)
    (rooted : SourceNativeObserverConsumerRootedAuthorityAt generated)
    (dispositionExact :
      (compileSourceNativeObserverConsumerSubmissionAt generated
        ).useDisposition = .rooted rooted) :
    RawRootedExternalWholeLedgerU8At generated := by
  let bridge :=
    sourceGeneratedCanonicalSocietyExternalRootLawBridge generated rooted
  exact
    { rooted := rooted
      dispositionExact := dispositionExact
      bridge := bridge }

/-- Presentation cannot simultaneously own the rooted external writing leaf. -/
theorem RawLawfulPresentationNoWriteAt.rootedExternal_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    {generated : SourceGeneratedObserverConsumerSubmissionAt program material}
    (presentation : RawLawfulPresentationNoWriteAt generated) :
    IsEmpty (RawRootedExternalWholeLedgerU8At generated) :=
  ⟨fun rooted => by
    have impossible :=
      presentation.dispositionExact.symm.trans rooted.dispositionExact
    cases impossible⟩

/-- Presentation and typed rejection are different exact compiler leaves. -/
theorem RawLawfulPresentationNoWriteAt.rejection_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    {generated : SourceGeneratedObserverConsumerSubmissionAt program material}
    (presentation : RawLawfulPresentationNoWriteAt generated) :
    IsEmpty (RawTypedRejectionVisibleResidualAt generated) :=
  ⟨fun rejected => by
    have impossible :=
      presentation.dispositionExact.symm.trans rejected.dispositionExact
    cases impossible⟩

/-- Typed rejection cannot simultaneously own the rooted external writing
leaf; its visible residual bearer therefore cannot be erased by a write. -/
theorem RawTypedRejectionVisibleResidualAt.rootedExternal_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    {generated : SourceGeneratedObserverConsumerSubmissionAt program material}
    (rejected : RawTypedRejectionVisibleResidualAt generated) :
    IsEmpty (RawRootedExternalWholeLedgerU8At generated) :=
  ⟨fun rooted => by
    have impossible :=
      rejected.dispositionExact.symm.trans rooted.dispositionExact
    cases impossible⟩

/-- Exact anti-smuggling control for the action class: this M14 source root
has no same-occurrence legislation program, hence no local installed action. -/
theorem rawRootedInstalledAction_isEmpty
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    IsEmpty (RawRootedInstalledActionWholeLedgerNextAt generated) :=
  ⟨fun action =>
    (arbitrarySourceLocalLegislation_isEmpty generated).false
      action.localLegislation⟩

/-- Unified four-class final exhaustion.  The lower compiler's rooted leaf
maps to exact external U8; the installed-action class remains explicit and is
constructively empty at this local root.  There is no fifth authority. -/
theorem rawAttempt_richExhaustive
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    Nonempty (RawLawfulPresentationNoWriteAt generated) ∨
      Nonempty (RawTypedRejectionVisibleResidualAt generated) ∨
        Nonempty (RawRootedInstalledActionWholeLedgerNextAt generated) ∨
          Nonempty (RawRootedExternalWholeLedgerU8At generated) := by
  rcases compiledSubmission_exhaustive generated with
    presentation | rooted | rejected
  · exact .inl ⟨
      { dispositionExact := presentation
        sourceRootLedgerAndNext := generated.rootLedgerAndNext_factorize
        sameOccurrenceLegislationEmpty :=
          arbitrarySourceLocalLegislation_isEmpty generated }⟩
  · rcases rooted with ⟨authority, dispositionExact⟩
    exact .inr (.inr (.inr ⟨
      rawRootedExternalWholeLedgerU8_directConsumer generated authority
        dispositionExact⟩))
  · rcases rejected with ⟨rejection, dispositionExact⟩
    exact .inr (.inl ⟨
      { rejection := rejection
        dispositionExact := dispositionExact
        residualBearer :=
          SourceNativeObserverConsumerRejectionAt.residualBearer
            (generated := generated)
        residualBearerExact := rfl
        sourceRootLedgerAndNext := generated.rootLedgerAndNext_factorize
        sameOccurrenceLegislationEmpty :=
          arbitrarySourceLocalLegislation_isEmpty generated }⟩)

/-- Per-generated-submission root-law completion at M∞. -/
structure CanonicalSocietyRawAttemptRootLawCompleteAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    Prop where
  richExhaustive :
    Nonempty (RawLawfulPresentationNoWriteAt generated) ∨
      Nonempty (RawTypedRejectionVisibleResidualAt generated) ∨
        Nonempty (RawRootedInstalledActionWholeLedgerNextAt generated) ∨
          Nonempty (RawRootedExternalWholeLedgerU8At generated)
  noSameOccurrenceLegislation :
    IsEmpty (SourceNativeObserverConsumerSameOccurrenceLegislationAt generated)
  localActionEmpty :
    IsEmpty (RawRootedInstalledActionWholeLedgerNextAt generated)
  presentationRejectionDisjoint : IsEmpty
    (RawLawfulPresentationNoWriteAt generated ×
      RawTypedRejectionVisibleResidualAt generated)
  presentationU8Disjoint : IsEmpty
    (RawLawfulPresentationNoWriteAt generated ×
      RawRootedExternalWholeLedgerU8At generated)
  rejectionU8Disjoint : IsEmpty
    (RawTypedRejectionVisibleResidualAt generated ×
      RawRootedExternalWholeLedgerU8At generated)

/-- U8 availability is exact and conditional: whenever the actual lower
compiler selected rooted authority, the source-owned external Payment bridge
delivers the installed U8 core, first write and both row-next consumers. -/
structure CanonicalSocietyRawAttemptU8AvailableAt
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    Prop where
  rootedExternal :
    ∀ (rooted : SourceNativeObserverConsumerRootedAuthorityAt generated),
      (compileSourceNativeObserverConsumerSubmissionAt generated
        ).useDisposition = .rooted rooted →
        Nonempty (RawRootedExternalWholeLedgerU8At generated)

/-- Universal raw mouth: completion and permanent conditional U8 availability
are proved together for an arbitrary generated submission. -/
theorem rawAttempt_rootLawComplete_and_u8Available
    {oldVisit : OldVisit} {sourceIndex index : Nat}
    {scenario : (universalSocietyRecognitionAt oldVisit sourceIndex
      ).law.vocabulary.Scenario}
    {Visible : Type uVisible} {Output : Type uOutput}
    {ClaimedEffect : Type uEffect}
    {attempt : SourceNativeObserverConsumerAttemptAt
      (universalSocietyRecognitionAt oldVisit sourceIndex)
      (universalSocietyVisitAt oldVisit sourceIndex index) scenario
      Visible Output ClaimedEffect}
    {program : SourceNativeObserverConsumerSubmissionProgramAt attempt}
    {material : SourceNativeObserverConsumerSubmissionMaterialAt attempt}
    (generated : SourceGeneratedObserverConsumerSubmissionAt program material) :
    CanonicalSocietyRawAttemptRootLawCompleteAt generated ∧
      CanonicalSocietyRawAttemptU8AvailableAt generated := by
  constructor
  · exact
      { richExhaustive := rawAttempt_richExhaustive generated
        noSameOccurrenceLegislation :=
          arbitrarySourceLocalLegislation_isEmpty generated
        localActionEmpty := rawRootedInstalledAction_isEmpty generated
        presentationRejectionDisjoint :=
          ⟨fun pair => pair.1.rejection_isEmpty.false pair.2⟩
        presentationU8Disjoint :=
          ⟨fun pair => pair.1.rootedExternal_isEmpty.false pair.2⟩
        rejectionU8Disjoint :=
          ⟨fun pair => pair.1.rootedExternal_isEmpty.false pair.2⟩ }
  · exact
      { rootedExternal := fun rooted dispositionExact =>
          ⟨rawRootedExternalWholeLedgerU8_directConsumer generated rooted
            dispositionExact⟩ }

/-- The positive rooted leaf is inhabited without assuming a local legislation
program.  It is the non-vacuity witness for the final universal mouth. -/
theorem canonicalActualRootedExternal_nonempty
    (oldVisit : OldVisit) (sourceIndex index : Nat) :
    Nonempty
      (RawRootedExternalWholeLedgerU8At
        (universalSocietyCertifiedRootAuthorityProgramAt oldVisit sourceIndex
          index .actual).generate) := by
  let generated :=
    (universalSocietyCertifiedRootAuthorityProgramAt oldVisit sourceIndex
      index .actual).generate
  let compiled := compileSourceNativeObserverConsumerSubmissionAt generated
  have rooted : compiled.useDisposition.IsRooted :=
    universalSocietyActualRawAttempt_isRooted oldVisit sourceIndex index
  generalize dispositionExact : compiled.useDisposition = disposition at rooted
  cases disposition with
  | presentation =>
      simp [SourceNativeObserverConsumerUseDispositionAt.IsRooted] at rooted
  | rooted authority =>
      exact ⟨rawRootedExternalWholeLedgerU8_directConsumer generated authority
        dispositionExact⟩
  | rejected rejection =>
      simp [SourceNativeObserverConsumerUseDispositionAt.IsRooted] at rooted

end
end M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.rawRootedExternalWholeLedgerU8_directConsumer
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.RawLawfulPresentationNoWriteAt.rootedExternal_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.RawLawfulPresentationNoWriteAt.rejection_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.RawTypedRejectionVisibleResidualAt.rootedExternal_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.rawRootedInstalledAction_isEmpty
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.rawAttempt_richExhaustive
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.rawAttempt_rootLawComplete_and_u8Available
#print axioms SaturationMonoid.ProcessGame.Society.M14ProofCarryingCanonicalSocietyRawAttemptRootLawExhaustion.canonicalActualRootedExternal_nonempty

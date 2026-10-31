import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Recognition.StructuralExploitationWitness
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M6.GoNaturalAuthorityReconstructionRegression
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Observer.SourceWitnessRefinement

/-!
# M14 root-independent recognition-witness publication

The fixed structural-exploitation witness is published only on the exact
left standing of the already installed M6 authority kernel.  Publication is
an indexed source object, not an observer guess: its support bit is proved
equivalent to inhabitation of the publication fibre.  The right kernel fibre
is constructively empty.

This fixture still has no final living root, ledger row, branch, repair, or
next.  It is safe to install as a pre-emitter renewal disposition without a
definition cycle.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14RecognitionWitnessPublication

noncomputable section

open Lifecycle Universal Observer
open Go Go.G1HistoryCounterexample
open Go.CrossOccurrencePathResidual
open Go.CrossOccurrenceClassicalResidual
open M6GoNaturalAuthorityReconstructionRegression
open M8RelationshipMaintenanceRenewalRegression
open M14StructuralExploitationWitness

abbrev RecognitionPath := ActualPath

/-- The pre-resignation state is read from the exact actual occurrence trace
at the common source-prefix ordinal.  The publication law receives no endpoint
equality classifier or field: the existing `ActualPath → actualOccurrence`
index selects the source occurrence, then this definition reads its trace. -/
def recognitionReplayFinal? (path : RecognitionPath) : Option (Go.Frame 2) :=
  (actualOccurrence path).trace[koMoves.length]?

@[simp] theorem recognitionReplayFinal?_ko :
    recognitionReplayFinal? koPath = some koReplay.final := by
  decide

@[simp] theorem recognitionReplayFinal?_fresh :
    recognitionReplayFinal? freshPath = some freshReplay.final := by
  decide

/-- Total replay-native recapture probe. -/
def recaptureRejectionTag (path : RecognitionPath) : Bool :=
  match recognitionReplayFinal? path with
  | none => false
  | some frame => (nativeStep? law frame (.play p00)).isNone

/-- Path-native witness condition: the exact trace-selected superko state
rejects the exact `p00` recapture. -/
def RecaptureRejectedAt (path : RecognitionPath) : Prop :=
  recaptureRejectionTag path = true

/-- An actual source witness published at one replay-native obstruction.
There is no endpoint equality field: support must come from the replay's own
recapture rejection. -/
structure SourceGeneratedRecognitionWitnessPublicationAt
    (seed : SourceSeed Lifecycle.actualEventOccurrenceOf
      Lifecycle.Universal.FixedAdapter.targetFace.Seed
      Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
      Lifecycle.actualEventGame.source)
    (path : RecognitionPath) : Type where
  private mk ::
  witness : SourceGeneratedStructuralExploitationWitnessAt seed
  recaptureRejected : RecaptureRejectedAt path

/-- Sole exact publication producer. -/
def SourceGeneratedRecognitionWitnessPublicationAt.publish
    (witness : SourceGeneratedStructuralExploitationWitnessAt
      relationshipRenewalSeed) :
  SourceGeneratedRecognitionWitnessPublicationAt
      relationshipRenewalSeed koPath where
  witness := witness
  recaptureRejected := by
    rw [RecaptureRejectedAt, recaptureRejectionTag,
      recognitionReplayFinal?_ko]
    change (nativeStep? law koReplay.final (.play p00)).isNone = true
    rw [ko_recapture_rejected]
    rfl

def sourceGeneratedRecognitionWitnessPublication :
    SourceGeneratedRecognitionWitnessPublicationAt
      relationshipRenewalSeed koPath :=
  SourceGeneratedRecognitionWitnessPublicationAt.publish
    sourceGeneratedStructuralExploitationWitness

/-- Exact source publication family over the existing two-path observer.
No registry is created: this is a dependent fibre on `ActualPath`. -/
abbrev RecognitionWitnessAt (path : RecognitionPath) :=
  SourceGeneratedRecognitionWitnessPublicationAt relationshipRenewalSeed path

theorem kernelLeft_has_sourceWitness : Nonempty (RecognitionWitnessAt koPath) :=
  ⟨sourceGeneratedRecognitionWitnessPublication⟩

theorem kernelRight_has_no_sourceWitness : IsEmpty (RecognitionWitnessAt freshPath) :=
  ⟨fun publication => by
    have rejected := publication.recaptureRejected
    rw [RecaptureRejectedAt, recaptureRejectionTag,
      recognitionReplayFinal?_fresh] at rejected
    have generated := fresh_recapture_isSome
    generalize resultEq : nativeStep? law freshReplay.final (.play p00) =
      result at generated rejected
    cases result <;> simp_all⟩

/-- Public support tag.  It is not K and contains no path payload; its
source-law meaning is certified by `witnessPublicationTag_true_iff`. -/
def witnessPublicationTag (path : RecognitionPath) : Bool :=
  recaptureRejectionTag path

@[simp] theorem witnessPublicationTag_ko :
    witnessPublicationTag koPath = true := by
  rw [witnessPublicationTag, recaptureRejectionTag,
    recognitionReplayFinal?_ko]
  change (nativeStep? law koReplay.final (.play p00)).isNone = true
  rw [ko_recapture_rejected]
  rfl

@[simp] theorem witnessPublicationTag_fresh :
    witnessPublicationTag freshPath = false := by
  have generated := fresh_recapture_isSome
  rw [witnessPublicationTag, recaptureRejectionTag,
    recognitionReplayFinal?_fresh]
  generalize resultEq : nativeStep? law freshReplay.final (.play p00) =
    result at generated ⊢
  cases result <;> simp_all

/-- The public bit is true exactly when a source-generated publication
inhabits that path fibre.  Hence refinement does not rely on an arbitrary
caller label. -/
theorem witnessPublicationTag_true_iff (path : RecognitionPath) :
    witnessPublicationTag path = true ↔ Nonempty (RecognitionWitnessAt path) := by
  constructor
  · intro published
    have rejected : RecaptureRejectedAt path := by
      exact published
    exact ⟨⟨sourceGeneratedStructuralExploitationWitness, rejected⟩⟩
  · rintro ⟨publication⟩
    exact publication.recaptureRejected

theorem witnessPublicationTag_false_iff (path : RecognitionPath) :
    witnessPublicationTag path = false ↔ IsEmpty (RecognitionWitnessAt path) := by
  constructor
  · intro notPublished
    refine ⟨fun publication => ?_⟩
    have published : witnessPublicationTag path = true :=
      (witnessPublicationTag_true_iff path).2 ⟨publication⟩
    rw [notPublished] at published
    contradiction
  · intro empty
    cases published : witnessPublicationTag path with
    | false => rfl
    | true =>
        rcases (witnessPublicationTag_true_iff path).1 published with
          ⟨publication⟩
        exact (empty.false publication).elim

/-- Honest total publication law later read from the installed disposition. -/
def recognitionWitnessPublicationLaw :
    SourceWitnessPublicationAt RecognitionWitnessAt where
  publicationTag := witnessPublicationTag
  publicationTag_eq_true_iff := witnessPublicationTag_true_iff

/-! ## Pre-emitter consumer / disposition families -/

abbrev RecognitionWitnessConsumerAt
    (seed : SourceSeed Lifecycle.actualEventOccurrenceOf
      Lifecycle.Universal.FixedAdapter.targetFace.Seed
      Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
      Lifecycle.actualEventGame.source) :=
  SourceGeneratedStructuralExploitationWitnessAt seed

structure RecognitionWitnessDispositionAt
    (seed : SourceSeed Lifecycle.actualEventOccurrenceOf
      Lifecycle.Universal.FixedAdapter.targetFace.Seed
      Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
      Lifecycle.actualEventGame.source) : Type where
  private mk ::
  exactPublication :
    SourceGeneratedRecognitionWitnessPublicationAt seed koPath
  publicationLaw : SourceWitnessPublicationAt RecognitionWitnessAt

/-- Sole pre-emitter disposition producer.  It accepts the exact source
witness, not a publication bit or observer decoder. -/
def RecognitionWitnessDispositionAt.publish
    (witness : SourceGeneratedStructuralExploitationWitnessAt
      relationshipRenewalSeed) :
    RecognitionWitnessDispositionAt relationshipRenewalSeed where
  exactPublication :=
    SourceGeneratedRecognitionWitnessPublicationAt.publish witness
  publicationLaw := recognitionWitnessPublicationLaw

def recognitionWitnessConsumer :
    RecognitionWitnessConsumerAt relationshipRenewalSeed :=
  sourceGeneratedStructuralExploitationWitness

def recognitionWitnessDisposition :
    RecognitionWitnessDispositionAt relationshipRenewalSeed :=
  RecognitionWitnessDispositionAt.publish recognitionWitnessConsumer

/-- Without the exact structural witness no publication can be installed. -/
theorem noStructuralWitness_noPublication
    {seed : SourceSeed Lifecycle.actualEventOccurrenceOf
      Lifecycle.Universal.FixedAdapter.targetFace.Seed
      Lifecycle.Universal.FixedAdapter.targetFace.SeedAt
      Lifecycle.actualEventGame.source}
    (noWitness : IsEmpty
      (SourceGeneratedStructuralExploitationWitnessAt seed)) :
    IsEmpty (RecognitionWitnessDispositionAt seed) :=
  ⟨fun disposition => noWitness.false
    disposition.exactPublication.witness⟩

end
end M14RecognitionWitnessPublication
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14RecognitionWitnessPublication.SourceGeneratedRecognitionWitnessPublicationAt.publish
#print axioms SaturationMonoid.ProcessGame.Society.M14RecognitionWitnessPublication.witnessPublicationTag_true_iff

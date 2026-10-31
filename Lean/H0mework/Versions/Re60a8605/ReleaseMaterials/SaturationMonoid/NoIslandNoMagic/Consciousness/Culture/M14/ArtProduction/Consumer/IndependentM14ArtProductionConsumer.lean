import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source.SourceGeneratedM14ActualArtProduction
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation.SourceGeneratedM14TeachingCultureRepresentation

/-!
# Independent M14 art-production consumers

The two occurrences are the exact raw and produced work contexts carried by
one source-generated progress receipt.  Both are restricted to the same
complete teaching culture face.  Work-form and lifecycle/write-back consumers
are declared before any art-production carrier or quotient.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NoIslandNoMagic
namespace Consciousness
namespace Culture
namespace M14
namespace ArtProduction
namespace Consumer

open ProcessGame Society
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProcessGame.Society.M14SourceGeneratedContributionMergeActionSource
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Beauty.M12
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Consumer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.Teaching.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Source

noncomputable section

abbrev M14ArtProductionRawFaceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence : SourceGeneratedM12AestheticContextOccurrence //
    occurrence = m14ArtProductionRawOccurrence ∧
      Nonempty (M14ArtProductionProgressReceiptAt oldVisit sourceIndex
        boundary) }

abbrev M14ArtProductionWorkFaceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  { occurrence : SourceGeneratedM12AestheticContextOccurrence //
    occurrence = m14ArtProductionWorkOccurrence ∧
      Nonempty (M14ArtProductionProgressReceiptAt oldVisit sourceIndex
        boundary) }

abbrev M14ArtProductionOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  M14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary ⊕
    M14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary

def m14ArtProductionRawFaceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary :=
  .inl ⟨m14ArtProductionRawOccurrence, rfl,
    ⟨m14ArtProductionProgress
      (m14ArtProductionSourceAt oldVisit sourceIndex boundary)⟩⟩

def m14ArtProductionWorkFaceOccurrenceAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary :=
  .inr ⟨m14ArtProductionWorkOccurrence, rfl,
    ⟨m14ArtProductionProgress
      (m14ArtProductionSourceAt oldVisit sourceIndex boundary)⟩⟩

def m14ArtProductionContextReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary →
      SourceGeneratedM12AestheticContextOccurrence
  | .inl occurrence => occurrence.1
  | .inr occurrence => occurrence.1

def m14ArtProductionWorkReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary →
      M14ArtWorkReadout
  | .inl occurrence => m14ArtWorkReadAt occurrence.1
  | .inr occurrence => m14ArtWorkReadAt occurrence.1

structure M14ArtProductionLifecycleReadout : Type where
  residual : SourceGeneratedM12AestheticContextOccurrence
  progressEventCount : Nat
  sourceOwned : Bool
  writtenBack : Bool

def m14ArtProductionLifecycleReadAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat} :
    M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary →
      M14ArtProductionLifecycleReadout
  | .inl occurrence =>
      { residual := occurrence.1
        progressEventCount := 0
        sourceOwned := true
        writtenBack := false }
  | .inr occurrence =>
      { residual := occurrence.1
        progressEventCount :=
          (m14ArtProductionRunAt oldVisit sourceIndex boundary).events.length
        sourceOwned := true
        writtenBack := true }

def m14ArtProductionOldTeachingViewAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary →
      M14TeachingOccurrenceAt oldVisit sourceIndex boundary :=
  fun _occurrence =>
    m14TeachingTargetOccurrenceAt oldVisit sourceIndex boundary

def m14ArtProductionWorkIndependentReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14ArtWorkReadout
  read := m14ArtProductionWorkReadAt

def m14ArtProductionLifecycleIndependentReadoutAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    IndependentReadout
      (M14ArtProductionOccurrenceAt oldVisit sourceIndex boundary) where
  Output := M14ArtProductionLifecycleReadout
  read := m14ArtProductionLifecycleReadAt

def m14ArtProductionReindexedTeachingConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14TeachingConsumersAt oldVisit sourceIndex boundary).reindex
    (m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary)

def m14ArtProductionWorkConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionReindexedTeachingConsumersAt oldVisit sourceIndex boundary
    ).adjoin
      (m14ArtProductionWorkIndependentReadoutAt oldVisit sourceIndex boundary)

def m14ArtProductionConsumersAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :=
  (m14ArtProductionWorkConsumersAt oldVisit sourceIndex boundary).adjoin
    (m14ArtProductionLifecycleIndependentReadoutAt oldVisit sourceIndex
      boundary)

@[simp] theorem m14ArtProductionOldTeachingView_raw_eq_work
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary
        (m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary) =
      m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary
        (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary) :=
  rfl

@[simp] theorem m14ArtProductionContextRead_raw_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14ArtProductionContextReadAt
        (m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary) =
      m14ArtProductionRawOccurrence :=
  rfl

@[simp] theorem m14ArtProductionContextRead_work_exact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14ArtProductionContextReadAt
        (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary) =
      m14ArtProductionWorkOccurrence :=
  rfl

theorem m14ArtProductionWorkRead_raw_ne_work
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14ArtProductionWorkReadAt
        (m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary) ≠
      m14ArtProductionWorkReadAt
        (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary) :=
  m14ArtWork_transformation_nontrivial

theorem m14ArtProductionWorkRead_injective
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    Function.Injective
      (m14ArtProductionWorkReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary)) := by
  intro left right sameRead
  cases left with
  | inl leftRaw =>
      cases right with
      | inl rightRaw =>
          exact congrArg Sum.inl (Subtype.ext
            (leftRaw.property.1.trans rightRaw.property.1.symm))
      | inr rightWork =>
          have sameAlignment := congrArg M14ArtWorkReadout.alignment sameRead
          have leftExact := leftRaw.property.1
          have rightExact := rightWork.property.1
          change (m14ArtWorkReadAt leftRaw.1).alignment =
            (m14ArtWorkReadAt rightWork.1).alignment at sameAlignment
          rw [leftExact, rightExact] at sameAlignment
          exact (m14ArtWork_alignment_changes sameAlignment).elim
  | inr leftWork =>
      cases right with
      | inl rightRaw =>
          have sameAlignment := congrArg M14ArtWorkReadout.alignment sameRead
          have leftExact := leftWork.property.1
          have rightExact := rightRaw.property.1
          change (m14ArtWorkReadAt leftWork.1).alignment =
            (m14ArtWorkReadAt rightRaw.1).alignment at sameAlignment
          rw [leftExact, rightExact] at sameAlignment
          exact (m14ArtWork_alignment_changes sameAlignment.symm).elim
      | inr rightWork =>
          exact congrArg Sum.inr (Subtype.ext
            (leftWork.property.1.trans rightWork.property.1.symm))

theorem m14ArtProductionLifecycleRead_sourceExact
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    let raw := m14ArtProductionLifecycleReadAt
      (m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary)
    let work := m14ArtProductionLifecycleReadAt
      (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary)
    raw.residual = m14ArtProductionRawOccurrence ∧
      work.residual = m14ArtProductionWorkOccurrence ∧
      raw.progressEventCount = 0 ∧
      work.progressEventCount = 1 ∧
      raw.sourceOwned = true ∧
      work.sourceOwned = true ∧
      raw.writtenBack = false ∧
      work.writtenBack = true ∧
      Nonempty (SourceOwnsResponsibilityIncidence
        (M14ArtProductionVocabularyAt oldVisit sourceIndex boundary)
        (m14ArtProductionSourceAt oldVisit sourceIndex boundary)
        (m14ArtProductionRawObligationAt oldVisit sourceIndex boundary)) ∧
      type_of% (m14ArtProductionTarget_writeBack_exact oldVisit sourceIndex
        boundary) :=
  ⟨rfl, rfl, rfl,
    m14ArtProductionRun_events_length oldVisit sourceIndex boundary,
    rfl, rfl, rfl, rfl,
    ⟨m14ArtProductionSourceOwnershipAt oldVisit sourceIndex boundary⟩,
    m14ArtProductionTarget_writeBack_exact oldVisit sourceIndex boundary⟩

theorem m14ArtProductionLifecycleRead_raw_ne_work
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    m14ArtProductionLifecycleReadAt
        (m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary) ≠
      m14ArtProductionLifecycleReadAt
        (m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary) := by
  intro sameRead
  have sameResidual := congrArg M14ArtProductionLifecycleReadout.residual
    sameRead
  change m14ArtProductionRawOccurrence =
    m14ArtProductionWorkOccurrence at sameResidual
  exact m14ArtWork_alignment_changes
    (congrArg (fun occurrence => (m14ArtWorkReadAt occurrence).alignment)
      sameResidual)

theorem m14ArtProductionWorkKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary)
      (m14ArtProductionWorkIndependentReadoutAt oldVisit sourceIndex
        boundary) :=
  ⟨m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary,
    m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary,
    m14ArtProductionOldTeachingView_raw_eq_work oldVisit sourceIndex boundary,
    m14ArtProductionWorkRead_raw_ne_work oldVisit sourceIndex boundary⟩

theorem m14ArtProductionLifecycleKernelEscapeAt
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    FaceKernelEscapeAt
      (m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary)
      (m14ArtProductionLifecycleIndependentReadoutAt oldVisit sourceIndex
        boundary) :=
  ⟨m14ArtProductionRawFaceOccurrenceAt oldVisit sourceIndex boundary,
    m14ArtProductionWorkFaceOccurrenceAt oldVisit sourceIndex boundary,
    m14ArtProductionOldTeachingView_raw_eq_work oldVisit sourceIndex boundary,
    m14ArtProductionLifecycleRead_raw_ne_work oldVisit sourceIndex boundary⟩

theorem m14ArtProductionWork_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14ArtProductionWorkReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary) :=
  (m14ArtProductionWorkKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14ArtProductionLifecycle_oldFactorization_isEmpty
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    ¬ Function.FactorsThrough
      (m14ArtProductionLifecycleReadAt (oldVisit := oldVisit)
        (sourceIndex := sourceIndex) (boundary := boundary))
      (m14ArtProductionOldTeachingViewAt oldVisit sourceIndex boundary) :=
  (m14ArtProductionLifecycleKernelEscapeAt oldVisit sourceIndex boundary
    ).not_factorsThrough

theorem m14ArtProductionConsumer_grounded
    (oldVisit : OldVisit) (sourceIndex boundary : Nat) :
    type_of% (sourceGeneratedM14ActualArtProduction_directConsumer oldVisit
      sourceIndex boundary) ∧
      Function.Injective
        (m14ArtProductionWorkReadAt (oldVisit := oldVisit)
          (sourceIndex := sourceIndex) (boundary := boundary)) ∧
      type_of% (m14ArtProductionLifecycleRead_sourceExact oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProductionWorkKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProductionLifecycleKernelEscapeAt oldVisit sourceIndex
        boundary) ∧
      type_of% (m14ArtProductionWork_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      type_of% (m14ArtProductionLifecycle_oldFactorization_isEmpty oldVisit
        sourceIndex boundary) ∧
      IsEmpty (M14ArtProductionWithoutMaterialAt oldVisit sourceIndex
        boundary) ∧
      IsEmpty (M14ArtProductionWithoutTraceAt oldVisit sourceIndex boundary) ∧
      IsEmpty (M14ArtProductionWithoutWriteBackAt oldVisit sourceIndex
        boundary) :=
  ⟨sourceGeneratedM14ActualArtProduction_directConsumer oldVisit sourceIndex
      boundary,
    m14ArtProductionWorkRead_injective oldVisit sourceIndex boundary,
    m14ArtProductionLifecycleRead_sourceExact oldVisit sourceIndex boundary,
    m14ArtProductionWorkKernelEscapeAt oldVisit sourceIndex boundary,
    m14ArtProductionLifecycleKernelEscapeAt oldVisit sourceIndex boundary,
    m14ArtProductionWork_oldFactorization_isEmpty oldVisit sourceIndex
      boundary,
    m14ArtProductionLifecycle_oldFactorization_isEmpty oldVisit sourceIndex
      boundary,
    m14ArtProduction_noMaterial_claim_isEmpty oldVisit sourceIndex boundary,
    m14ArtProduction_noTrace_claim_isEmpty oldVisit sourceIndex boundary,
    m14ArtProduction_noWriteBack_claim_isEmpty oldVisit sourceIndex boundary⟩

end
end Consumer
end ArtProduction
end M14
end Culture
end Consciousness
end NoIslandNoMagic
end SaturationMonoid

#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer.m14ArtProductionWorkRead_injective
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer.m14ArtProductionWorkKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer.m14ArtProductionLifecycleKernelEscapeAt
#print axioms SaturationMonoid.NoIslandNoMagic.Consciousness.Culture.M14.ArtProduction.Consumer.m14ArtProductionConsumer_grounded

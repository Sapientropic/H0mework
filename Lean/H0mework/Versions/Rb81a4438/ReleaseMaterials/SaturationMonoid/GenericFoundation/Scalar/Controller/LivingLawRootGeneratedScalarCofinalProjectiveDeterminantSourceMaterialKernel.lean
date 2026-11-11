import H0mework.Versions.Rb81a4438.Realization.Faces.DualityTransport
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Cofinal.LivingLawRootGeneratedScalarCofinalProjectiveDeterminantDispositionKernel

/-!
# Source-installed scalar cofinal determinant material

This file defines the source-facing material law required before a scalar
cofinal determinant disposition can enter a living-root controller.  The law
extends an already source-owned cofinal-history/cochain/duality law with an
occurrence-indexed scalar history, compatibility proof, dual evaluation, and
observation language.  It contains no disposition branch, determinant,
Picard value, ledger row, or next current.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ScalarCofinalProjectiveDeterminantController

open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainDuality
open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open SourceGeneratedScalarCofinalExactEnvelope

noncomputable section

universe w

variable {N : WorldRelationNetwork.{w}} {V : Vocabulary.{w}}
variable {source : SourceNativeLedgerSource N V}
variable {R : Type w} [CommRing R]
variable {Generator : Type w} [AddCommGroup Generator] [Module R Generator]
variable {StageCarrier : ℕ → Type w}
variable [∀ stage, AddCommGroup (StageCarrier stage)]
variable [∀ stage, Module R (StageCarrier stage)]
variable {DualTarget : Type w}
variable [AddCommGroup DualTarget] [Module R DualTarget]
variable {Observation : Type w}
variable [AddCommGroup Observation] [Module R Observation]

abbrev SourceOccurrenceAt (current : V.Current) :=
  source.source.toRootSource.actual.OccurrenceAt current

/-- Branch-preserving scalar exposure over the parent law's complete history
tree at one exact source occurrence. -/
def scalarOccurrenceAt
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (data : Data (R := R) (Generator := Generator)
      (Carrier := StageCarrier)) :
    RootedAccountedUnfolding
      (SourceOccurrenceAt (source := source) current ×
        Data (R := R) (Generator := Generator)
          (Carrier := StageCarrier)) :=
  (parent.commonLaw.historyAt occurrence).root.map
    (fun actual => (actual, data))

def scalarFaceAt
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (data : Data (R := R) (Generator := Generator)
      (Carrier := StageCarrier)) :
    Face (scalarOccurrenceAt parent occurrence data) :=
  Face.generate

theorem scalarCalculationAt
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (data : Data (R := R) (Generator := Generator)
      (Carrier := StageCarrier)) (laws : data.Compatible) :
    Face.GeneratedCompatibilityCalculationAt
      (scalarFaceAt parent occurrence data) :=
  Face.generateCompatibility (scalarFaceAt parent occurrence data) (by
    simpa [Face.CompatibilityLaws, Face.data, Face.dataOccurrence,
      scalarFaceAt, scalarOccurrenceAt] using laws)

/-- Projecting the scalar exposure recovers the complete parent history tree. -/
theorem scalarFaceAt_root_eq_parent
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (data : Data (R := R) (Generator := Generator)
      (Carrier := StageCarrier)) :
    (scalarFaceAt parent occurrence data).root =
      (parent.commonLaw.historyAt occurrence).root := by
  change
    ((parent.commonLaw.historyAt occurrence).root.map
      (fun actual => (actual, data))).map Prod.fst =
        (parent.commonLaw.historyAt occurrence).root
  rw [RootedAccountedUnfolding.map_map]
  change (parent.commonLaw.historyAt occurrence).root.map id =
    (parent.commonLaw.historyAt occurrence).root
  exact RootedAccountedUnfolding.map_id
    (parent.commonLaw.historyAt occurrence).root

/-- Source-native scalar material.  Every mathematical input is indexed by
the exact source occurrence; no output branch can be submitted. -/
structure SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
    (source : SourceNativeLedgerSource N V) : Type (w + 1) where
  private mk ::
  parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source
  dataAt : {current : V.Current} →
    SourceOccurrenceAt (source := source) current →
    Data (R := R) (Generator := Generator) (Carrier := StageCarrier)
  compatibleAt : {current : V.Current} →
    (occurrence : SourceOccurrenceAt (source := source) current) →
      (dataAt occurrence).Compatible
  evaluationAt : {current : V.Current} →
    (occurrence : SourceOccurrenceAt (source := source) current) →
      (scalarFaceAt parent occurrence (dataAt occurrence)).completion
          (scalarCalculationAt parent occurrence (dataAt occurrence)
            (compatibleAt occurrence)) →ₗ[R]
        Module.Dual R DualTarget
  observationAt : {current : V.Current} →
    (occurrence : SourceOccurrenceAt (source := source) current) →
      SourceGeneratedScalarCofinalExactEnvelope.Carrier
          (scalarFaceAt parent occurrence (dataAt occurrence))
          (scalarCalculationAt parent occurrence (dataAt occurrence)
            (compatibleAt occurrence))
          (evaluationAt occurrence) →ₗ[R] Observation

namespace SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw

/-- Raw scalar coordinates carried by the fixed source projection, before
any determinant disposition or temporal step is generated. -/
structure RawAt
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current) : Type w where
  data : Data (R := R) (Generator := Generator) (Carrier := StageCarrier)
  compatible : data.Compatible
  evaluation :
    (scalarFaceAt parent occurrence data).completion
        (scalarCalculationAt parent occurrence data compatible) →ₗ[R]
      Module.Dual R DualTarget
  observation :
    SourceGeneratedScalarCofinalExactEnvelope.Carrier
        (scalarFaceAt parent occurrence data)
        (scalarCalculationAt parent occurrence data compatible)
        evaluation →ₗ[R] Observation

def create
    (parent : SourceNativeCofinalHistoryCochainDualityMaterialLaw source)
    (dataAt : {current : V.Current} →
      SourceOccurrenceAt (source := source) current →
      Data (R := R) (Generator := Generator) (Carrier := StageCarrier))
    (compatibleAt : {current : V.Current} →
      (occurrence : SourceOccurrenceAt (source := source) current) →
        (dataAt occurrence).Compatible)
    (evaluationAt : {current : V.Current} →
      (occurrence : SourceOccurrenceAt (source := source) current) →
        (scalarFaceAt parent occurrence (dataAt occurrence)).completion
            (scalarCalculationAt parent occurrence (dataAt occurrence)
              (compatibleAt occurrence)) →ₗ[R]
          Module.Dual R DualTarget)
    (observationAt : {current : V.Current} →
      (occurrence : SourceOccurrenceAt (source := source) current) →
        SourceGeneratedScalarCofinalExactEnvelope.Carrier
            (scalarFaceAt parent occurrence (dataAt occurrence))
            (scalarCalculationAt parent occurrence (dataAt occurrence)
              (compatibleAt occurrence))
            (evaluationAt occurrence) →ₗ[R] Observation) :
    SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) source :=
  ⟨parent, dataAt, compatibleAt, evaluationAt, observationAt⟩

/-- The complete raw scalar family is fixed in the source projection before
the root emitter. The parent coordinate remains an installed restriction. -/
def toProjectionLaw
    (law : SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) source) :
    SourceNativeProjectionLaw source :=
  {
    Projection := law.parent.toProjectionLaw.Projection ⊕ PUnit
    ActiveAt := fun projection {_current} occurrence =>
      match projection with
      | .inl parentProjection =>
          law.parent.toProjectionLaw.ActiveAt parentProjection occurrence
      | .inr _ => PUnit
    InactiveAt := fun projection {_current} occurrence =>
      match projection with
      | .inl parentProjection =>
          law.parent.toProjectionLaw.InactiveAt parentProjection occurrence
      | .inr _ => PEmpty
    classify := fun projection {_current} occurrence =>
      match projection with
      | .inl parentProjection =>
          law.parent.toProjectionLaw.classify parentProjection occurrence
      | .inr _ => .inl PUnit.unit
    PayloadAt := fun projection {_current} occurrence active =>
      match projection with
      | .inl parentProjection =>
          law.parent.toProjectionLaw.PayloadAt parentProjection occurrence active
      | .inr _ => RawAt law.parent occurrence
    project := fun projection {_current} occurrence active =>
      match projection with
      | .inl parentProjection =>
          law.parent.toProjectionLaw.project parentProjection occurrence active
      | .inr _ =>
          ⟨law.dataAt occurrence, law.compatibleAt occurrence,
            law.evaluationAt occurrence, law.observationAt occurrence⟩
  }

/-- The previously installed parent projection survives the scalar source
extension as the left coordinate of the same fixed inventory. -/
def parentComponentInstallation
    (law : SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) source) :
    SourceNativeProjectionLaw.InstallationAt
      law.parent.toProjectionLaw law.toProjectionLaw where
  embed := Sum.inl
  embed_injective := Sum.inl_injective
  outcome_heq := by
    intro current occurrence projection
    cases projection with
    | inl parentProjection => cases parentProjection; rfl
    | inr scalarProjection => cases scalarProjection; rfl

/-- Reading the fixed scalar projection recovers the original evaluator
history, not a caller-supplied post-root replacement. -/
@[simp] theorem scalarProject_data
    (law : SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) source)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current) :
    (law.toProjectionLaw.project (.inr PUnit.unit) occurrence PUnit.unit).data =
      law.dataAt occurrence :=
  rfl

/-- The complete scalar outcome of a fixed parent law determines its raw
evaluator history. A replacement cannot reuse the same source coordinate. -/
theorem dataAt_eq_of_scalar_outcome_heq
    (left right : SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) source)
    (parent_eq : left.parent = right.parent)
    {current : V.Current}
    (occurrence : SourceOccurrenceAt (source := source) current)
    (same : HEq
      (left.toProjectionLaw.outcomeAt (.inr PUnit.unit) occurrence)
      (right.toProjectionLaw.outcomeAt (.inr PUnit.unit) occurrence)) :
    left.dataAt occurrence = right.dataAt occurrence := by
  obtain ⟨leftParent, leftData, leftCompatible, leftEvaluation, leftObservation⟩ := left
  obtain ⟨rightParent, rightData, rightCompatible, rightEvaluation, rightObservation⟩ := right
  cases parent_eq
  have outcomeEq := eq_of_heq same
  have rawEq := (Sigma.mk.inj (Sum.inl.inj outcomeEq)).2
  have dataEq := congrArg RawAt.data (eq_of_heq rawEq)
  change leftData occurrence = rightData occurrence at dataEq
  exact dataEq

end SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw

end

end ScalarCofinalProjectiveDeterminantController
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

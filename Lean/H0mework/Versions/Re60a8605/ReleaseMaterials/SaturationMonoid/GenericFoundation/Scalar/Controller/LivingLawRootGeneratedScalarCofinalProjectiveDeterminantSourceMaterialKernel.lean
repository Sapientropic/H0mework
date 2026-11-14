import H0mework.Realization.Faces.DualityTransport
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

universe w r u d o

variable {N : WorldRelationNetwork.{w}} {V : Vocabulary.{w}}
variable {source : SourceNativeLedgerSource N V}
variable {R : Type r} [CommRing R]
variable {Generator : Type u} [AddCommGroup Generator] [Module R Generator]
variable {StageCarrier : ℕ → Type u}
variable [∀ stage, AddCommGroup (StageCarrier stage)]
variable [∀ stage, Module R (StageCarrier stage)]
variable {DualTarget : Type d}
variable [AddCommGroup DualTarget] [Module R DualTarget]
variable {Observation : Type o}
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
    (source : SourceNativeLedgerSource N V) : Type (max w r u d o + 1) where
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

/-- The scalar extension uses the already installed parent projection law.
Its extra fields are source material behind that occurrence seal, just as the
parent pairing is; they do not create a second projection inventory. -/
def toProjectionLaw
    (law : SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw
      (R := R) (Generator := Generator) (StageCarrier := StageCarrier)
      (DualTarget := DualTarget) (Observation := Observation) source) :
    SourceNativeProjectionLaw source :=
  law.parent.toProjectionLaw

end SourceNativeScalarCofinalProjectiveDeterminantMaterialLaw

end

end ScalarCofinalProjectiveDeterminantController
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

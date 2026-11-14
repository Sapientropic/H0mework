import Mathlib.Analysis.Complex.Basic
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Cofinal.LivingLawRootGeneratedScalarCofinalFiniteFreeDeterminantDispositionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Cofinal.LivingLawRootGeneratedScalarCofinalProjectiveDeterminantDispositionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Cofinal.LivingLawRootGeneratedScalarCofinalBoundedDispositionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Cofinal.LivingLawRootGeneratedScalarCofinalExactEnvelopeNaturalityKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Cofinal.LivingLawRootGeneratedScalarCofinalFunctorialityKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Cofinal.LivingLawRootGeneratedScalarCofinalObservationDispositionKernel

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarCofinalExactEnvelopeRegression

open CategoryTheory
open SourceGeneratedScalarCofinalKernelCompletion
open SourceGeneratedScalarCofinalRootOccurrence
open SourceGeneratedScalarCofinalExactEnvelope
open SourceGeneratedScalarCofinalObservationDisposition
open SourceGeneratedScalarCofinalBoundedDisposition
open SourceGeneratedScalarCofinalFiniteFreeDeterminantDisposition
open SourceGeneratedScalarCofinalProjectiveDeterminantDisposition
open SourceGeneratedScalarCofinalExactEnvelopeNaturality
open SourceGeneratedScalarCofinalNaturality
open SourceGeneratedScalarPerfectification
open SourceGeneratedScalarExactEnvelope

noncomputable section

abbrev ComplexStageCarrier : Nat → Type := fun _ ↦ ℂ

def complexData : Data (R := ℂ) (Generator := ℂ)
    (Carrier := ComplexStageCarrier) where
  evaluator := fun _ ↦ LinearMap.mulLeft ℂ Complex.I
  transition := fun _ ↦ LinearMap.id

theorem complexData_compatible : complexData.Compatible := by
  intro stage
  rfl

def complexOccurrence : RootedAccountedUnfolding (Bool ×
    Data (R := ℂ) (Generator := ℂ) (Carrier := ComplexStageCarrier)) :=
  RootedAccountedUnfolding.zero (true, complexData)

def complexFace : Face complexOccurrence := Face.generate

theorem complexCalculation :
    Face.GeneratedCompatibilityCalculationAt complexFace :=
  Face.generateCompatibility complexFace (by
    change complexData.Compatible
    exact complexData_compatible)

/-- The stage-zero realized restriction is an actual linear read of the
generated cofinal completion. -/
def completionRead : complexFace.completion complexCalculation →ₗ[ℂ] ℂ :=
  (complexFace.data.stageRealization 0).comp
    (complexFace.restriction complexCalculation 0).hom

/-- Multiplication curries the completion read into a source dual
evaluation, so no scalar-forgetting adapter occurs. -/
def completionEvaluation :
    complexFace.completion complexCalculation →ₗ[ℂ] Module.Dual ℂ ℂ :=
  (LinearMap.mul ℂ ℂ).comp completionRead

theorem completionRead_source (value : ℂ) :
    completionRead (complexFace.completionMap complexCalculation value) =
      Complex.I * value := by
  have readback := ConcreteCategory.congr_hom
    (complexFace.source_to_evaluator complexCalculation 0) value
  exact readback

theorem completionEvaluation_source_one (value : ℂ) :
    completionEvaluation (complexFace.completionMap complexCalculation value) 1 =
      Complex.I * value := by
  change completionRead
      (complexFace.completionMap complexCalculation value) * 1 = _
  rw [completionRead_source]
  simp

def sourceEnvelopeMap : ℂ →ₗ[ℂ]
    SourceGeneratedScalarCofinalExactEnvelope.Carrier
      complexFace complexCalculation completionEvaluation :=
  SourceGeneratedScalarCofinalExactEnvelope.sourceMap
    complexFace complexCalculation completionEvaluation

example : complexFace.root = complexOccurrence.map Prod.fst :=
  SourceGeneratedScalarCofinalExactEnvelope.preserves_root
    complexFace

theorem sourceEvaluation_readback :
    ((dualInclusion completionEvaluation).comp
        (generatedDualMap completionEvaluation)).comp sourceEnvelopeMap =
      completionEvaluation.comp (complexFace.completionMap complexCalculation).hom :=
  SourceGeneratedScalarCofinalExactEnvelope.source_evaluation_readback
    complexFace complexCalculation completionEvaluation

def generatedDualObservation :
    SourceGeneratedScalarCofinalExactEnvelope.Carrier
        complexFace complexCalculation completionEvaluation →ₗ[ℂ]
      SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        complexFace complexCalculation completionEvaluation :=
  generatedDualMap completionEvaluation

theorem generatedDualObservation_exact :
    ∃ equivalence,
      SourceGeneratedScalarCofinalObservationDisposition.settle
          complexFace complexCalculation completionEvaluation
          generatedDualObservation = .exact equivalence := by
  rw [SourceGeneratedScalarCofinalObservationDisposition.exact_iff_bijective]
  exact generatedDualMap_bijective completionEvaluation

theorem cofinalBounded_positive :
    ∃ (equivalence :
        SourceGeneratedScalarCofinalExactEnvelope.Carrier
            complexFace complexCalculation completionEvaluation ≃ₗ[ℂ]
          SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
            complexFace complexCalculation completionEvaluation)
      (finite : Module.Finite ℂ
        (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
          complexFace complexCalculation completionEvaluation))
      (projective : Module.Projective ℂ
        (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
          complexFace complexCalculation completionEvaluation))
      (duality : SourceGeneratedScalarFiniteProjectiveDuality.TensorDuality
        (R := ℂ)
        (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
          complexFace complexCalculation completionEvaluation)),
      SourceGeneratedScalarCofinalBoundedDisposition.settle
          complexFace complexCalculation completionEvaluation
          generatedDualObservation =
        .boundedDualizable equivalence finite projective duality := by
  let equivalence := perfectEquiv completionEvaluation
  let finite : Module.Finite ℂ
      (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        complexFace complexCalculation completionEvaluation) := inferInstance
  let projective : Module.Projective ℂ
      (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        complexFace complexCalculation completionEvaluation) := inferInstance
  let duality := SourceGeneratedScalarFiniteProjectiveDuality.generate
    finite projective
  exact ⟨equivalence, finite, projective, duality,
    SourceGeneratedScalarBoundedObservationDisposition.settle_eq_boundedDualizable
      completionEvaluation generatedDualObservation equivalence
      (SourceGeneratedScalarObservationDisposition.settle_eq_exact_of_bijective
        generatedDualObservation (generatedDualMap_bijective completionEvaluation))
      finite projective⟩

theorem cofinalFreeDeterminant_positive :
    ∃ (equivalence :
        SourceGeneratedScalarCofinalExactEnvelope.Carrier
            complexFace complexCalculation completionEvaluation ≃ₗ[ℂ]
          SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
            complexFace complexCalculation completionEvaluation)
      (readout : SourceGeneratedScalarFiniteFreeTopExterior.Readout
        (R := ℂ)
        (O := SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
          complexFace complexCalculation completionEvaluation)),
      SourceGeneratedScalarCofinalFiniteFreeDeterminantDisposition.bounded
          complexFace complexCalculation completionEvaluation
          generatedDualObservation =
        .boundedDualizable equivalence readout.finite readout.projective
          readout.duality ∧
      SourceGeneratedScalarFiniteFreeDeterminantDisposition.settle
          (observation := generatedDualObservation)
          (.boundedDualizable (observation := generatedDualObservation)
            equivalence readout.finite readout.projective readout.duality) =
        .freeDeterminant (observation := generatedDualObservation)
          equivalence readout := by
  obtain ⟨equivalence, finite, projective, duality, boundedEquality⟩ :=
    cofinalBounded_positive
  let free : Module.Free ℂ
      (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        complexFace complexCalculation completionEvaluation) := inferInstance
  let readout : SourceGeneratedScalarFiniteFreeTopExterior.Readout
      (R := ℂ)
      (O := SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        complexFace complexCalculation completionEvaluation) :=
    ⟨finite, projective, duality, free⟩
  exact ⟨equivalence, readout, boundedEquality,
    SourceGeneratedScalarFiniteFreeDeterminantDisposition.settle_bounded_free
      equivalence finite projective duality free⟩

theorem cofinalProjectiveDeterminant_positive :
    ∃ (equivalence :
        SourceGeneratedScalarCofinalExactEnvelope.Carrier
            complexFace complexCalculation completionEvaluation ≃ₗ[ℂ]
          SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
            complexFace complexCalculation completionEvaluation)
      (finite : Module.Finite ℂ
        (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
          complexFace complexCalculation completionEvaluation))
      (projective : Module.Projective ℂ
        (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
          complexFace complexCalculation completionEvaluation))
      (duality : SourceGeneratedScalarFiniteProjectiveDuality.TensorDuality
        (R := ℂ)
        (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
          complexFace complexCalculation completionEvaluation)),
      SourceGeneratedScalarCofinalProjectiveDeterminantDisposition.bounded
          complexFace complexCalculation completionEvaluation
          generatedDualObservation =
        .boundedDualizable equivalence finite projective duality ∧
      SourceGeneratedScalarBoundedProjectiveDeterminantDisposition.settle
          (observation := generatedDualObservation)
          (.boundedDualizable (observation := generatedDualObservation)
            equivalence finite projective duality) =
        .boundedProjective equivalence finite projective duality
          (SourceGeneratedScalarProjectiveDeterminantDisposition.settle
            finite projective) ∧
      ∃ (readout : SourceGeneratedScalarConstantRankDeterminant.Readout
          (R := ℂ)
          (M := SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
            complexFace complexCalculation completionEvaluation))
        (picard : readout.PicardDisposition),
        SourceGeneratedScalarProjectiveDeterminantDisposition.settle
            finite projective = .constant readout picard := by
  obtain ⟨equivalence, finite, projective, duality, boundedEquality⟩ :=
    cofinalBounded_positive
  let free : Module.Free ℂ
      (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        complexFace complexCalculation completionEvaluation) := inferInstance
  have constantRank :
      Module.rankAtStalk
          (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
            complexFace complexCalculation completionEvaluation) =
        fun _ : PrimeSpectrum ℂ =>
          Module.finrank ℂ
            (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
              complexFace complexCalculation completionEvaluation) := by
    letI : Module.Free ℂ
        (SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
          complexFace complexCalculation completionEvaluation) := free
    funext prime
    exact congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := ℂ)
      (M := SourceGeneratedScalarCofinalExactEnvelope.GeneratedDual
        complexFace complexCalculation completionEvaluation)) prime
  exact ⟨equivalence, finite, projective, duality, boundedEquality, rfl,
    SourceGeneratedScalarProjectiveDeterminantDisposition.settle_constant_of_constantRank
      finite projective _ constantRank⟩

def identityDataMorphism :
    SourceGeneratedScalarCofinalNaturality.Morphism
      complexFace.data complexFace.data :=
  SourceGeneratedScalarCofinalNaturality.Morphism.id complexFace.data

def identityRootMorphism : RootMorphism complexFace complexFace where
  dataMorphism := identityDataMorphism
  rootMap := id
  root_naturality := (RootedAccountedUnfolding.map_id complexFace.root).symm

theorem identityEvaluationSquare :
    (inducedDualTarget (LinearMap.id : ℂ →ₗ[ℂ] ℂ)).comp
        completionEvaluation =
      completionEvaluation.comp
        (identityRootMorphism.completionMorphism
          complexCalculation complexCalculation).hom := by
  rw [show identityRootMorphism.completionMorphism
      complexCalculation complexCalculation =
        𝟙 (complexFace.completion complexCalculation) by
    exact SourceGeneratedScalarCofinalNaturality.Morphism.completionMorphism_id
      complexFace.data complexCalculation.laws]
  rfl

example :
    (SourceGeneratedScalarCofinalExactEnvelopeNaturality.carrierMap
      identityRootMorphism complexCalculation complexCalculation
      completionEvaluation completionEvaluation LinearMap.id
      identityEvaluationSquare).comp sourceEnvelopeMap =
    sourceEnvelopeMap.comp identityDataMorphism.generatorMap :=
  SourceGeneratedScalarCofinalExactEnvelopeNaturality.carrierMap_source_naturality
    identityRootMorphism complexCalculation complexCalculation
    completionEvaluation completionEvaluation LinearMap.id
    identityEvaluationSquare

#print axioms SourceGeneratedScalarCofinalExactEnvelope.source_evaluation_readback
#print axioms SourceGeneratedScalarCofinalExactEnvelope.sourceMap_eq_zero_iff
#print axioms SourceGeneratedScalarCofinalExactEnvelope.completion_universal_property
#print axioms SourceGeneratedScalarCofinalObservationDisposition.exact_iff_bijective
#print axioms SourceGeneratedScalarCofinalBoundedDisposition.total
#print axioms cofinalFreeDeterminant_positive
#print axioms cofinalProjectiveDeterminant_positive
#print axioms SourceGeneratedScalarCofinalExactEnvelopeNaturality.carrierMap_source_naturality
#print axioms SourceGeneratedScalarCofinalExactEnvelopeNaturality.coevaluation_naturality
#print axioms completionEvaluation_source_one

end
end SourceGeneratedScalarCofinalExactEnvelopeRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

import H0mework.Realization.Perfectification.SourceCoimage
import H0mework.Realization.Perfectification.IntegralPair
import H0mework.Realization.Perfectification.ExactObservation
import H0mework.Realization.Perfectification.AmbientExtension
import H0mework.Foundation.Cofinal.KernelCompletion
import H0mework.Foundation.Cofinal.CoverageResidual

/-!
# Universal cofinal perfectification

This is the cofinal continuation of the source-generated coimage mouth.  An
actual dependent evaluator occurrence first generates the kernel quotient
tower and its categorical completion; the coverage-residual tower is then
formed from the same completion and the same compatibility calculation.  A
dual evaluation on that completed carrier is fed to the canonical
`C / ker(e)` producer, so finite observations, perfect ambient evidence, and
representation residuals all refer to one source-owned cofinal carrier.

No finite, free, projective, perfect, determinant, inverse-limit, or coverage
claim is accepted as an input.  The only extra input is the source's actual
stage compatibility law.  The residual map into the finite-residual limit is
the existing faithful tower map and its injectivity is exposed directly.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace UniversalCofinalPerfectification

open CofinalKernelCompletion
open CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt
open CofinalCoverageResidualTower
open CofinalCoverageResidualTower.RootGeneratedCofinalCoverageResidualTowerAt
open SourceGeneratedPerfectification
open SourceGeneratedCanonicalPerfectPair
open ExactPerfectEnvelopeBoundedDisposition
open SourceGeneratedPerfectAmbient

noncomputable section

universe u w d a

variable {Root : Type w} {Generator : Type u} [AddCommGroup Generator]
variable {StageCarrier : Nat → Type u}
variable [∀ stage, AddCommGroup (StageCarrier stage)]
variable {DualTarget : Type d} [AddCommGroup DualTarget]
variable {dependentOccurrence : RootedAccountedUnfolding
  (Root × AdditiveCofinalEvaluatorData Generator StageCarrier)}

abbrev CompletionFace
    (dependentOccurrence : RootedAccountedUnfolding
      (Root × AdditiveCofinalEvaluatorData Generator StageCarrier)) :=
  RootGeneratedCofinalKernelCompletionAt dependentOccurrence

abbrev CompletedCarrier
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :=
  face.completion calculation

abbrev CoverageFace
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :=
  RootGeneratedCofinalCoverageResidualTowerAt
    (completionFace := face) (calculation := calculation)

def coverageFace
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    CoverageFace face calculation :=
  RootGeneratedCofinalCoverageResidualTowerAt.generate

/-! ## One cofinal carrier, one perfectification -/

structure Generated
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) : Type (max (max u w) d + 4) where
  completion : CompletionFace dependentOccurrence
  coverage : CoverageFace face calculation
  perfectification :
    SourceGeneratedPerfectification.PerfectificationDisposition evaluation
  canonicalPerfectPair :
    SourceGeneratedCanonicalPerfectPair.Generated evaluation
  ambient :
    SourceGeneratedPerfectAmbient.PerfectAmbientExtensionDisposition evaluation

def generate
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) :
    Generated face calculation evaluation where
  completion := face
  coverage := coverageFace face calculation
  perfectification := SourceGeneratedPerfectification.settlePerfectification evaluation
  canonicalPerfectPair := SourceGeneratedCanonicalPerfectPair.generate evaluation
  ambient := SourceGeneratedPerfectAmbient.settlePerfectAmbientExtension evaluation

theorem generated_total
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) :
    Nonempty (Generated face calculation evaluation) :=
  ⟨generate face calculation evaluation⟩

@[simp] theorem generated_completion
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) :
    (generate face calculation evaluation).completion = face :=
  rfl

@[simp] theorem generated_coverage
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) :
    (generate face calculation evaluation).coverage = coverageFace face calculation :=
  rfl

def canonicalMap
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) :
    CompletedCarrier face calculation →ₗ[ℤ]
      SourceGeneratedPerfectification.PerfectificationCarrier evaluation :=
  SourceGeneratedPerfectification.canonicalMap evaluation

def dualEmbedding
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) :
    SourceGeneratedPerfectification.PerfectificationCarrier evaluation →ₗ[ℤ]
      Module.Dual ℤ DualTarget :=
  SourceGeneratedPerfectification.dualEmbedding evaluation

@[simp] theorem dualEmbedding_comp_canonicalMap
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) :
    (dualEmbedding face calculation evaluation).comp
        (canonicalMap face calculation evaluation) = evaluation :=
  SourceGeneratedPerfectification.dualEmbedding_comp_canonicalMap evaluation

theorem canonicalMap_universal
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget)
    {Q : Type a} [AddCommGroup Q]
    (map : CompletedCarrier face calculation →ₗ[ℤ] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map) :
    ∃! factor : SourceGeneratedPerfectification.PerfectificationCarrier evaluation
        →ₗ[ℤ] Q,
      factor.comp (canonicalMap face calculation evaluation) = map :=
  SourceGeneratedPerfectification.canonicalMap_universal evaluation map
    kernel_compatibility

theorem canonicalPerfectPair_readback
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget) :
    (generate face calculation evaluation).canonicalPerfectPair.inclusion.comp
        (generate face calculation evaluation).canonicalPerfectPair.map =
      SourceGeneratedPerfectification.dualEmbedding evaluation :=
  SourceGeneratedCanonicalPerfectPair.generated_readback evaluation

def boundedObservationDisposition
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (evaluation : CompletedCarrier face calculation →ₗ[ℤ]
      Module.Dual ℤ DualTarget)
    {O : Type a} [AddCommGroup O]
    (observation :
      SourceGeneratedPerfectification.PerfectificationCarrier evaluation →ₗ[ℤ] O) :
    ExactPerfectEnvelopeBoundedDisposition.Disposition evaluation observation :=
  ExactPerfectEnvelopeBoundedDisposition.settle evaluation observation

/-! ## Cofinal residual is a faithful sibling, not a replacement carrier -/

def cofinalResidualMap
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    face.CompletionResidual calculation →+
      (coverageFace face calculation).residualLimit :=
  (coverageFace face calculation).completionResidualToResidualLimit

theorem completionResidualToResidualLimit_injective
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    Function.Injective (cofinalResidualMap face calculation) := by
  exact (coverageFace face calculation).completionResidualToResidualLimit_injective

theorem completionResidual_subsingleton_of_residualLimit_subsingleton
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face)
    (historyRigid : Subsingleton (coverageFace face calculation).residualLimit) :
    Subsingleton (face.CompletionResidual calculation) :=
  (coverageFace face calculation).completionResidual_subsingleton_of_residualLimit_subsingleton
    historyRigid

def residualDisposition
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    CoverageSettlementOutcome face calculation :=
  face.settleCoverage calculation

theorem residualDisposition_total
    (face : CompletionFace dependentOccurrence)
    (calculation : GeneratedCompatibilityCalculationAt face) :
    Nonempty (CoverageSettlementOutcome face calculation) :=
  ⟨residualDisposition face calculation⟩

/-! ## Root and successor provenance are inherited from the occurrence -/

def sourceRoot
    (face : CompletionFace dependentOccurrence) :
    RootedAccountedUnfolding Root :=
  face.root

theorem sourceRoot_map
    (face : CompletionFace dependentOccurrence) :
    face.root = dependentOccurrence.map Prod.fst :=
  rfl

end
end UniversalCofinalPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

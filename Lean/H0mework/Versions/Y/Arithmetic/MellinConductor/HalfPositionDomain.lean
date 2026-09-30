import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import H0mework.Realization.Operators.MaximalLpMultiplication
import H0mework.Versions.Y.Arithmetic.MellinConductor.GraphLogPosition

/-!
# Maximal Quarter-Mellin half-position domain

Multiplication by `x/2` is installed on the actual Quarter-Mellin energy as
the canonical maximal Lp multiplication operator.  Its domain is dense, its
graph is closed, and its output is the same pointwise coordinate used by the
corrected Müntz graph cone.  It is not promoted to a bounded whole-space map.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace MuntzConductor
namespace HalfPositionDomain

open Filter GenericFoundation.Analysis.MaximalLpMultiplication MeasureTheory Set
open GraphLogPositionCone

open scoped ENNReal SchwartzMap

noncomputable section

def halfPositionMultiplier (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (x : ℂ)

theorem halfPositionMultiplier_eq_graphCoordinate (x : ℝ) :
    halfPositionMultiplier x = ((x / 2 : ℝ) : ℂ) := by
  unfold halfPositionMultiplier
  push_cast
  ring

abbrev HalfPositionOperator :=
  GenericFoundation.Analysis.MaximalLpMultiplication.operator
    (2 : ℝ≥0∞) (volume : Measure ℝ) halfPositionMultiplier

theorem halfPositionOperator_graph :
    HalfPositionOperator.graph =
      GenericFoundation.Analysis.MaximalLpMultiplication.graph
        (2 : ℝ≥0∞) (volume : Measure ℝ) halfPositionMultiplier :=
  GenericFoundation.Analysis.MaximalLpMultiplication.operator_graph
    (2 : ℝ≥0∞) (volume : Measure ℝ) halfPositionMultiplier

theorem halfPositionOperator_isClosed :
    HalfPositionOperator.IsClosed :=
  GenericFoundation.Analysis.MaximalLpMultiplication.operator_isClosed
    (2 : ℝ≥0∞) (volume : Measure ℝ) halfPositionMultiplier

theorem halfPositionOperator_isClosable :
    HalfPositionOperator.IsClosable :=
  halfPositionOperator_isClosed.isClosable

theorem halfPositionOperator_apply_ae
    (value : HalfPositionOperator.domain) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      HalfPositionOperator value x =
        ((x / 2 : ℝ) : ℂ) * value.1 x := by
  filter_upwards [GenericFoundation.Analysis.MaximalLpMultiplication.operator_apply_ae
      (2 : ℝ≥0∞) (volume : Measure ℝ) halfPositionMultiplier value]
    with x atPoint
  simpa only [halfPositionMultiplier_eq_graphCoordinate] using atPoint

theorem mem_halfPositionOperator_domain_iff
    (value : PositiveMellinQuarterEnergy) :
    value ∈ HalfPositionOperator.domain ↔
      MemLp (fun x : ℝ => ((x / 2 : ℝ) : ℂ) * value x)
        (2 : ℝ≥0∞) (volume : Measure ℝ) := by
  simpa only [halfPositionMultiplier_eq_graphCoordinate] using
    (GenericFoundation.Analysis.MaximalLpMultiplication.mem_operator_domain_iff
      (2 : ℝ≥0∞) (volume : Measure ℝ) halfPositionMultiplier value)

/-- Failure of the weighted L2 premise remains an explicit domain residual;
it cannot be hidden by treating half-position as a total bounded map. -/
theorem not_mem_halfPositionOperator_domain_iff
    (value : PositiveMellinQuarterEnergy) :
    value ∉ HalfPositionOperator.domain ↔
      ¬ MemLp (fun x : ℝ => ((x / 2 : ℝ) : ℂ) * value x)
        (2 : ℝ≥0∞) (volume : Measure ℝ) := by
  exact not_congr (mem_halfPositionOperator_domain_iff value)

theorem halfPositionMultiplier_temperate :
    halfPositionMultiplier.HasTemperateGrowth := by
  unfold halfPositionMultiplier
  fun_prop

def halfPositionSchwartz :
    𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ halfPositionMultiplier

theorem halfPositionSchwartz_apply (test : 𝓢(ℝ, ℂ)) (x : ℝ) :
    halfPositionSchwartz test x = ((x / 2 : ℝ) : ℂ) * test x := by
  rw [halfPositionSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply halfPositionMultiplier_temperate,
    halfPositionMultiplier_eq_graphCoordinate]
  rfl

theorem schwartz_toLp_mem_halfPositionOperator_domain
    (test : 𝓢(ℝ, ℂ)) :
    test.toLp (2 : ℝ≥0∞) (volume : Measure ℝ) ∈
      HalfPositionOperator.domain := by
  rw [mem_halfPositionOperator_domain_iff]
  have outputMem := (halfPositionSchwartz test).memLp
    (2 : ℝ≥0∞) (volume : Measure ℝ)
  exact (memLp_congr_ae <| by
    filter_upwards [test.coeFn_toLp (2 : ℝ≥0∞) (volume : Measure ℝ)]
      with x testAt
    rw [testAt, halfPositionSchwartz_apply]).mpr outputMem

theorem halfPositionOperator_dense_domain :
    Dense (HalfPositionOperator.domain : Set PositiveMellinQuarterEnergy) := by
  apply (SchwartzMap.denseRange_toLpCLM
    (E := ℝ) (F := ℂ) (μ := (volume : Measure ℝ))
    (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top).mono
  intro value mem
  rcases mem with ⟨test, rfl⟩
  exact schwartz_toLp_mem_halfPositionOperator_domain test

/-- The unbounded operator output is precisely the raw `x/2` graph
coordinate of the same Lp representative. -/
theorem halfPositionOperator_reads_graphLogPosition
    (value : HalfPositionOperator.domain) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      HalfPositionOperator value x =
        graphLogPosition (fun y : ℝ => value.1 y) x := by
  filter_upwards [halfPositionOperator_apply_ae value] with x atPoint
  simpa only [graphLogPosition] using atPoint

end
end HalfPositionDomain
end MuntzConductor
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

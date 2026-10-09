import Mathlib.Analysis.InnerProductSpace.GramMatrix
import H0mework.Versions.R2.Arithmetic.MuntzAction.CoPoissonMuntzGraphCokernel
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier
import H0mework.Realization.Graph.Realization

/-!
# Gram boundary for a Burnol physical realization

The existing pre-quotient graph source is dense and remembers both quarter
energy and Mellin measurement.  Its two-point Gram matrix is exactly the sum
of those two coordinate Gram matrices.  On an actual co-Poisson relation at a
zeta zero the measurement summand vanishes.

These identities are the exact source-side contract for a future landing in
`BurnolPhysicalState.burnolFace`.  This file does not assert that landing or
rename the graph completion as a Burnol space.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open SourceGeneratedComplexFeaturePerfectification
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedFunctionalGraphCokernel
open scoped InnerProductSpace

noncomputable section

universe c h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [CompleteSpace H]

abbrev QuarterMellinGraphCompletion (z : ℂ) :=
  GraphCompletion (quarterMellinL2Feature z) (quarterMellinL2Functional z)

/-- Concrete dense source before quotienting by the co-Poisson relation. -/
def quarterMellinGraphDenseSourceMap (z : ℂ) :
    QuarterMellinL2Test z →ₗ[ℂ] QuarterMellinGraphCompletion z :=
  graphSourceMap (quarterMellinL2Feature z) (quarterMellinL2Functional z)

theorem quarterMellinGraphDenseSourceMap_denseRange (z : ℂ) :
    DenseRange (quarterMellinGraphDenseSourceMap z) :=
  graphSourceMap_denseRange
    (quarterMellinL2Feature z) (quarterMellinL2Functional z)

/-- The canonical realization reads both coordinates without loss. -/
theorem quarterMellinGraphDenseSourceMap_realization_readback
    (z : ℂ) (value : QuarterMellinL2Test z) :
    let realized := graphHilbertAmbientRealization
      (quarterMellinL2Feature z) (quarterMellinL2Functional z)
      (quarterMellinGraphDenseSourceMap z value)
    realized.fst = quarterMellinL2Feature z value ∧
      realized.snd = quarterMellinL2Functional z value := by
  simp [quarterMellinGraphDenseSourceMap, graphSourceMap]

theorem graphSourceMap_inner_eq_energy_add_measurement
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (left right : C) :
    ⟪graphSourceMap feature functional left,
        graphSourceMap feature functional right⟫_ℂ =
      ⟪feature left, feature right⟫_ℂ +
        ⟪functional left, functional right⟫_ℂ := by
  rw [← (graphHilbertAmbientRealization feature functional).inner_map_map]
  change ⟪graphHilbertAmbientRealization feature functional
        (canonicalHilbertMap (graphFeature feature functional) left),
      graphHilbertAmbientRealization feature functional
        (canonicalHilbertMap (graphFeature feature functional) right)⟫_ℂ = _
  rw [graphHilbertAmbientRealization_source_readback,
    graphHilbertAmbientRealization_source_readback,
    WithLp.prod_inner_apply]
  rfl

/-- Minimal polarization test for any proposed physical realization. -/
theorem graphSourceMap_finTwo_gram
    (feature : C →ₗ[ℂ] H) (functional : C →ₗ[ℂ] ℂ)
    (source : Fin 2 → C) :
    Matrix.gram ℂ (fun i ↦ graphSourceMap feature functional (source i)) =
      Matrix.gram ℂ (fun i ↦ feature (source i)) +
        Matrix.gram ℂ (fun i ↦ functional (source i)) := by
  ext i j
  exact graphSourceMap_inner_eq_energy_add_measurement
    feature functional (source i) (source j)

theorem quarterMellinGraphSource_finTwo_gram
    (z : ℂ) (source : Fin 2 → QuarterMellinL2Test z) :
    Matrix.gram ℂ
        (fun i ↦ quarterMellinGraphDenseSourceMap z (source i)) =
      Matrix.gram ℂ (fun i ↦ quarterMellinL2Feature z (source i)) +
        Matrix.gram ℂ
          (fun i ↦ quarterMellinL2Functional z (source i)) :=
  graphSourceMap_finTwo_gram
    (quarterMellinL2Feature z) (quarterMellinL2Functional z) source

/-- Direct relation consumer: at a zeta zero the actual co-Poisson relation
has no hidden Mellin Gram term. -/
theorem coPoissonRelationGraphSource_finTwo_gram_at_zero
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0) (source : Fin 2 → SchwartzMap ℝ ℂ) :
    Matrix.gram ℂ (fun i ↦
        quarterMellinGraphDenseSourceMap z
          (coPoissonQuarterMellinConvergentMap z positive belowHalf
            (source i))) =
      Matrix.gram ℂ (fun i ↦
        quarterMellinL2Feature z
          (coPoissonQuarterMellinConvergentMap z positive belowHalf
            (source i))) := by
  rw [quarterMellinGraphSource_finTwo_gram]
  have annihilates :=
    quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      z positive belowHalf zero
  have measurementZero : (fun i ↦
      quarterMellinL2Functional z
        (coPoissonQuarterMellinConvergentMap z positive belowHalf
          (source i))) = 0 := by
    funext i
    exact LinearMap.congr_fun annihilates (source i)
  rw [measurementZero, Matrix.gram_zero, add_zero]

end

end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.quarterMellinGraphDenseSourceMap_denseRange
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.graphSourceMap_finTwo_gram
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.coPoissonRelationGraphSource_finTwo_gram_at_zero

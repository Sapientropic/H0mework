import H0mework.Arithmetic.Muntz.CoPoissonMuntzFactorization
import H0mework.Realization.Graph.CokernelDuality
import H0mework.Versions.Y.Arithmetic.MellinBoundary.PositiveMellinQuarterTranslationNoGo

/-!
# Graph-cokernel perfectification of the co-Poisson--Müntz relation

At a zeta zero in the open quarter strip, the general Müntz identity kills
the complete arbitrary-Schwartz relation map.  The generic functional graph
cokernel then generates a complete quotient, a nonzero descended continuous
coordinate, and its canonical Riesz representer.  No bounded evaluator,
closed-range, finite, or determinant premise is accepted.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open SourceGeneratedFunctionalGraphCokernel
open scoped InnerProductSpace

noncomputable section

def coPoissonMuntzQuarterShellTest (z : ℂ) (positive : 0 < z.re) :
    QuarterMellinL2Test z :=
  ⟨positiveMellinQuarterNoGoShell,
    ⟨positiveMellinQuarterNoGoShellL2.2,
      (positiveMellinQuarterNoGoShellElement z positive).2⟩⟩

theorem quarterMellinL2Functional_ne_zero
    (z : ℂ) (positive : 0 < z.re) :
    quarterMellinL2Functional z ≠ 0 := by
  intro zero
  have atShell := LinearMap.congr_fun zero
    (coPoissonMuntzQuarterShellTest z positive)
  rw [LinearMap.zero_apply] at atShell
  exact (positiveMellinQuarterNoGoShellElement_value_ne_zero z positive)
    atShell

abbrev CoPoissonMuntzGraphCokernel
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :=
  ClosedRangeQuotient
    (quarterMellinL2Feature z)
    (quarterMellinL2Functional z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf)

def coPoissonMuntzGraphSourceMap
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    QuarterMellinL2Test z →ₗ[ℂ]
      CoPoissonMuntzGraphCokernel z positive belowHalf :=
  canonicalSourceMap
    (quarterMellinL2Feature z)
    (quarterMellinL2Functional z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf)

theorem coPoissonMuntzGraphSourceMap_relation
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    coPoissonMuntzGraphSourceMap z positive belowHalf
        (coPoissonQuarterMellinConvergentMap z positive belowHalf test) = 0 := by
  exact canonicalSourceMap_relation
    (quarterMellinL2Feature z)
    (quarterMellinL2Functional z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf) test

def coPoissonMuntzDescendedFunctional
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0) :
    CoPoissonMuntzGraphCokernel z positive belowHalf →L[ℂ] ℂ :=
  descendedFunctional
    (quarterMellinL2Feature z)
    (quarterMellinL2Functional z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf)
    (quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      z positive belowHalf zero)

theorem coPoissonMuntzDescendedFunctional_ne_zero
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0) :
    coPoissonMuntzDescendedFunctional z positive belowHalf zero ≠ 0 := by
  exact descendedFunctional_ne_zero
    (quarterMellinL2Feature z)
    (quarterMellinL2Functional z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf)
    (quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      z positive belowHalf zero)
    (quarterMellinL2Functional_ne_zero z positive)

def coPoissonMuntzRieszVector
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0) :
    CoPoissonMuntzGraphCokernel z positive belowHalf :=
  descendedRieszVector
    (quarterMellinL2Feature z)
    (quarterMellinL2Functional z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf)
    (quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      z positive belowHalf zero)

theorem coPoissonMuntzRieszVector_ne_zero
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0) :
    coPoissonMuntzRieszVector z positive belowHalf zero ≠ 0 := by
  exact descendedRieszVector_ne_zero
    (quarterMellinL2Feature z)
    (quarterMellinL2Functional z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf)
    (quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      z positive belowHalf zero)
    (quarterMellinL2Functional_ne_zero z positive)

theorem coPoissonMuntzRieszVector_source_readback
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (zero : riemannZeta (2 * z) = 0) (value : QuarterMellinL2Test z) :
    ⟪coPoissonMuntzRieszVector z positive belowHalf zero,
      coPoissonMuntzGraphSourceMap z positive belowHalf value⟫_ℂ =
        quarterMellinL2Functional z value := by
  exact descendedRieszVector_source_readback
    (quarterMellinL2Feature z)
    (quarterMellinL2Functional z)
    (coPoissonQuarterMellinConvergentMap z positive belowHalf)
    (quarterMellinL2Functional_comp_coPoissonQuarterMellinConvergentMap_eq_zero
      z positive belowHalf zero) value

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

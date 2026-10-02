import H0mework.Versions.R2.Arithmetic.MuntzAction.CoPoissonMuntzRieszDilation

/-!
# Actual dilation square for the full Müntz relation family

Square-root scaling on arbitrary Schwartz tests generates the normalized
positive dilation on the quarter-Mellin relation.  The square holds for the
whole relation map, not just a selected shell or quotient representative.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open ClozelEndpointSourceEffect
open scoped SchwartzMap

noncomputable section

/-- Source Schwartz action whose square-root scaling generates normalized
quarter-Mellin dilation on the actual Müntz relation. -/
def quarterMuntzSchwartzDilationAction
    (scale : ℝ) (positive : 0 < scale) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap ℝ ℂ where
  toFun test := positiveMellinQuarterDilationWeight scale •
    scaledSchwartzTest (Real.sqrt scale)
      (Real.sqrt_pos.2 positive).ne' test
  map_add' left right := by
    unfold scaledSchwartzTest
    rw [map_add, smul_add]
  map_smul' coefficient test := by
    unfold scaledSchwartzTest
    rw [map_smul]
    simp only [smul_smul]
    congr 1
    exact mul_comm _ _

theorem quarterDilation_muntzRelation_square
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale) :
    (quarterDilationTestAction z scale positive).comp
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf) =
      (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf).comp
        (quarterMuntzSchwartzDilationAction scale positive) := by
  apply LinearMap.ext
  intro test
  apply Subtype.ext
  funext t
  change positiveMellinQuarterDilationWeight scale *
      clozelTemperedRemainder
        (scaledSchwartzTest (Real.sqrt (scale * t.1))
          (Real.sqrt_pos.2 (mul_pos positive t.2)).ne' test) =
    clozelTemperedRemainder
      (scaledSchwartzTest (Real.sqrt t.1)
        (Real.sqrt_pos.2 t.2).ne'
        (positiveMellinQuarterDilationWeight scale •
          scaledSchwartzTest (Real.sqrt scale)
            (Real.sqrt_pos.2 positive).ne' test))
  have scaledEq :
      scaledSchwartzTest (Real.sqrt t.1) (Real.sqrt_pos.2 t.2).ne'
          (positiveMellinQuarterDilationWeight scale •
            scaledSchwartzTest (Real.sqrt scale)
              (Real.sqrt_pos.2 positive).ne' test) =
        positiveMellinQuarterDilationWeight scale •
          scaledSchwartzTest (Real.sqrt (scale * t.1))
            (Real.sqrt_pos.2 (mul_pos positive t.2)).ne' test := by
    apply SchwartzMap.ext
    intro x
    change positiveMellinQuarterDilationWeight scale *
        test (Real.sqrt scale * (Real.sqrt t.1 * x)) =
      positiveMellinQuarterDilationWeight scale *
        test (Real.sqrt (scale * t.1) * x)
    congr 2
    rw [Real.sqrt_mul positive.le]
    ring
  rw [scaledEq, map_smul]
  rfl

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

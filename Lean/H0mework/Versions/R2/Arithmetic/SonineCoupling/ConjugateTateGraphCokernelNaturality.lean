import H0mework.Realization.Graph.CokernelSemilinearIsometry
import H0mework.Versions.R2.Arithmetic.MuntzAction.CoPoissonMuntzGraphCokernel
import H0mework.Versions.R2.Arithmetic.SonineCoupling.ConjugateTateGraphSourceMorphism

/-!
# Conjugate--Tate naturality on the actual Müntz graph cokernel

The actual one-way graph-relation morphism generates the quotient map, its
source and relation readbacks, and conjugation of the descended functional.
The generated-high class and an independent reversal-low class are not
identified: their difference remains an explicit source and quotient
residual.  Since no isometric equivalence of Schwartz relation carriers is
input, the quotient result is the generated contraction, not a free
antiunitary equivalence; its generic contraction consequence remains a
separate generic theorem rather than a slow domain wrapper.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open SourceGeneratedFunctionalGraphCokernel
open SourceGeneratedFunctionalGraphPerfectification

noncomputable section

abbrev ConjugateTateGeneratedHighGraphCokernel
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ)) :=
  CoPoissonMuntzGraphCokernel
    (conjugateTateMellinParameter z)
    (conjugateTateMellinParameter_re_pos z belowHalf)
    (conjugateTateMellinParameter_re_lt_half z positive)

/-- The one-way quotient map generated from the actual conjugate--Tate
source and relation squares. -/
def conjugateTateCoPoissonMuntzQuotientMap
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ)) :
    CoPoissonMuntzGraphCokernel z positive belowHalf →L⋆[ℂ]
      ConjugateTateGeneratedHighGraphCokernel z positive belowHalf :=
  (conjugateTateRelationGraphSourceMorphism
    z positive belowHalf).quotientMap

@[simp]
theorem conjugateTateCoPoissonMuntzQuotientMap_source
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (value : QuarterMellinL2Test z) :
    conjugateTateCoPoissonMuntzQuotientMap z positive belowHalf
        (coPoissonMuntzGraphSourceMap z positive belowHalf value) =
      coPoissonMuntzGraphSourceMap
        (conjugateTateMellinParameter z)
        (conjugateTateMellinParameter_re_pos z belowHalf)
        (conjugateTateMellinParameter_re_lt_half z positive)
        (conjugateTateQuarterMellinTest z value) := by
  exact (conjugateTateRelationGraphSourceMorphism
    z positive belowHalf).quotientMap_source_readback value

/-- The entire actual Schwartz relation is transported to the target
relation and hence remains zero in the generated quotient. -/
@[simp]
theorem conjugateTateCoPoissonMuntzQuotientMap_relation
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    conjugateTateCoPoissonMuntzQuotientMap z positive belowHalf
        (coPoissonMuntzGraphSourceMap z positive belowHalf
          (coPoissonQuarterMellinConvergentMap
            z positive belowHalf test)) = 0 := by
  rw [coPoissonMuntzGraphSourceMap_relation, map_zero]

/-- Descended Mellin evaluation is conjugated on every generated quotient
class.  The two annihilation laws are the exact relation-admission evidence. -/
theorem conjugateTateCoPoissonMuntzDescendedFunctional_naturality
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (annihilates :
      (quarterMellinL2Functional z).comp
        (coPoissonQuarterMellinConvergentMap z positive belowHalf) = 0)
    (annihilatesHigh :
      (quarterMellinL2Functional (conjugateTateMellinParameter z)).comp
        (coPoissonQuarterMellinConvergentMap
          (conjugateTateMellinParameter z)
          (conjugateTateMellinParameter_re_pos z belowHalf)
          (conjugateTateMellinParameter_re_lt_half z positive)) = 0)
    (quotient : CoPoissonMuntzGraphCokernel z positive belowHalf) :
    descendedFunctional
        (quarterMellinL2Feature (conjugateTateMellinParameter z))
        (quarterMellinL2Functional (conjugateTateMellinParameter z))
        (coPoissonQuarterMellinConvergentMap
          (conjugateTateMellinParameter z)
          (conjugateTateMellinParameter_re_pos z belowHalf)
          (conjugateTateMellinParameter_re_lt_half z positive))
        annihilatesHigh
        (conjugateTateCoPoissonMuntzQuotientMap
          z positive belowHalf quotient) =
      star (descendedFunctional
        (quarterMellinL2Feature z)
        (quarterMellinL2Functional z)
        (coPoissonQuarterMellinConvergentMap z positive belowHalf)
        annihilates quotient) := by
  exact (conjugateTateRelationGraphSourceMorphism
    z positive belowHalf).descendedFunctional_quotientMap
      annihilates annihilatesHigh quotient

/-- Difference between the generated high test and an independently supplied
low-chart test at the same target parameter. -/
def conjugateTateGeneratedHighReversalSourceResidual
    (z : ℂ) (selectedLow : QuarterMellinL2Test z)
    (reversalLow : QuarterMellinL2Test
      (conjugateTateMellinParameter z)) :
    QuarterMellinL2Test (conjugateTateMellinParameter z) :=
  conjugateTateQuarterMellinTest z selectedLow - reversalLow

/-- The same generated-high minus reversal-low residual in the actual
closed-relation quotient. -/
def conjugateTateGeneratedHighReversalQuotientResidual
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (selectedLow : QuarterMellinL2Test z)
    (reversalLow : QuarterMellinL2Test
      (conjugateTateMellinParameter z)) :
    ConjugateTateGeneratedHighGraphCokernel z positive belowHalf :=
  conjugateTateCoPoissonMuntzQuotientMap z positive belowHalf
      (coPoissonMuntzGraphSourceMap z positive belowHalf selectedLow) -
    coPoissonMuntzGraphSourceMap
      (conjugateTateMellinParameter z)
      (conjugateTateMellinParameter_re_pos z belowHalf)
      (conjugateTateMellinParameter_re_lt_half z positive)
      reversalLow

theorem conjugateTateGeneratedHighReversalQuotientResidual_source
    (z : ℂ) (positive : 0 < z.re)
    (belowHalf : z.re < (1 / 2 : ℝ))
    (selectedLow : QuarterMellinL2Test z)
    (reversalLow : QuarterMellinL2Test
      (conjugateTateMellinParameter z)) :
    conjugateTateGeneratedHighReversalQuotientResidual
        z positive belowHalf selectedLow reversalLow =
      coPoissonMuntzGraphSourceMap
        (conjugateTateMellinParameter z)
        (conjugateTateMellinParameter_re_pos z belowHalf)
        (conjugateTateMellinParameter_re_lt_half z positive)
        (conjugateTateGeneratedHighReversalSourceResidual
          z selectedLow reversalLow) := by
  rw [conjugateTateGeneratedHighReversalQuotientResidual,
    conjugateTateCoPoissonMuntzQuotientMap_source]
  unfold conjugateTateGeneratedHighReversalSourceResidual
  exact (map_sub
    (coPoissonMuntzGraphSourceMap
      (conjugateTateMellinParameter z)
      (conjugateTateMellinParameter_re_pos z belowHalf)
      (conjugateTateMellinParameter_re_lt_half z positive))
    (conjugateTateQuarterMellinTest z selectedLow) reversalLow).symm

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

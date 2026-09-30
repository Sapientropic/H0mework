import H0mework.Versions.Y.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartAlgebra
import H0mework.Versions.Y.Arithmetic.RiemannAnnulus.CompactCoPoissonQuarterProjection
import H0mework.Arithmetic.BurnolCarrier.CompactAnnulusClosedRange

/-! Source addition and scaling are transported by the original quarter rechart. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
noncomputable section

def burnolCompactAdditivePhysicalLinear : burnolCompactAnnulusSource →ₗ[ℂ] (EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius) where
  toFun := burnolCompactAdditivePhysicalState
  map_add' a b := by
    apply Subtype.ext
    change burnolCompactAdditiveL2 (a + b) = burnolCompactAdditiveL2 a + burnolCompactAdditiveL2 b
    simp_rw [← compactQuarterMellinAdditiveEvenRechart_eq (3 / 8) (by norm_num) (by norm_num)]
    change quarterMellinAdditiveEvenRechartLinear (3 / 8)
        (coPoissonQuarterMellinConvergentMap (3 / 8) (by norm_num) (by norm_num) (a.1 + b.1)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c a := by
    apply Subtype.ext
    change burnolCompactAdditiveL2 (c • a) = c • burnolCompactAdditiveL2 a
    simp_rw [← compactQuarterMellinAdditiveEvenRechart_eq (3 / 8) (by norm_num) (by norm_num)]
    change quarterMellinAdditiveEvenRechartLinear (3 / 8)
        (coPoissonQuarterMellinConvergentMap (3 / 8) (by norm_num) (by norm_num) (c • a.1)) = _
    rw [map_smul, map_smul]
    rfl

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

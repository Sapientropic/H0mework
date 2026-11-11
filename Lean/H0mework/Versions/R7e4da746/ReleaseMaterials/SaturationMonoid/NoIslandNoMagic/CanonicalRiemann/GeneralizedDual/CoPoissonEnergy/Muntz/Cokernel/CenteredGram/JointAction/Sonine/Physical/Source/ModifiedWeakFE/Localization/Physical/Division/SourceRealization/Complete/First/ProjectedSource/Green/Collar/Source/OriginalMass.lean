import H0mework.Versions.R7e4da746.Arithmetic.RiemannRationalSource.EvenWindow

/-! The actual original Pa source has zero outer tail and retains its original Mellin mass. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem original_source_tail_at_or_above_four
    (coordinate : BurnolCompletedMellinCoordinate) (b : ℝ) (outer : 4 ≤ b)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    burnolRadiusMellinTailEvaluator b (lt_of_lt_of_le (by norm_num) outer)
      coordinate.value coordinate.rightHalf
        (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) = 0 := by
  rw [burnolRadiusMellinTailEvaluator_eq_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_of_ae (pa_tate_source_annulus p inside),
    ae_restrict_mem measurableSet_Ioi] with x sourceSupport hx
  have outside : x ∉ burnolSamplingAnnulus := by
    intro inAnnulus
    have lower : 4 < x := lt_of_le_of_lt outer hx
    exact (not_le_of_gt lower) ((le_abs_self x).trans inAnnulus.2)
  simp only [sourceSupport outside, mul_zero, Pi.zero_apply]

theorem original_source_tail_four
    (coordinate : BurnolCompletedMellinCoordinate) (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) = 0 :=
  original_source_tail_at_or_above_four coordinate 4 le_rfl p inside

theorem original_source_mass_eq_coefficient
    (coordinate : BurnolCompletedMellinCoordinate) (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    (2 : ℂ) *
      (burnolRadiusMellinTailEvaluator (1 / 4) (by norm_num)
          coordinate.value coordinate.rightHalf
            (burnolTateReciprocalL2 (burnolMobiusSourceL2 p)) -
        burnolRadiusMellinTailEvaluator 4 (by norm_num) coordinate.value coordinate.rightHalf
          (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))) =
      burnolPaResolventSourceCoefficient coordinate p := by
  rw [original_source_tail_four coordinate p inside, sub_zero]
  rfl

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

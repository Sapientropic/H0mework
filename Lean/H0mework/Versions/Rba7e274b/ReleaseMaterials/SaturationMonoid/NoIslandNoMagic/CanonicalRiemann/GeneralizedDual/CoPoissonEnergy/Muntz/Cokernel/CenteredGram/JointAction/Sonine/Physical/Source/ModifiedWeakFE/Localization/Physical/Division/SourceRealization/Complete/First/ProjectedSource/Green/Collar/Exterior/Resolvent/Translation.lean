import H0mework.Versions.V2.Arithmetic.RemainderSource.ResolventBoundary

/-! The native translated Laplace pairing reads the original direct right resolvent. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen

open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

private def shiftedResolventPairing (v : BurnolL2) (h : ℝ) : BurnolL2 →L[ℂ] ℂ :=
  (innerSL ℂ v).comp (burnolMultiplicativeDilation h).toLinearIsometry.toContinuousLinearMap

private theorem shiftedResolventPairing_integrand
    (z : ℂ) (p v : BurnolL2) (h t : ℝ) :
    shiftedResolventPairing v h (burnolDirectRightResolventIntegrand z p t) =
      positiveMellinQuarterRightResolventWeight z t *
        inner ℂ v (burnolMultiplicativeDilation (h - t / 2) p) := by
  change inner ℂ v (burnolMultiplicativeDilation h
    (positiveMellinQuarterRightResolventWeight z t • burnolMultiplicativeDilation (-t / 2) p)) = _
  rw [map_smul, inner_smul_right, burnolMultiplicativeDilation_add]
  simp only [neg_div, sub_eq_add_neg]

private theorem coordinate_half_rightQuarter (coordinate : BurnolCompletedMellinCoordinate) :
    1 / 4 < (coordinate.value / 2).re := by
  rw [Complex.div_re]
  norm_num
  linarith [coordinate.rightHalf]

/-- The original resolvent's Bochner integrability supplies every translated scalar Laplace pairing. -/
theorem translated_resolvent_pairing_integrable
    (coordinate : BurnolCompletedMellinCoordinate) (p v : BurnolL2) (h : ℝ) :
    IntegrableOn (fun t => positiveMellinQuarterRightResolventWeight (coordinate.value / 2) t *
      inner ℂ v (burnolMultiplicativeDilation (h - t / 2) p)) (Ioi (0 : ℝ)) := by
  have native := (shiftedResolventPairing v h).integrable_comp
    (burnolDirectRightResolventIntegrand_integrableOn (coordinate.value / 2)
      (coordinate_half_rightQuarter coordinate) p)
  exact native.congr (Eventually.of_forall
    (fun t => shiftedResolventPairing_integrand (coordinate.value / 2) p v h t))

/-- The literal translated Laplace integral equals the negative shifted original resolvent pairing. -/
theorem translated_resolvent_pairing
    (coordinate : BurnolCompletedMellinCoordinate) (p v : BurnolL2) (h : ℝ) :
    (∫ t : ℝ in Ioi 0, positiveMellinQuarterRightResolventWeight (coordinate.value / 2) t *
      inner ℂ v (burnolMultiplicativeDilation (h - t / 2) p)) =
        -inner ℂ v (burnolMultiplicativeDilation h
          (burnolDirectRightResolvent (coordinate.value / 2) p)) := by
  have native := (shiftedResolventPairing v h).integral_comp_comm
    (burnolDirectRightResolventIntegrand_integrableOn (coordinate.value / 2)
      (coordinate_half_rightQuarter coordinate) p)
  change _ = -(shiftedResolventPairing v h
    (-∫ t : ℝ in Ioi 0, burnolDirectRightResolventIntegrand (coordinate.value / 2) p t))
  rw [map_neg, neg_neg, ← native]
  apply integral_congr_ae
  filter_upwards with t
  exact (shiftedResolventPairing_integrand (coordinate.value / 2) p v h t).symm

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.V2.Arithmetic.BurnolPhysical.ModifiedWeakFEUnitPhysicalMellinRead

/-!
# Compact co-Poisson quarter projection

For every actual compact-annulus source, the reciprocal-square quarter
rechart is the already generated additive co-Poisson state away from the
measure-zero origin.  Consequently its even projection is literally the
primary `P_a` generator, not a comparison shadow.  At a zeta-zero coordinate
the existing completed-Mellin read and its Riesz pairing therefore vanish on
this same source occurrence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem sqrt_rpow_neg_two {t : ℝ} (positive : 0 < t) :
    Real.sqrt (t ^ (-2 : ℝ)) = t⁻¹ := by
  rw [Real.rpow_neg (le_of_lt positive), Real.rpow_two,
    Real.sqrt_inv, Real.sqrt_sq_eq_abs, abs_of_pos positive]

private theorem positiveExtension_compactQuarterMap_rpow_neg_two
    (source : burnolCompactAnnulusSource) {t : ℝ} (positive : 0 < t) :
    positiveMellinExtension (coPoissonQuarterMellinMap source.1)
        (t ^ (-2 : ℝ)) =
      coPoissonMuntzScaleRemainder source.1 t⁻¹ := by
  have rpowPositive : 0 < t ^ (-2 : ℝ) :=
    Real.rpow_pos_of_pos positive _
  simp only [positiveMellinExtension, coPoissonQuarterMellinMap,
    coPoissonMuntzScaleRemainder, LinearMap.coe_mk, AddHom.coe_mk]
  rw [dif_pos rpowPositive, dif_pos (inv_pos.mpr positive)]
  have scaledEq :
      ClozelEndpointSourceEffect.scaledSchwartzTest
          (Real.sqrt (t ^ (-2 : ℝ)))
          (Real.sqrt_pos.2 rpowPositive).ne' source.1 =
        ClozelEndpointSourceEffect.scaledSchwartzTest t⁻¹
          (inv_pos.mpr positive).ne' source.1 := by
    apply SchwartzMap.ext
    intro x
    simp only [ClozelEndpointSourceEffect.scaledSchwartzTest_apply]
    rw [sqrt_rpow_neg_two positive]
  rw [scaledEq]

private theorem compactQuarterRechartRaw_eq_coSum_of_pos
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (source : burnolCompactAnnulusSource) {t : ℝ} (positive : 0 < t) :
    quarterMellinAdditiveEvenRechartRaw
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf source.1) t =
      burnolCompactAdditiveCoSum source t := by
  rw [quarterMellinAdditiveEvenRechartRaw, abs_of_pos positive]
  unfold quarterMellinAdditivePositiveRechartRaw
  change (1 / 2 : ℂ) • ((t : ℂ) ^ (-(1 : ℂ)) •
      positiveMellinExtension (coPoissonQuarterMellinMap source.1)
        (t ^ (-2 : ℝ))) = _
  rw [positiveExtension_compactQuarterMap_rpow_neg_two source positive,
    coPoissonMuntzScaleRemainder_reciprocal_eq_compactAdditiveCoSum
      source positive]
  simp only [smul_eq_mul]
  push_cast
  rw [Complex.cpow_neg, Complex.cpow_one]
  field_simp [positive.ne']

private theorem compactQuarterRechartRaw_eq_coSum_away_zero
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (source : burnolCompactAnnulusSource) {t : ℝ} (nonzero : t ≠ 0) :
    quarterMellinAdditiveEvenRechartRaw
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf source.1) t =
      burnolCompactAdditiveCoSum source t := by
  by_cases positive : 0 < t
  · exact compactQuarterRechartRaw_eq_coSum_of_pos
      z positiveZ belowHalf source positive
  · have negative : t < 0 :=
      lt_of_le_of_ne (le_of_not_gt positive) nonzero
    calc
      quarterMellinAdditiveEvenRechartRaw
          (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf source.1) t =
          quarterMellinAdditiveEvenRechartRaw
            (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf source.1)
            (-t) :=
        (quarterMellinAdditiveEvenRechartRaw_neg
          (coPoissonQuarterMellinConvergentMap
            z positiveZ belowHalf source.1) t).symm
      _ = burnolCompactAdditiveCoSum source (-t) :=
        compactQuarterRechartRaw_eq_coSum_of_pos
          z positiveZ belowHalf source (neg_pos.mpr negative)
      _ = burnolCompactAdditiveCoSum source t :=
        burnolCompactAdditiveCoSum_even source t

theorem compactQuarterMellinAdditiveEvenRechart_eq
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (source : burnolCompactAnnulusSource) :
    quarterMellinAdditiveEvenRechart
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf source.1) =
      burnolCompactAdditiveL2 source := by
  apply Lp.ext
  filter_upwards [quarterMellinAdditiveEvenRechart_coeFn
      (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf source.1),
    burnolCompactAdditiveL2_coeFn source,
    volume.ae_ne (0 : ℝ)] with t left right nonzero
  rw [left, right]
  exact compactQuarterRechartRaw_eq_coSum_away_zero
    z positiveZ belowHalf source nonzero

theorem compactQuarterMellinAdditiveProjectedPhysicalState_eq
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (source : burnolCompactAnnulusSource) :
    quarterMellinAdditiveProjectedPhysicalState
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf source.1) =
      burnolCompactAdditivePhysicalState source := by
  unfold quarterMellinAdditiveProjectedPhysicalState
    burnolEvenAmbientProjection
  rw [compactQuarterMellinAdditiveEvenRechart_eq]
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
    |>.orthogonalProjectionOnto_mem_subspace_eq_self
      (burnolCompactAdditivePhysicalState source)

theorem compactQuarterMellinAdditiveProjectedPhysicalState_mem_closedRange
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (source : burnolCompactAnnulusSource) :
    quarterMellinAdditiveProjectedPhysicalState
        (coPoissonQuarterMellinConvergentMap z positiveZ belowHalf source.1) ∈
      burnolCompactCoPoissonClosedRange := by
  rw [compactQuarterMellinAdditiveProjectedPhysicalState_eq]
  simpa [burnolCompactCoPoissonGenerator] using
    burnolCompactCoPoissonGenerator_mem_closedRange
      (source, (0 : Fin 2))

theorem compactQuarterMellinAdditiveProjectedPhysicalState_evaluator_eq_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (source : burnolCompactAnnulusSource) :
    burnolCompletedMellinEvaluator coordinate
        (quarterMellinAdditiveProjectedPhysicalState
          (coPoissonQuarterMellinConvergentMap
            (coordinate.value / 2)
            (by
              rw [Complex.div_re]
              norm_num
              linarith [coordinate.rightHalf])
            (by
              rw [Complex.div_re]
              norm_num
              linarith [coordinate.belowOne])
            source.1)) = 0 := by
  rw [compactQuarterMellinAdditiveProjectedPhysicalState_eq]
  exact burnolCompletedMellinEvaluator_compactAdditivePhysicalState_eq_zero
    source coordinate zero

theorem compactQuarterMellinAdditiveEvenRechart_riesz_inner_eq_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (source : burnolCompactAnnulusSource) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
        (quarterMellinAdditiveEvenRechart
          (coPoissonQuarterMellinConvergentMap
            (coordinate.value / 2)
            (by
              rw [Complex.div_re]
              norm_num
              linarith [coordinate.rightHalf])
            (by
              rw [Complex.div_re]
              norm_num
              linarith [coordinate.belowOne])
            source.1)) = 0 := by
  rw [← quarterMellinAdditiveProjectedPhysicalState_evaluator_eq_inner]
  exact compactQuarterMellinAdditiveProjectedPhysicalState_evaluator_eq_zero
    coordinate zero source

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

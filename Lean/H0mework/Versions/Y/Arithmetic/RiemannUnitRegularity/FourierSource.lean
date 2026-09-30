import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.UnitResponseOccupation

/-! The original unit source and its Tate sibling retain a nonzero inner
power germ after every original finite Pa source replay. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolUnitFourierSourceDefect_even (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolPaAmbientCarrier) :
    reflectL2 (burnolNormalizedFirstSourceUnitTail coordinate +
      burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate) -
        burnolMobiusSourceL2 value) =
      burnolNormalizedFirstSourceUnitTail coordinate +
        burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate) -
          burnolMobiusSourceL2 value := by
  rw [map_sub, map_add, burnolOriginalUnitTail_even,
    ← burnolTateReciprocal_reflect, burnolOriginalUnitTail_even,
    burnolMobiusSourceL2_even]

theorem burnolUnitFourierSourceDefect_innerPower (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolPaAmbientCarrier) :
    ((burnolNormalizedFirstSourceUnitTail coordinate +
      burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate) -
        burnolMobiusSourceL2 value : BurnolL2) : ℝ → ℂ) =ᵐ[
          volume.restrict (symmetricInterval (1 / 4 : ℝ))]
      fun x => (-1 : ℂ) * (((|x| : ℝ) : ℂ) ^ (coordinate.value - 1)) := by
  let tau := burnolNormalizedFirstSourceUnitTail coordinate
  filter_upwards [
    ae_restrict_of_ae (Lp.coeFn_sub (tau + burnolTateReciprocalL2 tau) (burnolMobiusSourceL2 value)),
    ae_restrict_of_ae (Lp.coeFn_add tau (burnolTateReciprocalL2 tau)),
    burnolOriginalUnitTail_window_zero coordinate (1 / 4) (by norm_num),
    ae_restrict_of_ae (burnolNormalizedFirstSourceUnitTail_tate_coeFn coordinate),
    burnolMobiusSourceL2_innerGap value,
    ae_restrict_mem (measurableSet_symmetricInterval (1 / 4 : ℝ)),
    ae_restrict_of_ae (volume.ae_ne (1 / 4 : ℝ)),
    ae_restrict_of_ae (volume.ae_ne (-(1 / 4 : ℝ)))]
      with x difference sum tail tate finite inside notRight notLeft
  change (tau + burnolTateReciprocalL2 tau - burnolMobiusSourceL2 value : BurnolL2) x = _
  rw [difference]
  change (tau + burnolTateReciprocalL2 tau : BurnolL2) x - burnolMobiusSourceL2 value x = _
  rw [sum]
  change tau x + burnolTateReciprocalL2 tau x - burnolMobiusSourceL2 value x = _
  rw [tail, tate, finite]
  have strict : |x| < (1 / 4 : ℝ) := by
    apply abs_lt.mpr
    exact ⟨lt_of_le_of_ne inside.1 notLeft.symm, lt_of_le_of_ne inside.2 notRight⟩
  simp only [strict, if_true, zero_add, sub_zero, neg_one_mul]

theorem burnolUnitFourierSourceDefect_nonzero (coordinate : BurnolCompletedMellinCoordinate)
    (value : BurnolPaAmbientCarrier) :
    burnolNormalizedFirstSourceUnitTail coordinate +
      burnolTateReciprocalL2 (burnolNormalizedFirstSourceUnitTail coordinate) -
        burnolMobiusSourceL2 value ≠ 0 := by
  intro zero
  have germ := burnolUnitFourierSourceDefect_innerPower coordinate value
  rw [zero] at germ
  have impossible : ∀ᵐ x : ℝ ∂volume.restrict (symmetricInterval (1 / 4 : ℝ)), False := by
    filter_upwards [germ, ae_restrict_of_ae (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)),
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with x hx hz nonzero
    rw [hz] at hx
    apply (mul_ne_zero (by norm_num : (-1 : ℂ) ≠ 0)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (abs_pos.mpr nonzero).ne'))))
    exact hx.symm
  have measureZero : (volume.restrict (symmetricInterval (1 / 4 : ℝ))) univ = 0 := by
    simpa only [ae_iff, not_false_eq_true, ofPred_true] using impossible
  norm_num [symmetricInterval] at measureZero

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

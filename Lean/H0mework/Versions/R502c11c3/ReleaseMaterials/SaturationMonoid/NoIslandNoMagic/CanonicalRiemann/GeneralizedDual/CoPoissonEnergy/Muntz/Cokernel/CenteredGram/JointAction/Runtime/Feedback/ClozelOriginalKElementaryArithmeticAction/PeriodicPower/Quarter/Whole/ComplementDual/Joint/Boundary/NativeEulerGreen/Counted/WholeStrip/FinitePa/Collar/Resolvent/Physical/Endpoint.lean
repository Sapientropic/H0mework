import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

open private moment power_covector_raw star_real_power from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private actual_direct_R_positive_kernel from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource

local notation "q" => (1/4 : ℝ)
local notation "E" => burnolQuarterZeroExtension
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R₀" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "box" => symmetricInterval q
local notation "weight" => fun (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (x : ℝ) =>
  ((|x| : ℝ) : ℂ)^(star (BurnolCompletedMellinCoordinate.value c)-1) * v x

private theorem quarter_weighted_read (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    (fun x : ℝ => inner ℂ (E (SingularCounting.powerL2 (barC c)) x) (v x)) =ᵐ[volume]
      (box).indicator (weight c v) := by
  filter_upwards [power_covector_raw c, volume.ae_ne (0 : ℝ)] with x raw live
  rw [RCLike.inner_apply, starRingEnd_apply, raw]
  by_cases inside : |x| ≤ q
  · have member : x ∈ box := abs_le.mp inside
    rw [if_pos inside, indicator_of_mem member, star_real_power |x| (abs_pos.mpr live),
      star_sub, star_one]
    exact mul_comm _ _
  · have outside : x ∉ box := fun h => inside (abs_le.mpr h)
    rw [if_neg inside, star_zero, mul_zero, indicator_of_notMem outside]

private theorem quarter_weighted_domain (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    IntegrableOn (weight c v) box := by
  exact (integrable_indicator_iff (measurableSet_symmetricInterval q)).mp
    ((L2.integrable_inner (𝕜 := ℂ) (E (SingularCounting.powerL2 (barC c))) v).congr
      (quarter_weighted_read c v))

private theorem quarter_positive_domain (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ)^(star c.value-1) * v x) volume 0 q := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ q)).mpr
  have insideBox : Ioc 0 q ⊆ box := by
    intro x inside
    exact ⟨by linarith [inside.1], inside.2⟩
  apply ((quarter_weighted_domain c v).mono_set insideBox).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x inside
  simp only [abs_of_pos (show 0 < x from inside.1)]

private theorem quarter_even_integral (f : ℝ → ℂ) (integrable : IntegrableOn f box)
    (even : ∀ᵐ x ∂volume, f (-x) = f x) :
    (∫ x in box, f x) = 2*(∫ x : ℝ in 0..q, f x) := by
  have full : IntervalIntegrable f volume (-q) q :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-q : ℝ) ≤ q)).mpr integrable
  have left : IntervalIntegrable f volume (-q) 0 := by
    apply full.mono_set
    rw [uIcc_of_le (by norm_num : (-q : ℝ) ≤ 0), uIcc_of_le (by norm_num : (-q : ℝ) ≤ q)]
    exact Icc_subset_Icc_right (by norm_num)
  have right : IntervalIntegrable f volume 0 q := by
    apply full.mono_set
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ q), uIcc_of_le (by norm_num : (-q : ℝ) ≤ q)]
    exact Icc_subset_Icc_left (by norm_num)
  have negative : (∫ x in (-q)..(0 : ℝ), f x) = ∫ x : ℝ in 0..q, f x := by
    have moved := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := q)
    rw [neg_zero] at moved
    rw [← moved]
    apply intervalIntegral.integral_congr_ae
    exact even.mono fun _ same _ => same
  change (∫ x in Icc (-q) q, f x) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-q : ℝ) ≤ q),
    ← intervalIntegral.integral_add_adjacent_intervals left right, negative, two_mul]

private theorem quarter_positive_price (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) :
    moment c v = 2*(∫ x : ℝ in 0..q, (x : ℂ)^(star c.value-1)*v x) := by
  let w := weight c v
  have reflection := Lp.coeFn_compMeasurePreserving v negMeasurePreserving
  change (reflectL2 v : ℝ → ℂ) =ᵐ[volume] fun x => v (-x) at reflection
  rw [even] at reflection
  have same : ∀ᵐ x ∂volume, w (-x) = w x := by
    filter_upwards [reflection] with x reflected
    simp only [w, abs_neg, ← reflected]
  have positive : (∫ x : ℝ in 0..q, w x) =
      ∫ x : ℝ in 0..q, (x : ℂ)^(star c.value-1)*v x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x inside
    have hx : 0 < x := ((uIoc_of_le (by norm_num : (0 : ℝ) ≤ q)) ▸ inside).1
    simp only [w, abs_of_pos hx]
  change inner ℂ (E (SingularCounting.powerL2 (barC c))) v = _
  rw [L2.inner_def, integral_congr_ae (quarter_weighted_read c v),
    integral_indicator (measurableSet_symmetricInterval q),
    quarter_even_integral w (quarter_weighted_domain c v) same, positive]

/-- The inward R action on the actual quarter is determined by its own outer coefficient and the remaining source. -/
theorem actual_quarter_endpoint_action (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (even : reflectL2 v = v) :
    ∀ᵐ x : ℝ ∂volume, 0 < x → x ≤ q →
      R₀ c v x = (x : ℂ)^(-star c.value) *
        (-moment c v + 2*(∫ y : ℝ in x..q, (y : ℂ)^(star c.value-1)*v y)) := by
  let f := fun y : ℝ => (y : ℂ)^(star c.value-1)*v y
  have domain := quarter_positive_domain c v
  have original := actual_direct_R_positive_kernel (barC c) v (v : ℝ → ℂ) (EventuallyEq.rfl)
  filter_upwards [original] with x read positive bounded
  have left : IntervalIntegrable f volume 0 x := by
    apply domain.mono_set
    rw [uIcc_of_le positive.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)]
    exact Icc_subset_Icc_right bounded
  have right : IntervalIntegrable f volume x q := by
    apply domain.mono_set
    rw [uIcc_of_le bounded, uIcc_of_le (by norm_num : (0 : ℝ) ≤ q)]
    exact Icc_subset_Icc_left positive.le
  have split := intervalIntegral.integral_add_adjacent_intervals left right
  have atPoint := read positive
  change R₀ c v x = -2*(x : ℂ)^(-star c.value)*(∫ y : ℝ in 0..x, f y) at atPoint
  rw [atPoint, quarter_positive_price c v even, ← split]
  ring

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

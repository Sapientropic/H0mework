import H0mework.Versions.Y.Arithmetic.RiemannNativeCurrent.FirstUnitPairing
import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.Weighted

/-! The actual first Tate–Volterra coefficient and its source-generated derivative on the reciprocal annulus. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section

def burnolFirstSourceDensity (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (u : ℝ) : ℂ :=
  ((max (1 / 8 : ℝ) u : ℝ) : ℂ) ^ (-coordinate.value) * ((2 : ℂ) * source.1 u)

theorem burnolFirstSourceDensity_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) : Continuous (burnolFirstSourceDensity coordinate source) := by
  have base : Continuous (fun u : ℝ => ((max (1 / 8 : ℝ) u : ℝ) : ℂ)) := by fun_prop
  have powered : Continuous (fun u : ℝ => ((max (1 / 8 : ℝ) u : ℝ) : ℂ) ^ (-coordinate.value)) :=
    continuousOn_univ.mp (base.continuousOn.cpow_const (fun u _ =>
      Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))))
  exact powered.mul (source.1.continuous.const_mul (2 : ℂ))

def burnolFirstSourceCoefficient (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  -(2 : ℂ) * ((max (1 / 8 : ℝ) t : ℝ) : ℂ) ^ (coordinate.value - 1) *
    ∫ u : ℝ in t..4, burnolFirstSourceDensity coordinate source u

def burnolFirstSourceCoefficientSlope (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) (t : ℝ) : ℂ :=
  -(2 : ℂ) * ((coordinate.value - 1) * ((max (1 / 8 : ℝ) t : ℝ) : ℂ) ^ (coordinate.value - 2) *
    (∫ u : ℝ in t..4, burnolFirstSourceDensity coordinate source u) -
      ((max (1 / 8 : ℝ) t : ℝ) : ℂ) ^ (coordinate.value - 1) * burnolFirstSourceDensity coordinate source t)

theorem burnolFirstSourceIntegral_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    Continuous (fun t : ℝ => ∫ u : ℝ in t..4, burnolFirstSourceDensity coordinate source u) := by
  have primitive := intervalIntegral.continuous_primitive (μ := (volume : Measure ℝ))
    (fun a b => (burnolFirstSourceDensity_continuous coordinate source).intervalIntegrable a b) (4 : ℝ)
  have orientation : (fun t : ℝ => ∫ u : ℝ in t..4, burnolFirstSourceDensity coordinate source u) =
      fun t : ℝ => -(∫ u : ℝ in 4..t, burnolFirstSourceDensity coordinate source u) := by
    funext t
    exact intervalIntegral.integral_symm (f := burnolFirstSourceDensity coordinate source)
      (a := (4 : ℝ)) (b := t) (μ := volume)
  rw [orientation]
  exact primitive.neg

theorem burnolFirstSourceCoefficient_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) : Continuous (burnolFirstSourceCoefficient coordinate source) := by
  have base : Continuous (fun t : ℝ => ((max (1 / 8 : ℝ) t : ℝ) : ℂ)) := by fun_prop
  have powered : Continuous (fun t : ℝ => ((max (1 / 8 : ℝ) t : ℝ) : ℂ) ^ (coordinate.value - 1)) :=
    continuousOn_univ.mp (base.continuousOn.cpow_const
    (fun t _ => Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))))
  exact (powered.const_mul (-(2 : ℂ))).mul (burnolFirstSourceIntegral_continuous coordinate source)

theorem burnolFirstSourceCoefficientSlope_continuous (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) : Continuous (burnolFirstSourceCoefficientSlope coordinate source) := by
  have power (exponent : ℂ) : Continuous (fun t : ℝ => ((max (1 / 8 : ℝ) t : ℝ) : ℂ) ^ exponent) := by
    have base : Continuous (fun t : ℝ => ((max (1 / 8 : ℝ) t : ℝ) : ℂ)) := by fun_prop
    exact continuousOn_univ.mp (base.continuousOn.cpow_const (fun t _ =>
      Complex.ofReal_mem_slitPlane.mpr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))))
  exact continuous_const.mul (((continuous_const.mul (power _)).mul
    (burnolFirstSourceIntegral_continuous coordinate source)).sub
      ((power _).mul (burnolFirstSourceDensity_continuous coordinate source)))

theorem burnolFirstSourceCoefficient_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    HasDerivAt (burnolFirstSourceCoefficient coordinate source) (burnolFirstSourceCoefficientSlope coordinate source t) t := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  have exponentNonzero : coordinate.value - 1 ≠ 0 := by
    intro zero
    have same := sub_eq_zero.mp zero
    have bound := coordinate.belowOne
    rw [same] at bound
    norm_num at bound
  have power := hasDerivAt_ofReal_cpow_const positive.ne' exponentNonzero
  have density := burnolFirstSourceDensity_continuous coordinate source
  have integralDerivative := intervalIntegral.integral_hasDerivAt_left
    (density.intervalIntegrable t 4) density.stronglyMeasurable.stronglyMeasurableAtFilter density.continuousAt
  have product := ((power.const_mul (-(2 : ℂ))).mul integralDerivative)
  have localized := product.congr_of_eventuallyEq (show burnolFirstSourceCoefficient coordinate source =ᶠ[𝓝 t]
      (fun u => -(2 : ℂ) * (u : ℂ) ^ (coordinate.value - 1) * ∫ v in u..4, burnolFirstSourceDensity coordinate source v) from by
    filter_upwards [eventually_gt_nhds (show (1 / 8 : ℝ) < t by linarith [inside.1])] with u hu
    simp only [burnolFirstSourceCoefficient, max_eq_right hu.le])
  unfold burnolFirstSourceCoefficientSlope
  rw [max_eq_right (show (1 / 8 : ℝ) ≤ t by linarith [inside.1])]
  convert! localized using 1
  rw [show coordinate.value - 2 = coordinate.value - 1 - 1 by ring]
  ring

theorem burnolFirstSourceCoefficient_raw (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) {t : ℝ} (inside : t ∈ Icc (1 / 4 : ℝ) 4) :
    burnolFirstSourceCoefficient coordinate source t =
      burnolFourierRightDivisionRaw (coordinate.value / 2) (fun u => (2 : ℂ) * source.1 u) t := by
  have positive : 0 < t := lt_of_lt_of_le (by norm_num) inside.1
  rw [burnolFourierRightDivisionRaw_eq_tail _ _ positive,
    show 2 * (coordinate.value / 2) - 1 = coordinate.value - 1 by ring,
    show -2 * (coordinate.value / 2) = -coordinate.value by ring]
  unfold burnolFirstSourceCoefficient
  rw [max_eq_right (show (1 / 8 : ℝ) ≤ t by linarith [inside.1])]
  congr 1
  rw [intervalIntegral.integral_of_le inside.2,
    ← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with u
  by_cases later : t < u
  · by_cases bounded : u ≤ 4
    · rw [indicator_of_mem (show u ∈ Ioc t 4 from ⟨later, bounded⟩),
        indicator_of_mem (show u ∈ Ioi t from later)]
      dsimp only [burnolFirstSourceDensity]
      rw [max_eq_right (show (1 / 8 : ℝ) ≤ u by linarith [inside.1])]
    · rw [indicator_of_notMem (show u ∉ Ioc t 4 from fun hu => bounded hu.2),
        indicator_of_mem (show u ∈ Ioi t from later)]
      rw [source.2.2.2 u (by rw [abs_of_pos (positive.trans later)]; linarith), mul_zero, mul_zero]
  · rw [indicator_of_notMem (show u ∉ Ioc t 4 from fun hu => later hu.1),
      indicator_of_notMem (show u ∉ Ioi t from later)]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

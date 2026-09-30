import H0mework.Versions.X.NavierStokes.HigherTreeOctic.ForcingGate

set_option autoImplicit false
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
noncomputable section

private theorem finite_l1_response {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (path force : ℝ → E) (first last : ℝ) (ordered : first ≤ last)
    (pathContinuous : ContinuousOn path (Icc first last))
    (forceIntegrable : IntervalIntegrable force volume first last)
    (powerIntegrable : ∀ time ∈ Icc first last,
      IntervalIntegrable (fun sample => 2 * inner ℝ (path sample) (force sample)) volume first time)
    (energy : ∀ time ∈ Icc first last,
      ‖path time‖^2 ≤ ‖path first‖^2 +
        ∫ sample in first..time, 2 * inner ℝ (path sample) (force sample)) :
    ‖path last‖ ≤ ‖path first‖ + 2 * ∫ sample in first..last, ‖force sample‖ := by
  obtain ⟨peak, peakIn, peakMax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr ordered) pathContinuous.norm
  let magnitude := ‖path peak‖
  have firstIn : first ∈ Icc first last := ⟨le_rfl, ordered⟩
  have lastIn : last ∈ Icc first last := ⟨ordered, le_rfl⟩
  have firstLe : ‖path first‖ ≤ magnitude := peakMax firstIn
  have lastLe : ‖path last‖ ≤ magnitude := peakMax lastIn
  have magnitude0 : 0 ≤ magnitude := norm_nonneg _
  have normIntegrable : IntervalIntegrable (fun sample => ‖force sample‖) volume first last := forceIntegrable.norm
  have budget0 : 0 ≤ ∫ sample in first..last, ‖force sample‖ :=
    intervalIntegral.integral_nonneg ordered (fun _ _ => norm_nonneg _)
  have pointwise (sample : ℝ) (inside : sample ∈ Icc first peak) :
      2 * inner ℝ (path sample) (force sample) ≤
        2 * magnitude * ‖force sample‖ := by
    have sampleIn : sample ∈ Icc first last := ⟨inside.1, inside.2.trans peakIn.2⟩
    have innerBound : inner ℝ (path sample) (force sample) ≤ ‖path sample‖ * ‖force sample‖ :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (path sample) (force sample)))
    nlinarith [mul_le_mul_of_nonneg_right (peakMax sampleIn) (norm_nonneg (force sample))]
  have localForce : IntervalIntegrable (fun sample => ‖force sample‖) volume first peak :=
    (forceIntegrable.mono_set' (by
      simpa only [uIoc_of_le ordered, uIoc_of_le peakIn.1] using
        (Ioc_subset_Ioc le_rfl peakIn.2))).norm
  have powerBound := intervalIntegral.integral_mono_on peakIn.1
    (powerIntegrable peak peakIn) (localForce.const_mul (2 * magnitude)) pointwise
  simp only [intervalIntegral.integral_const_mul] at powerBound
  have normBound := intervalIntegral.integral_mono_interval
    (c := first) (d := last) le_rfl peakIn.1 peakIn.2
    (Filter.Eventually.of_forall (fun sample => norm_nonneg (force sample))) normIntegrable
  have peakEnergy := energy peak peakIn
  simp only [intervalIntegral.integral_const_mul] at peakEnergy
  have peakBudget : magnitude^2 ≤ ‖path first‖^2 +
      2 * magnitude * ∫ sample in first..last, ‖force sample‖ := by
    nlinarith [mul_le_mul_of_nonneg_left normBound (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) magnitude0)]
  have magnitudeLe : magnitude ≤ ‖path first‖ + 2 * ∫ sample in first..last, ‖force sample‖ := by
    by_contra contrary
    have strict : ‖path first‖ + 2 * ∫ sample in first..last, ‖force sample‖ < magnitude := lt_of_not_ge contrary
    have positive : 0 < magnitude - ‖path first‖ - 2 * ∫ sample in first..last, ‖force sample‖ := by linarith
    have factor := mul_pos positive (by linarith [norm_nonneg (path first)] : 0 < magnitude)
    have other := mul_nonneg (norm_nonneg (path first)) (sub_nonneg.mpr firstLe)
    nlinarith
  exact lastLe.trans magnitudeLe

variable {nu : Viscosity}
variable (slot : Fin 3) (leaf : Fin 4) (position : Fin 5) (newest : Fin 6)
  (i j response outside l m p q r s u v : Coordinate) (selected : Fin 7) (a b : Coordinate)

theorem vector_l1_bound (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) (ordered : first ≤ last) :
    ‖vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last‖ ≤
      ‖vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first‖ +
      2 * ∫ time in first..last,
        ‖forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖ := by
  let path := vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed
  let force := forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed
  have pathContinuous : ContinuousOn path (Icc first last) := by
    have paid := (vector_ac (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b
      test seed observed first last first0 last0).continuousOn
    rwa [uIcc_of_le ordered] at paid
  have forceIntegrable : IntervalIntegrable force volume first last :=
    forcingVector_integrable (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b
      test seed observed first last first0 last0
  have powerIntegrable (time : ℝ) (inside : time ∈ Icc first last) :
      IntervalIntegrable (fun sample => 2 * inner ℝ (path sample) (force sample)) volume first time :=
    forcingPower_integrable (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b
      test seed observed first time first0 (first0.trans inside.1) inside.1
  have energy (time : ℝ) (inside : time ∈ Icc first last) :
      ‖path time‖^2 ≤ ‖path first‖^2 +
        ∫ sample in first..time, 2 * inner ℝ (path sample) (force sample) := by
    simpa only [path, force, work] using
      work_forcing_gate (nu := nu) slot leaf position newest i j response outside l m p q r s u v selected a b
        test seed observed first time first0 (first0.trans inside.1) inside.1
  exact finite_l1_response path force first last ordered pathContinuous forceIntegrable powerIntegrable energy

theorem pairing_l1_bound (test : Test) (seed : GeneratedWholeRestartCurrent nu)
    (observed : Finset Address) (first last : ℝ)
    (first0 : 0 ≤ first) (last0 : 0 ≤ last) (ordered : first ≤ last) :
    ‖original slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last -
      bare slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last‖^2 ≤
      NativeUnifiedCompleteSource.budget seed^2 *
        (‖vector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed first‖ +
          2 * ∫ time in first..last,
            ‖forcingVector slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed time‖)^2 := by
  have paid := pairing_bound slot leaf position newest i j response outside l m p q r s u v selected a b test seed observed last
  rw [work] at paid
  have growth := vector_l1_bound slot leaf position newest i j response outside l m p q r s u v selected a b
    test seed observed first last first0 last0 ordered
  exact paid.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) growth 2) (sq_nonneg _))

end
end SaturationMonoid.NavierStokes.NativeUnheatedOcticGramDual

import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ReciprocalTail
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.RegularQuadrature

open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszSourceGreen
noncomputable section
local notation "q" => (1 / 4 : ℝ)

def forcingSlope (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) : ℂ :=
  ((star coordinate.value - 1) * ForcingTail.forcingRemainder coordinate x +
    ForcingWhole.coefficient coordinate * Edge.raw q x) / (x : ℂ)

def forcingSlopeBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  4 * ‖ForcingWhole.coefficient coordinate‖ * (‖star coordinate.value - 1‖ + 1) * q

private theorem forcing_positive_read (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    ForcingWhole.raw coordinate x = ForcingPrimitive.leadingCoefficient coordinate *
      (x : ℂ) ^ (star coordinate.value - 1) + ForcingTail.forcingRemainder coordinate x := by
  rw [ForcingPrimitive.forcing_read coordinate x positive]
  simp only [ForcingTail.forcingRemainder, ForcingTail.edgeRemainder, abs_of_pos positive]
  ring

theorem forcing_positive_derivative (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    HasDerivAt (ForcingTail.forcingRemainder coordinate) (forcingSlope coordinate x) x := by
  have power := (Complex.hasStrictDerivAt_cpow_const
    (c := star coordinate.value - 1) (Complex.ofReal_mem_slitPlane.mpr positive)).hasDerivAt.comp_ofReal
  have generated := (forcing_raw_hasDerivAt coordinate x positive.ne').sub
    (power.const_mul (ForcingPrimitive.leadingCoefficient coordinate))
  have same : ForcingTail.forcingRemainder coordinate =ᶠ[𝓝 x]
      fun y => ForcingWhole.raw coordinate y - ForcingPrimitive.leadingCoefficient coordinate *
        (y : ℂ) ^ (star coordinate.value - 1) := by
    filter_upwards [Ioi_mem_nhds positive] with y positiveY
    rw [forcing_positive_read coordinate y positiveY]
    ring
  have slope : (((star coordinate.value - 1) * ForcingWhole.raw coordinate x +
      ForcingWhole.coefficient coordinate * Edge.raw q x) / (x : ℂ) -
      ForcingPrimitive.leadingCoefficient coordinate * ((star coordinate.value - 1) *
        (x : ℂ) ^ (star coordinate.value - 1 - 1))) = forcingSlope coordinate x := by
    rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr positive.ne'), cpow_one,
      forcing_positive_read coordinate x positive]
    unfold forcingSlope
    field_simp
    ring
  rw [slope] at generated
  exact generated.congr_of_eventuallyEq same

theorem forcing_zero (coordinate : BurnolCompletedMellinCoordinate) :
    ForcingTail.forcingRemainder coordinate 0 = 0 := by
  simp [ForcingTail.forcingRemainder, ForcingTail.edgeRemainder, ForcingPrimitive.edgePrimitive]

theorem forcing_zero_derivative (coordinate : BurnolCompletedMellinCoordinate) :
    HasDerivAt (ForcingTail.forcingRemainder coordinate) 0 0 := by
  rw [hasDerivAt_iff_tendsto]
  simp only [forcing_zero, sub_zero, smul_zero]
  have upper : Tendsto (fun x : ℝ => 4 * ‖ForcingWhole.coefficient coordinate‖ * |x|) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (4 * ‖ForcingWhole.coefficient coordinate‖)
  apply squeeze_zero' (Eventually.of_forall (fun x => mul_nonneg (inv_nonneg.mpr (norm_nonneg x)) (norm_nonneg _))) _ upper
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < q)] with x close
  have small : |x| ≤ q := (show |x| < q by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using close).le
  have source := ForcingTail.forcingRemainder_bound coordinate small
  rw [Real.norm_eq_abs]
  by_cases zero : x = 0
  · simp [zero]
  · exact (mul_le_mul_of_nonneg_left source (inv_nonneg.mpr (abs_nonneg x))).trans_eq
      (by rw [← sq_abs]; field_simp)

theorem forcing_derivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (nonnegative : 0 ≤ x) :
    HasDerivAt (ForcingTail.forcingRemainder coordinate) (forcingSlope coordinate x) x := by
  rcases nonnegative.eq_or_lt with zero | positive
  · subst x
    simpa only [forcingSlope, ofReal_zero, div_zero] using forcing_zero_derivative coordinate
  · exact forcing_positive_derivative coordinate x positive

theorem forcing_slope_linear_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (inside : x ∈ Icc 0 q) : ‖forcingSlope coordinate x‖ ≤
      (4 * ‖ForcingWhole.coefficient coordinate‖ * (‖star coordinate.value - 1‖ + 1)) * x := by
  have constantNonnegative : 0 ≤ 4 * ‖ForcingWhole.coefficient coordinate‖ * (‖star coordinate.value - 1‖ + 1) := by positivity
  by_cases zero : x = 0
  · subst x
    simp only [forcingSlope, ofReal_zero, div_zero, norm_zero, mul_zero, le_refl]
  have positive : 0 < x := lt_of_le_of_ne inside.1 (Ne.symm zero)
  have small : |x| ≤ q := by rw [abs_of_pos positive]; exact inside.2
  have raw := ForcingTail.forcingRemainder_bound coordinate small
  have edge := ForcingTail.edge_quadratic_bound small
  unfold forcingSlope
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  calc
    _ ≤ (‖star coordinate.value - 1‖ * (4 * ‖ForcingWhole.coefficient coordinate‖ * x ^ 2) +
        ‖ForcingWhole.coefficient coordinate‖ * (4 * x ^ 2)) / x := by
      apply div_le_div_of_nonneg_right _ positive.le
      exact (norm_add_le _ _).trans (by simp only [norm_mul]; gcongr)
    _ = (4 * ‖ForcingWhole.coefficient coordinate‖ * (‖star coordinate.value - 1‖ + 1)) * x := by
      field_simp

theorem forcing_slope_bound (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ)
    (inside : x ∈ Icc 0 q) : ‖forcingSlope coordinate x‖ ≤ forcingSlopeBound coordinate :=
  (forcing_slope_linear_bound coordinate x inside).trans
    (mul_le_mul_of_nonneg_left inside.2 (by positivity))

theorem forcing_slope_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (forcingSlope coordinate) (Icc 0 q) := by
  intro x inside
  by_cases zero : x = 0
  · subst x
    change Tendsto (forcingSlope coordinate) (𝓝[Icc 0 q] 0) (𝓝 (forcingSlope coordinate 0))
    rw [show forcingSlope coordinate 0 = 0 by simp [forcingSlope], tendsto_zero_iff_norm_tendsto_zero]
    have upper : Tendsto (fun t : ℝ =>
        (4 * ‖ForcingWhole.coefficient coordinate‖ * (‖star coordinate.value - 1‖ + 1)) * t)
        (𝓝[Icc 0 q] 0) (𝓝 0) := by
      simpa using ((continuous_id.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_mul
        (4 * ‖ForcingWhole.coefficient coordinate‖ * (‖star coordinate.value - 1‖ + 1))
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ upper
    filter_upwards [self_mem_nhdsWithin] with t located
    exact forcing_slope_linear_bound coordinate t located
  · exact ((((continuousAt_const.mul (forcing_derivative coordinate x inside.1).continuousAt).add
      (continuousAt_const.mul (Edge.raw_continuous q).continuousAt)).div
        Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr zero))).continuousWithinAt

theorem forcing_derivative_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (forcingSlope coordinate) (Icc 0 q) :=
  (forcing_slope_continuous coordinate).integrableOn_Icc

theorem return_derivative_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (Constructor.fourierDerivative (burnolRieszReturnRaw coordinate)) (Icc 0 q) :=
  (Constructor.fourierDerivative_continuous _ (burnolRieszReturnRaw_continuous coordinate)).integrableOn_Icc

theorem forcing_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    ContinuousOn (ForcingTail.forcingRemainder coordinate) (Icc 0 q) := by
  intro x inside
  exact (forcing_derivative coordinate x inside.1).continuousAt.continuousWithinAt

theorem forcing_lipschitz (coordinate : BurnolCompletedMellinCoordinate) (x y : ℝ)
    (hx : x ∈ Icc 0 q) (hy : y ∈ Icc 0 q) :
    ‖ForcingTail.forcingRemainder coordinate y - ForcingTail.forcingRemainder coordinate x‖ ≤
      forcingSlopeBound coordinate * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t inside => (forcing_derivative coordinate t inside.1).hasDerivWithinAt)
    (fun t inside => forcing_slope_bound coordinate t inside) (convex_Icc _ _) hx hy

theorem return_lipschitz (coordinate : BurnolCompletedMellinCoordinate) (x y : ℝ)
    (hx : x ∈ Icc 0 q) (hy : y ∈ Icc 0 q) :
    ‖InverseTail.smoothFourier coordinate y - InverseTail.smoothFourier coordinate x‖ ≤
      (2 * InverseTail.returnMass coordinate) * ‖y - x‖ :=
  Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (Constructor.fourierRaw_hasDerivAt _ (burnolRieszReturnRaw_continuous coordinate) t).hasDerivWithinAt)
    (fun t _ => ReciprocalTail.smoothDerivative_uniform_bound coordinate t) (convex_Icc _ _) hx hy

private theorem cell_error (f : ℝ → ℂ) (continuous : ContinuousOn f (Icc 0 q))
    (L : ℝ) (nonnegative : 0 ≤ L)
    (lipschitz : ∀ x ∈ Icc 0 q, ∀ y ∈ Icc 0 q, ‖f y - f x‖ ≤ L * ‖y - x‖)
    (a x : ℝ) (positive : 0 < x) (lower : 0 ≤ a) (upper : a + x ≤ q) :
    ‖(x : ℂ) * f (a + x) - ∫ t : ℝ in a..(a + x), f t‖ ≤ L * x ^ 2 := by
  have ordered : a ≤ a + x := by linarith
  have subset : Icc a (a + x) ⊆ Icc 0 q := fun t inside => ⟨lower.trans inside.1, inside.2.trans upper⟩
  have regular : IntervalIntegrable f volume a (a + x) :=
    (continuous.mono subset).intervalIntegrable_of_Icc ordered
  have identity : (x : ℂ) * f (a + x) - ∫ t : ℝ in a..(a + x), f t =
      ∫ t : ℝ in a..(a + x), f (a + x) - f t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const regular, intervalIntegral.integral_const,
      add_sub_cancel_left, Complex.real_smul]
  rw [identity]
  have bound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := a + x) (C := L * x) (f := fun t : ℝ => f (a + x) - f t) (fun t inside => by
      have located : t ∈ Icc a (a + x) := Ioc_subset_Icc_self
        (by simpa only [uIoc_of_le ordered] using inside)
      have actual := lipschitz t (subset located) (a + x) ⟨by linarith, upper⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr located.2)] at actual
      exact actual.trans (mul_le_mul_of_nonneg_left (by linarith [located.1]) nonnegative))
  simpa only [add_sub_cancel_left, abs_of_pos positive, pow_two, mul_assoc] using bound

private theorem complete_grid_error (f : ℝ → ℂ) (continuous : ContinuousOn f (Icc 0 q))
    (L : ℝ) (nonnegative : 0 ≤ L)
    (lipschitz : ∀ x ∈ Icc 0 q, ∀ y ∈ Icc 0 q, ‖f y - f x‖ ≤ L * ‖y - x‖)
    (x : ℝ) (positive : 0 < x) (M : ℕ) (inside : (M : ℝ) * x ≤ q) :
    ‖(x : ℂ) * (∑ n ∈ Finset.range M, f (((n + 1 : ℕ) : ℝ) * x)) -
      ∫ t : ℝ in (0 : ℝ)..((M : ℝ) * x), f t‖ ≤ L * ((M : ℝ) * x) * x := by
  have upper (n : ℕ) (hn : n < M) : (n : ℝ) * x + x ≤ q := by
    have natBound : (n : ℝ) + 1 ≤ M := by exact_mod_cast hn
    nlinarith
  have integrable (n : ℕ) (hn : n < M) :
      IntervalIntegrable f volume ((n : ℝ) * x) (((n + 1 : ℕ) : ℝ) * x) := by
    apply (continuous.mono _).intervalIntegrable_of_Icc (by push_cast; nlinarith)
    intro t ht
    constructor
    · exact (mul_nonneg (Nat.cast_nonneg n) positive.le).trans ht.1
    · exact ht.2.trans (by push_cast; nlinarith [upper n hn])
  have adjacent := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun n : ℕ => (n : ℝ) * x) integrable
  simp only [Nat.cast_zero, zero_mul] at adjacent
  rw [← adjacent, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.range M, ‖(x : ℂ) * f (((n + 1 : ℕ) : ℝ) * x) -
        ∫ t : ℝ in ((n : ℝ) * x)..(((n + 1 : ℕ) : ℝ) * x), f t‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range M, L * x ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have actual := cell_error f continuous L nonnegative lipschitz ((n : ℝ) * x) x positive
        (mul_nonneg (Nat.cast_nonneg n) positive.le) (upper n (Finset.mem_range.mp hn))
      simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using actual
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Right-endpoint quadrature keeps the final incomplete cell, including the one-cell case. -/
theorem quadrature_bound (f : ℝ → ℂ) (continuous : ContinuousOn f (Icc 0 q))
    (L B : ℝ) (nonnegativeL : 0 ≤ L) (nonnegativeB : 0 ≤ B)
    (lipschitz : ∀ x ∈ Icc 0 q, ∀ y ∈ Icc 0 q, ‖f y - f x‖ ≤ L * ‖y - x‖)
    (bounded : ∀ t ∈ Icc 0 q, ‖f t‖ ≤ B) (x : ℝ) (positive : 0 < x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, f ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..q, f t‖ ≤ L * q + B := by
  let M : ℕ := ⌊q / x⌋₊
  have endNonnegative : 0 ≤ (M : ℝ) * x := mul_nonneg (Nat.cast_nonneg M) positive.le
  have endBound : (M : ℝ) * x ≤ q := (le_div_iff₀ positive).mp (Nat.floor_le (by positivity))
  have remainderBound : q - (M : ℝ) * x ≤ x := by
    have next : q / x < (M : ℝ) + 1 := Nat.lt_floor_add_one _
    have scaled := (div_lt_iff₀ positive).mp next
    nlinarith
  have leftIntegral : IntervalIntegrable f volume 0 ((M : ℝ) * x) :=
    (continuous.mono (Icc_subset_Icc le_rfl endBound)).intervalIntegrable_of_Icc endNonnegative
  have rightIntegral : IntervalIntegrable f volume ((M : ℝ) * x) q :=
    (continuous.mono (Icc_subset_Icc endNonnegative le_rfl)).intervalIntegrable_of_Icc endBound
  have split := intervalIntegral.integral_add_adjacent_intervals leftIntegral rightIntegral
  have tail : ‖∫ t : ℝ in ((M : ℝ) * x)..q, f t‖ ≤ B * (q - (M : ℝ) * x) := by
    have actual := intervalIntegral.norm_integral_le_of_norm_le_const (a := (M : ℝ) * x) (b := q)
      (fun t inside => by
        have located : t ∈ Ioc ((M : ℝ) * x) q := by simpa only [uIoc_of_le endBound] using inside
        exact bounded t ⟨endNonnegative.trans located.1.le, located.2⟩)
    simpa only [abs_of_nonneg (sub_nonneg.mpr endBound)] using actual
  have whole : ‖(x : ℂ) * (∑ n ∈ Finset.range M, f (((n + 1 : ℕ) : ℝ) * x)) -
      ∫ t : ℝ in (0 : ℝ)..q, f t‖ ≤ (L * q + B) * x := by
    have decomposed : (x : ℂ) * (∑ n ∈ Finset.range M, f (((n + 1 : ℕ) : ℝ) * x)) -
        ∫ t : ℝ in (0 : ℝ)..q, f t =
      ((x : ℂ) * (∑ n ∈ Finset.range M, f (((n + 1 : ℕ) : ℝ) * x)) -
        ∫ t : ℝ in (0 : ℝ)..((M : ℝ) * x), f t) -
      ∫ t : ℝ in ((M : ℝ) * x)..q, f t := by rw [← split]; ring
    rw [decomposed]
    have firstBound : L * ((M : ℝ) * x) * x ≤ L * q * x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left endBound nonnegativeL) positive.le
    have lastBound : B * (q - (M : ℝ) * x) ≤ B * x :=
      mul_le_mul_of_nonneg_left remainderBound nonnegativeB
    exact (norm_sub_le _ _).trans ((add_le_add
      (complete_grid_error f continuous L nonnegativeL lipschitz x positive M endBound) tail).trans
      ((add_le_add firstBound lastBound).trans_eq (by ring)))
  have indices : (∑ n ∈ Finset.Icc 1 M, f ((n : ℝ) * x)) =
      ∑ n ∈ Finset.range M, f (((n + 1 : ℕ) : ℝ) * x) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  change ‖(∑ n ∈ Finset.Icc 1 M, f ((n : ℝ) * x)) - _‖ ≤ _
  rw [indices]
  have identity : (∑ n ∈ Finset.range M, f (((n + 1 : ℕ) : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..q, f t =
      (x : ℂ)⁻¹ * ((x : ℂ) * (∑ n ∈ Finset.range M, f (((n + 1 : ℕ) : ℝ) * x)) -
        ∫ t : ℝ in (0 : ℝ)..q, f t) := by
    rw [mul_sub, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr positive.ne')]
  rw [identity, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
  exact (mul_le_mul_of_nonneg_left whole (inv_nonneg.mpr positive.le)).trans_eq (by field_simp)

def forcingBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  forcingSlopeBound coordinate * q + 4 * ‖ForcingWhole.coefficient coordinate‖ * q ^ 2

def returnBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  (2 * InverseTail.returnMass coordinate) * q + InverseTail.returnMass coordinate

def sourceBound (coordinate : BurnolCompletedMellinCoordinate) : ℝ :=
  forcingBound coordinate + returnBound coordinate

theorem forcing_quadrature (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, ForcingTail.forcingRemainder coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..q, ForcingTail.forcingRemainder coordinate t‖ ≤ forcingBound coordinate := by
  apply quadrature_bound _ (forcing_continuous coordinate) (forcingSlopeBound coordinate)
    (4 * ‖ForcingWhole.coefficient coordinate‖ * q ^ 2) (by unfold forcingSlopeBound; positivity)
    (by positivity) (fun a ha b hb => forcing_lipschitz coordinate a b ha hb) _ x positive
  intro t inside
  exact (ForcingTail.forcingRemainder_bound coordinate (by rw [abs_of_nonneg inside.1]; exact inside.2)).trans
    (mul_le_mul_of_nonneg_left (by nlinarith [inside.1, inside.2]) (by positivity))

theorem return_quadrature (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊, InverseTail.smoothFourier coordinate ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..q, InverseTail.smoothFourier coordinate t‖ ≤ returnBound coordinate := by
  have mass : 0 ≤ InverseTail.returnMass coordinate := integral_nonneg (fun _ => norm_nonneg _)
  apply quadrature_bound _
    (Constructor.fourierRaw_continuous _ (burnolRieszReturnRaw_continuous coordinate)).continuousOn
    (2 * InverseTail.returnMass coordinate) (InverseTail.returnMass coordinate) (by positivity) mass
    (fun a ha b hb => return_lipschitz coordinate a b ha hb)
    (fun t _ => ReciprocalTail.smoothFourier_uniform_bound coordinate t) x positive

/-- The original two regular terms retain their common grid and their common final cell. -/
theorem original_regular_quadrature (coordinate : BurnolCompletedMellinCoordinate)
    (x : ℝ) (positive : 0 < x) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊q / x⌋₊,
        (ForcingTail.forcingRemainder coordinate ((n : ℝ) * x) + InverseTail.smoothFourier coordinate ((n : ℝ) * x))) -
      (x : ℂ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..q,
        ForcingTail.forcingRemainder coordinate t + InverseTail.smoothFourier coordinate t‖ ≤ sourceBound coordinate := by
  have first : IntervalIntegrable (ForcingTail.forcingRemainder coordinate) volume 0 q :=
    (forcing_continuous coordinate).intervalIntegrable_of_Icc (by norm_num)
  have second : IntervalIntegrable (InverseTail.smoothFourier coordinate) volume 0 q :=
    (Constructor.fourierRaw_continuous _ (burnolRieszReturnRaw_continuous coordinate)).intervalIntegrable _ _
  rw [Finset.sum_add_distrib, intervalIntegral.integral_add first second, mul_add,
    show ∀ a b c d : ℂ, (a + b) - (c + d) = (a - c) + (b - d) by intros; ring]
  exact (norm_add_le _ _).trans (add_le_add (forcing_quadrature coordinate x positive)
    (return_quadrature coordinate x positive))

theorem sourceBound_nonnegative (coordinate : BurnolCompletedMellinCoordinate) :
    0 ≤ sourceBound coordinate := by
  have mass : 0 ≤ InverseTail.returnMass coordinate := integral_nonneg (fun _ => norm_nonneg _)
  unfold sourceBound forcingBound returnBound forcingSlopeBound
  positivity

end
end OriginalRieszFinitePairing.CoPoisson.Ward.RegularQuadrature
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

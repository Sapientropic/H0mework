import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Prolate.Transform
import Mathlib.Analysis.Calculus.Deriv.Shift

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.ProlateCompactTail
open Complex Filter MeasureTheory Set ProlateKernel
open scoped ContDiff Topology
noncomputable section
local notation "q" => (1 / 4 : ℝ)
local notation "μq" => (volume.restrict (symmetricInterval q))

private theorem quarter_integral (f : ℝ → ℂ) :
    (∫ y : ℝ, f y ∂μq) = ∫ y : ℝ in (-q)..q, f y := by
  rw [intervalIntegral.integral_of_le (by norm_num : -q ≤ q), ← integral_Icc_eq_integral_Ioc]
  rfl

private theorem kernel_norm (x y : ℝ) : ‖kernel x y‖ ≤ 1 := by
  have argument : frequency * (x : ℂ) * (y : ℂ) = ((2 * Real.pi * x * y : ℝ) : ℂ) := by
    simp [frequency]
  rw [kernel, argument, ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _

private theorem transform_bound {f : ℝ → ℂ} (regular : Continuous f) (x : ℝ) :
    ‖ProlateTransform.transform f x‖ ≤ ∫ y : ℝ, ‖f y‖ ∂μq := by
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae
  · exact (by unfold kernel; fun_prop : Continuous (fun y : ℝ => kernel x y * f y)).norm.integrableOn_Icc
  · exact regular.norm.integrableOn_Icc
  · filter_upwards with y
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (kernel_norm x y) (norm_nonneg _)).trans_eq (one_mul _)

private theorem two_boundary_identity {f : ℝ → ℂ} (regular : ContDiff ℝ 2 f) (x : ℝ) :
    (frequency * (x : ℂ)) ^ 2 * ProlateTransform.transform f x -
        frequency * (x : ℂ) * Complex.sin (scale * (x : ℂ)) * (f q + f (-q)) =
      Complex.cos (scale * (x : ℂ)) * (deriv f q - deriv f (-q)) -
        ProlateTransform.transform (deriv (deriv f)) x := by
  let a : ℂ := frequency * (x : ℂ)
  let W : ℝ → ℂ := fun y => a * Complex.sin (a * (y : ℂ)) * f y +
    Complex.cos (a * (y : ℂ)) * deriv f y
  have first : ContDiff ℝ 1 (deriv f) := regular.deriv'
  have second : Continuous (deriv (deriv f)) := first.continuous_deriv_one
  have derivative (y : ℝ) : HasDerivAt W
      (a ^ 2 * (kernel x y * f y) + kernel x y * deriv (deriv f) y) y := by
    have raw := (regular.differentiable (by norm_num) y).hasDerivAt
    have rawFirst := (regular.differentiable_deriv_two y).hasDerivAt
    have sine : HasDerivAt (fun y : ℝ => Complex.sin (a * (y : ℂ)))
        (Complex.cos (a * (y : ℂ)) * a) y := by
      simpa only [id_eq, mul_one] using!
        (((Complex.hasDerivAt_sin (a * (y : ℂ))).comp (y : ℂ)
          ((hasDerivAt_id (y : ℂ)).const_mul a))).comp_ofReal
    have cosine : HasDerivAt (fun y : ℝ => Complex.cos (a * (y : ℂ)))
        (-Complex.sin (a * (y : ℂ)) * a) y := by
      simpa only [id_eq, mul_one] using!
        (((Complex.hasDerivAt_cos (a * (y : ℂ))).comp (y : ℂ)
          ((hasDerivAt_id (y : ℂ)).const_mul a))).comp_ofReal
    convert! ((sine.const_mul a).mul raw).add (cosine.mul rawFirst) using 1
    dsimp only [W, a, kernel]
    ring
  have original : Continuous (fun y => kernel x y * f y) := by unfold kernel; fun_prop
  have derived : Continuous (fun y => kernel x y * deriv (deriv f) y) := by unfold kernel; fun_prop
  have complete : IntervalIntegrable (fun y => a ^ 2 * (kernel x y * f y) +
      kernel x y * deriv (deriv f) y) volume (-q) q :=
    ((original.const_mul _).add derived).intervalIntegrable (-q) q
  have source := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => derivative y) complete
  have argument : a * (q : ℂ) = scale * (x : ℂ) := by dsimp only [a, scale]; ring
  have boundary : W q - W (-q) =
      a * Complex.sin (scale * (x : ℂ)) * (f q + f (-q)) +
        Complex.cos (scale * (x : ℂ)) * (deriv f q - deriv f (-q)) := by
    dsimp only [W]
    rw [Complex.ofReal_neg, mul_neg, Complex.sin_neg, Complex.cos_neg, argument]
    ring
  rw [boundary, intervalIntegral.integral_add ((original.const_mul _).intervalIntegrable (-q) q)
    (derived.intervalIntegrable (-q) q), intervalIntegral.integral_const_mul] at source
  have originalRead : ProlateTransform.transform f x = ∫ y : ℝ in (-q)..q, kernel x y * f y :=
    quarter_integral _
  have derivedRead : ProlateTransform.transform (deriv (deriv f)) x =
      ∫ y : ℝ in (-q)..q, kernel x y * deriv (deriv f) y := quarter_integral _
  rw [originalRead, derivedRead]
  dsimp only [a] at source
  linear_combination source

private theorem compact_tail {f : ℝ → ℂ} (regular : ContDiff ℝ 2 f)
    (even : ∀ y, f (-y) = f y) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 1 ≤ x →
      ‖ProlateTransform.transform f x - (2 * f q / frequency) *
        Complex.sin (scale * (x : ℂ)) / (x : ℂ)‖ ≤ D / x ^ 2 := by
  let C : ℝ := ‖deriv f q‖ + ‖deriv f (-q)‖ + ∫ y : ℝ, ‖deriv (deriv f) y‖ ∂μq
  have Cnonnegative : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C / (2 * Real.pi) ^ 2, div_nonneg Cnonnegative (sq_nonneg _), ?_⟩
  intro x large
  have xpositive : 0 < x := by linarith
  have xnonzero : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt xpositive
  have frequencyNonzero : frequency ≠ 0 := by
    unfold frequency
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have source := two_boundary_identity regular x
  rw [even q] at source
  have remainder :
      ProlateTransform.transform f x - (2 * f q / frequency) *
          Complex.sin (scale * (x : ℂ)) / (x : ℂ) =
        (Complex.cos (scale * (x : ℂ)) * (deriv f q - deriv f (-q)) -
          ProlateTransform.transform (deriv (deriv f)) x) / (frequency * (x : ℂ)) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero _ (mul_ne_zero frequencyNonzero xnonzero))).mpr
    field_simp
    linear_combination source
  have second : Continuous (deriv (deriv f)) :=
    (show ContDiff ℝ 1 (deriv f) from regular.deriv').continuous_deriv_one
  have cosBound : ‖Complex.cos (scale * (x : ℂ))‖ ≤ 1 := by
    have argument : scale * (x : ℂ) = frequency * (x : ℂ) * (q : ℂ) := by unfold scale; ring
    rw [argument]
    exact kernel_norm x q
  have numerator :
      ‖Complex.cos (scale * (x : ℂ)) * (deriv f q - deriv f (-q)) -
        ProlateTransform.transform (deriv (deriv f)) x‖ ≤ C := by
    apply (norm_sub_le _ _).trans
    apply add_le_add
    · rw [norm_mul]
      calc
        ‖Complex.cos (scale * (x : ℂ))‖ * ‖deriv f q - deriv f (-q)‖ ≤
            1 * ‖deriv f q - deriv f (-q)‖ := mul_le_mul_of_nonneg_right cosBound (norm_nonneg _)
        _ ≤ ‖deriv f q‖ + ‖deriv f (-q)‖ := by rw [one_mul]; exact norm_sub_le _ _
    · exact transform_bound second x
  rw [remainder, norm_div, norm_pow, norm_mul]
  have frequencyNorm : ‖frequency‖ = 2 * Real.pi := by
    simp [frequency, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [frequencyNorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos xpositive]
  calc
    _ ≤ C / (2 * Real.pi * x) ^ 2 := div_le_div_of_nonneg_right numerator (sq_nonneg _)
    _ = (C / (2 * Real.pi) ^ 2) / x ^ 2 := by ring

private theorem original_action_regular (coordinate : BurnolCompletedMellinCoordinate) :
    ContDiff ℝ 2 (act (burnolRieszReturnRaw coordinate)) := by
  have regular : ContDiff ℝ 4 (burnolRieszReturnRaw coordinate) :=
    (ProlateReturn.original_return_contDiff coordinate).of_le
      (WithTop.coe_le_coe.mpr (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have first : ContDiff ℝ 3 (deriv (burnolRieszReturnRaw coordinate)) := regular.deriv'
  have second : ContDiff ℝ 2 (deriv (deriv (burnolRieszReturnRaw coordinate))) := first.deriv'
  have raw : ContDiff ℝ 2 (burnolRieszReturnRaw coordinate) := regular.of_le (by norm_num)
  have rawFirst : ContDiff ℝ 2 (deriv (burnolRieszReturnRaw coordinate)) := first.of_le (by norm_num)
  have cast : ContDiff ℝ 2 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  unfold act
  fun_prop

private theorem action_even {f : ℝ → ℂ} (even : ∀ y, f (-y) = f y) (y : ℝ) :
    act f (-y) = act f y := by
  have first (x : ℝ) : deriv f (-x) = -deriv f x := by
    have source := deriv_comp_neg (f := f) (x := x)
    rw [show (fun y : ℝ => f (-y)) = f from funext even] at source
    linear_combination source
  have second : deriv (deriv f) (-y) = deriv (deriv f) y := by
    have source := deriv_comp_neg (f := deriv f) (x := y)
    rw [show (fun x : ℝ => deriv f (-x)) = fun x : ℝ => -deriv f x from funext first] at source
    change deriv (-deriv f) y = _ at source
    rw [deriv.neg] at source
    exact neg_injective source.symm
  unfold act
  rw [second, first, even, Complex.ofReal_neg]
  ring

/-- The compact return contribution retains the native q endpoint and pays its full quadratic tail. -/
theorem original_return_bound (coordinate : BurnolCompletedMellinCoordinate) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 1 ≤ x →
      ‖ProlateTransform.transform (act (burnolRieszReturnRaw coordinate)) x -
        (2 * act (burnolRieszReturnRaw coordinate) q / frequency) *
          Complex.sin (scale * (x : ℂ)) / (x : ℂ)‖ ≤ D / x ^ 2 :=
  compact_tail (original_action_regular coordinate) (action_even (return_raw_even coordinate))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.ProlateCompactTail
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

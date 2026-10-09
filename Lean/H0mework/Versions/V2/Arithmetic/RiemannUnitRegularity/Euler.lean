import H0mework.Versions.V2.Arithmetic.BurnolPhysical.L2DirectDilation
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! The original strong dilation graph supplies its Schwartz-tested Euler distribution equation. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

private def eulerCotest (test : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  (1 / 4 : ℂ) • test + (1 / 2 : ℂ) •
    SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) (SchwartzMap.derivCLM ℂ ℂ test)

private theorem eulerCotest_apply (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    eulerCotest test x = (1 / 4 : ℂ) * test x + (1 / 2 : ℂ) * (x : ℂ) * deriv test x := by
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [eulerCotest, add_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply growth, SchwartzMap.derivCLM_apply, smul_eq_mul]
  ring

private def cotestBound (test : SchwartzMap ℝ ℂ) : ℝ :=
  2 * (Finset.Iic (1, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) test

private theorem cotestBound_nonneg (test : SchwartzMap ℝ ℂ) : 0 ≤ cotestBound test := by
  unfold cotestBound
  positivity

private theorem cotest_decay (test : SchwartzMap ℝ ℂ) (x : ℝ) :
    (1 + ‖x‖) * ‖test x‖ ≤ cotestBound test := by
  simpa [cotestBound] using
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (1, 0)) (k := 1) (n := 0) le_rfl le_rfl test x)

private theorem cotest_scaled_decay (test : SchwartzMap ℝ ℂ)
    {h : ℝ} (hh : h ∈ Icc (-1 : ℝ) 1) (x : ℝ) :
    ‖test (Real.exp h * x)‖ ≤
      (Real.exp 1 * cotestBound test) * (1 + ‖x‖)⁻¹ := by
  have expLe : Real.exp (-h) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [hh.1])
  have expOne : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have xscale : x = Real.exp (-h) * (Real.exp h * x) := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  have xnorm : ‖x‖ ≤ Real.exp 1 * ‖Real.exp h * x‖ := by
    calc
      ‖x‖ = Real.exp (-h) * ‖Real.exp h * x‖ := by
        conv_lhs => rw [xscale]
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
      _ ≤ _ := mul_le_mul_of_nonneg_right expLe (norm_nonneg _)
  have compare : 1 + ‖x‖ ≤ Real.exp 1 * (1 + ‖Real.exp h * x‖) := by nlinarith
  have generated := (mul_le_mul_of_nonneg_right compare (norm_nonneg (test (Real.exp h * x)))).trans
    (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (cotest_decay test (Real.exp h * x)) (Real.exp_pos 1).le)
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using generated

private theorem inverse_weight_memLp :
    MemLp (fun x : ℝ => (1 + ‖x‖)⁻¹) 2 volume := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  simpa [Real.rpow_neg, Real.rpow_two, inv_pow] using
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num))

private def orbitCotest (test : SchwartzMap ℝ ℂ) (h x : ℝ) : ℂ :=
  (Real.exp (h / 4) : ℂ) * test (Real.exp (h / 2) * x)

private theorem orbitCotest_hasDerivAt (test : SchwartzMap ℝ ℂ) (h x : ℝ) :
    HasDerivAt (fun k : ℝ => orbitCotest test k x)
      ((Real.exp (h / 4) : ℂ) * eulerCotest test (Real.exp (h / 2) * x)) h := by
  have halfExp := ((hasDerivAt_id h).div_const 4).exp
  have scaleExp := (hasDerivAt_id h).div_const 2 |>.exp.mul_const x
  have testComp := (test.hasDerivAt (Real.exp (h / 2) * x)).scomp h scaleExp
  have generated := halfExp.smul testComp
  convert! generated using 1
  simp only [eulerCotest_apply, real_smul, id_eq, Function.comp_apply]
  push_cast
  ring

private theorem pairingCotest_hasDerivAt (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun h : ℝ => ∫ x : ℝ, orbitCotest test h x * value x)
      (∫ x : ℝ, eulerCotest test x * value x) 0 := by
  let F : ℝ → ℝ → ℂ := fun h x => orbitCotest test h x * value x
  let F' : ℝ → ℝ → ℂ := fun h x =>
    (Real.exp (h / 4) : ℂ) * eulerCotest test (Real.exp (h / 2) * x) * value x
  let C := Real.exp 1 * (Real.exp 1 * cotestBound (eulerCotest test))
  let bound : ℝ → ℝ := fun x => C * ((1 + ‖x‖)⁻¹ * ‖value x‖)
  have neighborhood : Icc (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have FMeasurable : ∀ᶠ h in 𝓝 (0 : ℝ), AEStronglyMeasurable (F h) volume :=
    Eventually.of_forall fun h => by
      have hc : Continuous (orbitCotest test h) := by unfold orbitCotest; fun_prop
      exact hc.aestronglyMeasurable.mul (Lp.memLp value).1
  have FIntegrable : Integrable (F 0) volume := by
    convert! (test.memLp 2 volume).integrable_mul (Lp.memLp value) using 1
    funext x
    simp [F, orbitCotest]
  have F'Measurable : AEStronglyMeasurable (F' 0) volume := by
    dsimp only [F']
    have hc : Continuous (fun x : ℝ =>
        (Real.exp (0 / 4) : ℂ) * eulerCotest test (Real.exp (0 / 2) * x)) := by fun_prop
    exact hc.aestronglyMeasurable.mul (Lp.memLp value).1
  have derivativeBound : ∀ᵐ x ∂volume, ∀ h ∈ Icc (-1 : ℝ) 1,
      ‖F' h x‖ ≤ bound x := by
    filter_upwards with x h hh
    have hhalf : h / 2 ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hh.1], by linarith [hh.2]⟩
    have expBound : Real.exp (h / 4) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by linarith [hh.2])
    dsimp only [F', bound, C]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc
      _ ≤ (Real.exp 1 *
          ((Real.exp 1 * cotestBound (eulerCotest test)) * (1 + ‖x‖)⁻¹)) * ‖value x‖ := by
        gcongr
        exact cotest_scaled_decay (eulerCotest test) hhalf x
      _ = _ := by ring
  have boundIntegrable : Integrable bound volume :=
    (inverse_weight_memLp.integrable_mul (Lp.memLp value).norm).const_mul C
  have pointwiseDerivative : ∀ᵐ x ∂volume, ∀ h ∈ Icc (-1 : ℝ) 1,
      HasDerivAt (fun k => F k x) (F' h x) h := by
    filter_upwards with x h _
    exact (orbitCotest_hasDerivAt test h x).mul_const (value x)
  have generated := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (F := F) (F' := F') (bound := bound)
    neighborhood FMeasurable FIntegrable F'Measurable
    derivativeBound boundIntegrable pointwiseDerivative
  simpa only [F, F', zero_div, Real.exp_zero, Complex.ofReal_one, one_mul] using generated.2

private theorem orbitPairing_eq (value : BurnolL2) (test : SchwartzMap ℝ ℂ) (h : ℝ) :
    (Lp.toTemperedDistributionCLM ℂ volume 2
      (burnolMultiplicativeDilation (-h / 2) value)) test =
        ∫ x : ℝ, orbitCotest test h x * value x := by
  let g : ℝ → ℂ := fun x => orbitCotest test h x * value x
  have cancel : Real.exp (h / 2) * Real.exp (-h / 2) = 1 := by
    rw [← Real.exp_add, show h / 2 + -h / 2 = 0 by ring, Real.exp_zero]
  have factor : Real.exp (-h / 2) * Real.exp (h / 4) = Real.exp ((-h / 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-h / 2) : ℂ) * ∫ x : ℝ, g (Real.exp (-h / 2) * x) := by
      rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [burnolMultiplicativeDilation_coeFn (-h / 2) value] with x hx
      rw [hx]
      dsimp only [g, orbitCotest, burnolL2RawNormalizedDilation]
      rw [← mul_assoc (Real.exp (h / 2)), cancel, one_mul]
      rw [smul_eq_mul, ← factor, Complex.ofReal_mul]
      ring
    _ = ∫ x : ℝ, g x := by
      rw [Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr (Real.exp_pos _)), real_smul]
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.exp_ne_zero _),
        Complex.ofReal_one, one_mul]

/-- The actual dilation already has a weak derivative for every original L² state. -/
theorem burnolDilation_weakDerivative (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun h : ℝ => (Lp.toTemperedDistributionCLM ℂ volume 2
      (burnolMultiplicativeDilation (-h / 2) value)) test)
      ((1 / 4 : ℂ) * (Lp.toTemperedDistributionCLM ℂ volume 2 value) test +
        (1 / 2 : ℂ) * (Lp.toTemperedDistributionCLM ℂ volume 2 value)
          (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
            (SchwartzMap.derivCLM ℂ ℂ test))) 0 := by
  have sameFunction :
      (fun h : ℝ => (Lp.toTemperedDistributionCLM ℂ volume 2
        (burnolMultiplicativeDilation (-h / 2) value)) test) =
      (fun h : ℝ => ∫ x : ℝ, orbitCotest test h x * value x) :=
    funext (orbitPairing_eq value test)
  rw [sameFunction]
  have read : (∫ x : ℝ, eulerCotest test x * value x) =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) (eulerCotest test) := by
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
    rfl
  have generated := pairingCotest_hasDerivAt value test
  rw [read] at generated
  simpa only [eulerCotest, map_add, map_smul, smul_eq_mul] using generated

/-- The given strong derivative of the original dilation supplies its weak Euler equation. -/
theorem burnolDilationStrong_eulerTested {value velocity : BurnolL2}
    (strong : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value) velocity 0)
    (test : SchwartzMap ℝ ℂ) :
    (Lp.toTemperedDistributionCLM ℂ volume 2 velocity) test =
      (1 / 4 : ℂ) * (Lp.toTemperedDistributionCLM ℂ volume 2 value) test +
      (1 / 2 : ℂ) * (Lp.toTemperedDistributionCLM ℂ volume 2 value)
        (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
          (SchwartzMap.derivCLM ℂ ℂ test)) := by
  let read : BurnolL2 →L[ℂ] ℂ :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) ℂ test).comp
      (Lp.toTemperedDistributionCLM ℂ volume 2)
  have strongRead := read.restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt 0 strong
  have weakRead := pairingCotest_hasDerivAt value test
  have sameFunction : (fun h : ℝ => read (burnolMultiplicativeDilation (-h / 2) value)) =
      (fun h : ℝ => ∫ x : ℝ, orbitCotest test h x * value x) := by
    funext h
    exact orbitPairing_eq value test h
  change HasDerivAt (fun h : ℝ => read (burnolMultiplicativeDilation (-h / 2) value))
    (read velocity) 0 at strongRead
  rw [sameFunction] at strongRead
  have answer := strongRead.unique weakRead
  change (Lp.toTemperedDistributionCLM ℂ volume 2 velocity) test =
    ∫ x : ℝ, eulerCotest test x * value x at answer
  have integralRead : (∫ x : ℝ, eulerCotest test x * value x) =
      (Lp.toTemperedDistributionCLM ℂ volume 2 value) (eulerCotest test) := by
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
    rfl
  rw [integralRead] at answer
  simpa only [eulerCotest, map_add, map_smul, smul_eq_mul] using answer

theorem burnolDilationStrong_eulerDistribution {value velocity : BurnolL2}
    (strong : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value)
      velocity 0) :
    TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
      (TemperedDistribution.derivCLM ℂ (value : TemperedDistribution ℝ ℂ)) =
      (((-2 : ℂ) • velocity - (1 / 2 : ℂ) • value : BurnolL2) :
        TemperedDistribution ℝ ℂ) := by
  ext test
  have generated := burnolDilationStrong_eulerTested strong test
  have derivative : SchwartzMap.derivCLM ℂ ℂ
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ)) test) =
        test + SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
          (SchwartzMap.derivCLM ℂ ℂ test) := by
    ext x
    rw [SchwartzMap.derivCLM_apply, SchwartzMap.smulLeftCLM_apply
      (by fun_prop : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth)]
    have source := Complex.ofRealCLM.hasDerivAt (x := x) |>.mul (test.hasDerivAt x)
    simpa [SchwartzMap.smulLeftCLM_apply (by fun_prop :
      (fun x : ℝ => (x : ℂ)).HasTemperateGrowth), smul_eq_mul, Pi.mul_def,
      Complex.ofRealCLM_apply] using source.deriv
  rw [TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.derivCLM_apply_apply, derivative, map_neg, map_add]
  change -((Lp.toTemperedDistributionCLM ℂ volume 2 value) test +
    (Lp.toTemperedDistributionCLM ℂ volume 2 value)
      (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
        (SchwartzMap.derivCLM ℂ ℂ test))) =
    (Lp.toTemperedDistributionCLM ℂ volume 2
      ((-2 : ℂ) • velocity - (1 / 2 : ℂ) • value)) test
  rw [map_sub, map_smul, map_smul]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  linear_combination 2 * generated

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import Mathlib.Analysis.Normed.Operator.Extend
import H0mework.Arithmetic.BurnolPhysical.PhysicalityProjection
import H0mework.Arithmetic.Muntz.CoPoissonSchwartzEnergyAction
import H0mework.Versions.Y.Arithmetic.SonineCoupling.ConjugateTateInverseDilationSource

/-!
# Multiplicative dilation on the additive Burnol carrier

The additive Burnol variable carries normalized multiplicative dilation,
not translation of the logarithmic quarter-energy coordinate.  The actual
Schwartz scaling equivalence extends uniquely across its dense `L²` image.
The resulting unitary is inverted by the opposite logarithmic scale, and
ordinary `L²` Fourier conjugates it to that inverse.

This is the source-owned action required by the Burnol constant-gap carrier.
It deliberately does not reuse the earlier log-translation compression.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory
open ClozelEndpointSourceEffect
open scoped ENNReal SchwartzMap InnerProductSpace

noncomputable section

private theorem complexExp_cpow_half (h : ℝ) :
    (Real.exp h : ℂ) ^ (1 / 2 : ℂ) =
      (Real.exp (h / 2) : ℂ) := by
  calc
    _ = ((Real.exp h ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      symm
      convert Complex.ofReal_cpow (Real.exp_pos h).le (1 / 2 : ℝ) using 1
      all_goals norm_num
    _ = _ := by
      congr 1
      rw [Real.rpow_def_of_pos (Real.exp_pos h), Real.log_exp]
      congr 1
      ring

theorem normalizedMultiplicativeSchwartzDilation_toLp_norm
    (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    ‖(coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
        (volume : Measure ℝ)‖ =
      ‖test.toLp 2 (volume : Measure ℝ)‖ := by
  have innerEq :
      inner ℂ ((coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
          (volume : Measure ℝ))
        ((coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
          (volume : Measure ℝ)) =
      inner ℂ (test.toLp 2 (volume : Measure ℝ))
        (test.toLp 2 (volume : Measure ℝ)) := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    calc
      (∫ x : ℝ,
          inner ℂ
            ((coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
              (volume : Measure ℝ) x)
            ((coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
              (volume : Measure ℝ) x)) =
        ∫ x : ℝ,
          inner ℂ
            (coPoissonSchwartzEnergyTranslationEquiv h test x)
            (coPoissonSchwartzEnergyTranslationEquiv h test x) := by
          apply integral_congr_ae
          filter_upwards [
            (coPoissonSchwartzEnergyTranslationEquiv h test).coeFn_toLp
              2 (volume : Measure ℝ)] with x hx
          rw [hx]
      _ = ∫ x : ℝ,
          (Real.exp h) • inner ℂ (test (Real.exp h * x))
            (test (Real.exp h * x)) := by
          apply integral_congr_ae
          filter_upwards with x
          change inner ℂ
              ((Real.exp h : ℂ) ^ (1 / 2 : ℂ) * test (Real.exp h * x))
              ((Real.exp h : ℂ) ^ (1 / 2 : ℂ) * test (Real.exp h * x)) = _
          rw [complexExp_cpow_half]
          rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
            norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos (h / 2)), Complex.real_smul]
          push_cast
          rw [mul_pow]
          have weightSquare :
              ((Real.exp (h / 2) : ℝ) : ℂ) ^ 2 =
                Complex.exp (h : ℂ) := by
            rw [← Complex.ofReal_exp]
            exact_mod_cast (by
              rw [← Real.exp_nat_mul]
              congr 1
              ring : Real.exp (h / 2) ^ 2 = Real.exp h)
          exact congrArg
            (fun coefficient : ℂ ↦ coefficient *
              ((‖test (Real.exp h * x)‖ : ℝ) : ℂ) ^ 2)
            weightSquare
      _ = ∫ y : ℝ, inner ℂ (test y) (test y) := by
          rw [integral_smul]
          let integrand : ℝ → ℂ := fun y ↦ inner ℂ (test y) (test y)
          have change := Measure.integral_comp_mul_left integrand (Real.exp h)
          change (Real.exp h) •
              (∫ x : ℝ, integrand (Real.exp h * x)) = ∫ y : ℝ, integrand y
          rw [change, abs_of_pos (inv_pos.mpr (Real.exp_pos h)), smul_smul,
            mul_inv_cancel₀ (Real.exp_ne_zero h), one_smul]
      _ = ∫ x : ℝ,
          inner ℂ (test.toLp 2 (volume : Measure ℝ) x)
            (test.toLp 2 (volume : Measure ℝ) x) := by
          apply integral_congr_ae
          filter_upwards [test.coeFn_toLp 2 (volume : Measure ℝ)] with x hx
          rw [hx]
  have squareEq :
      ‖(coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
          (volume : Measure ℝ)‖ ^ 2 =
        ‖test.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    calc
      _ = (inner ℂ
          ((coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
            (volume : Measure ℝ))
          ((coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
            (volume : Measure ℝ))).re :=
        InnerProductSpace.norm_sq_eq_re_inner ( 𝕜 := ℂ) _
      _ = (inner ℂ (test.toLp 2 (volume : Measure ℝ))
          (test.toLp 2 (volume : Measure ℝ))).re :=
        congrArg Complex.re innerEq
      _ = _ := (InnerProductSpace.norm_sq_eq_re_inner
        ( 𝕜 := ℂ) _).symm
  nlinarith [norm_nonneg
      ((coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
        (volume : Measure ℝ)),
    norm_nonneg (test.toLp 2 (volume : Measure ℝ))]

def burnolMultiplicativeDilation (h : ℝ) : BurnolL2 ≃ₗᵢ[ℂ] BurnolL2 :=
  (coPoissonSchwartzEnergyTranslationEquiv h).extendOfIsometry
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
    (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
    (normalizedMultiplicativeSchwartzDilation_toLp_norm h)

@[simp] theorem burnolMultiplicativeDilation_schwartz
    (h : ℝ) (test : SchwartzMap ℝ ℂ) :
    burnolMultiplicativeDilation h
        (test.toLp 2 (volume : Measure ℝ)) =
      (coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
        (volume : Measure ℝ) := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

theorem fourierL2_burnolMultiplicativeDilation
    (h : ℝ) (value : BurnolL2) :
    fourierL2 (burnolMultiplicativeDilation h value) =
      burnolMultiplicativeDilation (-h) (fourierL2 value) := by
  apply DenseRange.induction_on (p := fun value : BurnolL2 ↦
      fourierL2 (burnolMultiplicativeDilation h value) =
        burnolMultiplicativeDilation (-h) (fourierL2 value))
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top) value
  · apply isClosed_eq
    · exact fourierL2.continuous.comp
        (burnolMultiplicativeDilation h).continuous
    · exact (burnolMultiplicativeDilation (-h)).continuous.comp
        fourierL2.continuous
  · intro test
    change fourierL2
        (burnolMultiplicativeDilation h
          (test.toLp 2 (volume : Measure ℝ))) =
      burnolMultiplicativeDilation (-h)
        (fourierL2 (test.toLp 2 (volume : Measure ℝ)))
    rw [burnolMultiplicativeDilation_schwartz]
    change FourierTransform.fourier
        ((coPoissonSchwartzEnergyTranslationEquiv h test).toLp 2
          (volume : Measure ℝ)) =
      burnolMultiplicativeDilation (-h)
        (FourierTransform.fourier
          (test.toLp 2 (volume : Measure ℝ)))
    rw [SchwartzMap.toLp_fourier_eq,
      coPoissonSchwartzEnergyTranslationEquiv_apply,
      fourier_coPoissonSchwartzEnergyTranslation,
      SchwartzMap.toLp_fourier_eq,
      burnolMultiplicativeDilation_schwartz,
      coPoissonSchwartzEnergyTranslationEquiv_apply]

theorem burnolMultiplicativeDilation_neg_eq_symm (h : ℝ) :
    burnolMultiplicativeDilation (-h) =
      (burnolMultiplicativeDilation h).symm := by
  apply LinearIsometryEquiv.ext
  intro value
  apply DenseRange.induction_on (p := fun value : BurnolL2 ↦
      burnolMultiplicativeDilation (-h) value =
        (burnolMultiplicativeDilation h).symm value)
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
      (μ := (volume : Measure ℝ)) ENNReal.ofNat_ne_top) value
  · apply isClosed_eq
    · exact (burnolMultiplicativeDilation (-h)).continuous
    · exact (burnolMultiplicativeDilation h).symm.continuous
  · intro test
    change burnolMultiplicativeDilation (-h)
        (test.toLp 2 (volume : Measure ℝ)) =
      (burnolMultiplicativeDilation h).symm
        (test.toLp 2 (volume : Measure ℝ))
    apply (burnolMultiplicativeDilation h).injective
    rw [(burnolMultiplicativeDilation h).apply_symm_apply,
      burnolMultiplicativeDilation_schwartz,
      burnolMultiplicativeDilation_schwartz]
    congr 1
    exact (coPoissonSchwartzEnergyTranslationEquiv h).apply_symm_apply test

theorem fourierL2_burnolMultiplicativeDilation_inverse
    (h : ℝ) (value : BurnolL2) :
    fourierL2 (burnolMultiplicativeDilation h value) =
      (burnolMultiplicativeDilation h).symm (fourierL2 value) := by
  rw [← burnolMultiplicativeDilation_neg_eq_symm]
  exact fourierL2_burnolMultiplicativeDilation h value

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

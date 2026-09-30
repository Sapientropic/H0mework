import H0mework.Versions.Y.Arithmetic.BurnolPhysical.QuarterMellinAdditiveRechartAlgebra
import H0mework.Versions.Y.Arithmetic.BurnolPhysical.L2DirectDilation

/-!
# Actual dilation square for the quarter-Mellin additive rechart

Quarter dilation by exp(2h) and installed Burnol multiplicative dilation by
-h are the two exact action coordinates of the same reciprocal-square
rechart.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set
open scoped ENNReal InnerProductSpace

noncomputable section

private theorem quarterMellinAdditiveEvenRechartRaw_normalizedDilation
    (z : ℂ) (value : QuarterMellinL2Test z) (h x : ℝ) :
    quarterMellinAdditiveEvenRechartRaw
        (quarterDilationTestAction z (Real.exp (2 * h)) (Real.exp_pos _) value) x =
      (Real.exp (-h / 2) : ℂ) *
        quarterMellinAdditiveEvenRechartRaw value (Real.exp (-h) * x) := by
  by_cases hx : x = 0
  · subst x
    simp [quarterMellinAdditiveEvenRechartRaw,
      quarterMellinAdditivePositiveRechartRaw, positiveMellinExtension]
  · have absPositive : 0 < |x| := abs_pos.mpr hx
    have scaledAbs : |Real.exp (-h) * x| = Real.exp (-h) * |x| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have sourcePositive : 0 < |x| ^ (-2 : ℝ) := by positivity
    have scaledPositive :
        0 < |Real.exp (-h) * x| ^ (-2 : ℝ) := by positivity
    simp only [quarterMellinAdditiveEvenRechartRaw,
      quarterMellinAdditivePositiveRechartRaw, positiveMellinExtension,
      dif_pos sourcePositive, dif_pos scaledPositive,
      quarterDilationTestAction, positiveMellinQuarterNormalizedDilation,
      LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, positiveMellinRawDilation,
      LinearMap.coe_mk, AddHom.coe_mk]
    have argument :
        Real.exp (2 * h) * |x| ^ (-2 : ℝ) =
          (Real.exp (-h) * |x|) ^ (-2 : ℝ) := by
      rw [Real.mul_rpow (Real.exp_pos _).le absPositive.le]
      rw [Real.rpow_neg (Real.exp_pos _).le,
        Real.rpow_two]
      congr 1
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1
      ring
    have inputEq :
        (⟨Real.exp (2 * h) * |x| ^ (-2 : ℝ),
            mul_pos (Real.exp_pos _) sourcePositive⟩ : PositiveMellinReal) =
          ⟨|Real.exp (-h) * x| ^ (-2 : ℝ), scaledPositive⟩ := by
      apply Subtype.ext
      change Real.exp (2 * h) * |x| ^ (-2 : ℝ) =
        |Real.exp (-h) * x| ^ (-2 : ℝ)
      calc
        _ = (Real.exp (-h) * |x|) ^ (-2 : ℝ) := argument
        _ = _ := congrArg (fun t : ℝ => t ^ (-2 : ℝ)) scaledAbs.symm
    rw [inputEq]
    have inverseWeight :
        ((|Real.exp (-h) * x| : ℝ) : ℂ) ^ (-(1 : ℂ)) =
          (Real.exp h : ℂ) * (((|x| : ℝ) : ℂ)⁻¹) := by
      rw [scaledAbs, Complex.cpow_neg, Complex.cpow_one,
        Complex.ofReal_mul, mul_inv_rev,
        show ((Real.exp (-h) : ℝ) : ℂ)⁻¹ =
            (Real.exp h : ℂ) by
          rw [← Complex.ofReal_inv, ← Real.exp_neg]
          congr 2
          ring]
      ring
    rw [inverseWeight]
    unfold positiveMellinQuarterDilationWeight
    rw [Real.log_exp]
    have weightEq :
        ((Real.exp (2 * h / 4) : ℝ) : ℂ) =
          (Real.exp (h / 2) : ℂ) := by
      congr 2
      ring
    have balance :
        (Real.exp (-h / 2) : ℂ) * (Real.exp h : ℂ) =
          (Real.exp (h / 2) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    rw [weightEq]
    rw [Complex.cpow_neg, Complex.cpow_one]
    calc
      1 / 2 * (((|x| : ℝ) : ℂ)⁻¹ *
          ((Real.exp (h / 2) : ℂ) *
            value.1 ⟨|Real.exp (-h) * x| ^ (-2 : ℝ), scaledPositive⟩)) =
          1 / 2 * (Real.exp (h / 2) : ℂ) *
            (((|x| : ℝ) : ℂ)⁻¹) *
              value.1 ⟨|Real.exp (-h) * x| ^ (-2 : ℝ), scaledPositive⟩ := by
        ring
      _ = 1 / 2 *
          ((Real.exp (-h / 2) : ℂ) * (Real.exp h : ℂ)) *
            (((|x| : ℝ) : ℂ)⁻¹) *
              value.1 ⟨|Real.exp (-h) * x| ^ (-2 : ℝ), scaledPositive⟩ := by
        rw [balance]
      _ = (Real.exp (-h / 2) : ℂ) *
          (1 / 2 * ((Real.exp h : ℂ) *
            (((|x| : ℝ) : ℂ)⁻¹) *
              value.1 ⟨|Real.exp (-h) * x| ^ (-2 : ℝ), scaledPositive⟩)) := by
        ring

/-- The reciprocal-square additive rechart intertwines the actual quarter
dilation at scale `exp (2h)` with the installed Burnol multiplicative
dilation at logarithmic scale `-h`. -/
theorem quarterMellinAdditiveEvenRechart_normalizedDilation
    (z : ℂ) (value : QuarterMellinL2Test z) (h : ℝ) :
    quarterMellinAdditiveEvenRechart
        (quarterDilationTestAction z (Real.exp (2 * h)) (Real.exp_pos _) value) =
      burnolMultiplicativeDilation (-h)
        (quarterMellinAdditiveEvenRechart value) := by
  apply Lp.ext
  have qmp : Measure.QuasiMeasurePreserving
      (fun x : ℝ => Real.exp (-h) * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp (-h)) (Real.exp_ne_zero (-h)))
  filter_upwards [
    quarterMellinAdditiveEvenRechart_coeFn
      (quarterDilationTestAction z (Real.exp (2 * h)) (Real.exp_pos _) value),
    burnolMultiplicativeDilation_coeFn (-h)
      (quarterMellinAdditiveEvenRechart value),
    qmp.ae (quarterMellinAdditiveEvenRechart_coeFn value)]
      with x sourceRead targetRead originalRead
  calc
    quarterMellinAdditiveEvenRechart
        (quarterDilationTestAction z (Real.exp (2 * h)) (Real.exp_pos _) value) x =
        quarterMellinAdditiveEvenRechartRaw
          (quarterDilationTestAction z (Real.exp (2 * h)) (Real.exp_pos _) value) x :=
      sourceRead
    _ = (Real.exp (-h / 2) : ℂ) *
        quarterMellinAdditiveEvenRechartRaw value (Real.exp (-h) * x) :=
      quarterMellinAdditiveEvenRechartRaw_normalizedDilation z value h x
    _ = (Real.exp (-h / 2) : ℂ) *
        quarterMellinAdditiveEvenRechart value (Real.exp (-h) * x) := by
      rw [originalRead]
    _ = burnolL2RawNormalizedDilation (-h)
        (quarterMellinAdditiveEvenRechart value) x := by
      unfold burnolL2RawNormalizedDilation
      rfl
    _ = burnolMultiplicativeDilation (-h)
        (quarterMellinAdditiveEvenRechart value) x := targetRead.symm

/-- Arbitrary positive-scale form of the same action square. -/
theorem quarterMellinAdditiveEvenRechart_dilation
    (z : ℂ) (value : QuarterMellinL2Test z)
    (scale : ℝ) (positive : 0 < scale) :
    quarterMellinAdditiveEvenRechart
        (quarterDilationTestAction z scale positive value) =
      burnolMultiplicativeDilation (-(Real.log scale) / 2)
        (quarterMellinAdditiveEvenRechart value) := by
  let h : ℝ := Real.log scale / 2
  have scaleEq : Real.exp (2 * h) = scale := by
    dsimp only [h]
    rw [show 2 * (Real.log scale / 2) = Real.log scale by ring,
      Real.exp_log positive]
  have source := quarterMellinAdditiveEvenRechart_normalizedDilation
    z value h
  have actionEq :
      quarterDilationTestAction z scale positive value =
        quarterDilationTestAction z (Real.exp (2 * h)) (Real.exp_pos _) value := by
    apply Subtype.ext
    funext t
    change positiveMellinQuarterDilationWeight scale *
        value.1 ⟨scale * t.1, mul_pos positive t.2⟩ =
      positiveMellinQuarterDilationWeight (Real.exp (2 * h)) *
        value.1 ⟨Real.exp (2 * h) * t.1, mul_pos (Real.exp_pos _) t.2⟩
    have inputEq :
        (⟨scale * t.1, mul_pos positive t.2⟩ : PositiveMellinReal) =
          ⟨Real.exp (2 * h) * t.1, mul_pos (Real.exp_pos _) t.2⟩ := by
      apply Subtype.ext
      exact congrArg (fun current : ℝ => current * t.1) scaleEq.symm
    rw [inputEq, congrArg positiveMellinQuarterDilationWeight scaleEq]
  rw [actionEq]
  simpa only [h, neg_div] using source

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

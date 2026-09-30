import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import H0mework.Arithmetic.Mellin.QuarterL2
import H0mework.Arithmetic.Mellin.Functional
import H0mework.Versions.Y.Arithmetic.Mellin.PositiveMellinGaussianTate
import H0mework.Versions.Y.Arithmetic.Mellin.GaussianRemainderKernel

/-!
# Actual material in the quarter-weight L² carrier

The canonical low correction has an explicit log-quarter representative on
the negative half-line.  Its squared norm is an elementary exponential, so
the normalized-low class used by the q-rich character readout genuinely lies
in the generated `L²` carrier; this is not a chosen Hilbert vector.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set Filter Asymptotics
open scoped ENNReal

noncomputable section

def positiveClozelLowCorrection : ClozelPositiveMellinFunction :=
  fun t => clozelLowCorrection t.1

def positiveGeneratedClozelGaussianRemainder
    (owner : GlobalGermOwner) : ClozelPositiveMellinFunction :=
  fun t => generatedClozelGaussianRemainderKernel owner t.1

theorem positiveClozelLowCorrection_positiveMellinConvergent
    {z : ℂ} (hz : 0 < z.re) :
    MellinConvergent
      (positiveMellinExtension positiveClozelLowCorrection) z := by
  have h := hasMellin_clozelLowCorrection hz
  unfold MellinConvergent at h ⊢
  apply h.1.congr_fun
  · intro t ht
    change 0 < t at ht
    simp [positiveMellinExtension, positiveClozelLowCorrection,
      clozelLowCorrection, ht]
  · exact measurableSet_Ioi

theorem continuous_positiveMellinLogQuarterTransform_gaussianRemainder
    (owner : GlobalGermOwner) :
    Continuous (positiveMellinLogQuarterTransform
      (positiveGeneratedClozelGaussianRemainder owner)) := by
  unfold positiveMellinLogQuarterTransform
    positiveGeneratedClozelGaussianRemainder
    generatedClozelGaussianRemainderKernel
  rw [GeneratedRiemannWeakFEPairAt.generate_pair]
  apply Continuous.mul
  · fun_prop
  · apply Continuous.sub
    · apply Continuous.sub
      · exact (continuous_ofReal.comp_continuousOn
          (HurwitzZeta.continuousOn_evenKernel 0)).comp_continuous
          (by fun_prop) (fun x => Real.exp_pos x)
      · fun_prop
    · have cpowContinuous : Continuous
        (fun x : ℝ => (Real.exp x : ℂ) ^ (-(1 / 2 : ℂ))) := by
        rw [continuous_iff_continuousAt]
        intro x
        change ContinuousAt
          ((fun a : ℝ => (a : ℂ) ^ (-(1 / 2 : ℂ))) ∘ Real.exp) x
        exact (Complex.continuousAt_ofReal_cpow_const
          (Real.exp x) (-(1 / 2 : ℂ)) (Or.inr (Real.exp_ne_zero x))).comp
          (by fun_prop : ContinuousAt Real.exp x)
      exact cpowContinuous

theorem positiveMellinLogQuarterTransform_lowCorrection
    (x : ℝ) :
    positiveMellinLogQuarterTransform positiveClozelLowCorrection x =
      (Iic 0).indicator (fun y : ℝ => (Real.exp (y / 4) : ℂ)) x := by
  unfold positiveMellinLogQuarterTransform positiveClozelLowCorrection
    clozelLowCorrection
  change (Real.exp (x / 4) : ℂ) *
      (Ioc 0 1).indicator (fun _ => (1 : ℂ)) (Real.exp x) = _
  by_cases nonpositive : x ≤ 0
  · have expMem : Real.exp x ∈ Ioc (0 : ℝ) 1 :=
      ⟨Real.exp_pos x, Real.exp_le_one_iff.mpr nonpositive⟩
    rw [indicator_of_mem (mem_Iic.mpr nonpositive),
      indicator_of_mem expMem, mul_one]
  · have positive : 0 < x := lt_of_not_ge nonpositive
    have expNotMem : Real.exp x ∉ Ioc (0 : ℝ) 1 := by
      exact notMem_Ioc_of_gt (Real.one_lt_exp_iff.mpr positive)
    rw [indicator_of_notMem (notMem_Iic.mpr positive),
      indicator_of_notMem expNotMem, mul_zero]

theorem positiveMellinLogQuarterTransform_lowCorrection_sqNorm
    (x : ℝ) :
    ‖positiveMellinLogQuarterTransform positiveClozelLowCorrection x‖ ^ 2 =
      (Iic 0).indicator (fun y : ℝ => Real.exp (y / 2)) x := by
  rw [positiveMellinLogQuarterTransform_lowCorrection]
  by_cases nonpositive : x ≤ 0
  · rw [indicator_of_mem (mem_Iic.mpr nonpositive),
      indicator_of_mem (mem_Iic.mpr nonpositive)]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), pow_two, ← Real.exp_add]
    congr 1
    ring
  · have positive : 0 < x := lt_of_not_ge nonpositive
    rw [indicator_of_notMem (notMem_Iic.mpr positive),
      indicator_of_notMem (notMem_Iic.mpr positive), norm_zero,
      zero_pow (by norm_num)]

theorem positiveClozelLowCorrection_mem_quarterL2 :
    positiveClozelLowCorrection ∈ positiveMellinQuarterL2Submodule := by
  have measurable : AEStronglyMeasurable
      (positiveMellinLogQuarterTransform positiveClozelLowCorrection)
      (volume : Measure ℝ) := by
    rw [show positiveMellinLogQuarterTransform
        positiveClozelLowCorrection =
      (Iic 0).indicator
        (fun y : ℝ => (Real.exp (y / 4) : ℂ)) by
      funext x
      exact positiveMellinLogQuarterTransform_lowCorrection x]
    exact (Continuous.aestronglyMeasurable <| by fun_prop).indicator
      measurableSet_Iic
  change MemLp
    (positiveMellinLogQuarterTransform positiveClozelLowCorrection)
      (2 : ℝ≥0∞) (volume : Measure ℝ)
  rw [memLp_two_iff_integrable_sq_norm measurable]
  have exponentialIntegrable : IntegrableOn
      (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x)) (Iic 0) :=
    integrableOn_exp_mul_Iic (by norm_num) 0
  have indicatorIntegrable : Integrable
      ((Iic 0).indicator (fun x : ℝ => Real.exp (x / 2))) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    have functionEq :
        (fun x : ℝ => Real.exp (x / 2)) =
          (fun x : ℝ => Real.exp ((1 / 2 : ℝ) * x)) := by
      funext x
      congr 1
      ring
    rw [functionEq]
    exact exponentialIntegrable
  apply indicatorIntegrable.congr
  exact ae_of_all _ fun x =>
    (positiveMellinLogQuarterTransform_lowCorrection_sqNorm x).symm

theorem positiveNormalizedLowCorrection_mem_quarterL2
    (z : ℂ) :
    z • positiveClozelLowCorrection ∈ positiveMellinQuarterL2Submodule := by
  change MemLp
    (positiveMellinLogQuarterTransform (z • positiveClozelLowCorrection))
      (2 : ℝ≥0∞) (volume : Measure ℝ)
  rw [map_smul]
  exact positiveClozelLowCorrection_mem_quarterL2.const_smul z

theorem positiveGeneratedClozelGaussianRemainder_logQuarter_bigO
    (owner : GlobalGermOwner) :
    (fun x : ℝ =>
      positiveMellinLogQuarterTransform
        (positiveGeneratedClozelGaussianRemainder owner) x) =O[atTop]
      (fun x : ℝ => (Real.exp (-x / 4) : ℂ)) := by
  let P := (GeneratedRiemannWeakFEPairAt.generate owner).pair
  have hFreal :
      (fun x : ℝ => P.f (Real.exp x) - P.f₀) =O[atTop]
        (fun x : ℝ => (Real.exp x) ^ (-1 : ℝ)) := by
    have hFraw := (P.hf_top (-1)).comp_tendsto
      Real.tendsto_exp_atTop
    change (fun x : ℝ => P.f (Real.exp x) - P.f₀) =O[atTop]
      (fun x : ℝ => (Real.exp x) ^ (-1 : ℝ)) at hFraw
    exact hFraw
  have hF :
      (fun x : ℝ => P.f (Real.exp x) - P.f₀) =O[atTop]
        (fun x : ℝ => (Real.exp (-x) : ℂ)) := by
    apply Complex.isBigO_ofReal_right.mpr
    simpa [Real.rpow_neg_one, Real.exp_neg] using hFreal
  have hW :
      (fun x : ℝ => (Real.exp (x / 4) : ℂ)) =O[atTop]
        (fun x : ℝ => (Real.exp (x / 4) : ℂ)) :=
    isBigO_refl _ _
  have hA := hW.mul hF
  have hA' :
      (fun x : ℝ => (Real.exp (x / 4) : ℂ) *
        (P.f (Real.exp x) - P.f₀)) =O[atTop]
        (fun x : ℝ => (Real.exp (-3 * x / 4) : ℂ)) := by
    have targetEq :
        (fun x : ℝ => (Real.exp (x / 4) : ℂ) *
          (Real.exp (-x) : ℂ)) =
          (fun x : ℝ => (Real.exp (-3 * x / 4) : ℂ)) := by
      funext x
      rw [← ofReal_mul, ← Real.exp_add]
      congr 1
      ring
    rw [targetEq] at hA
    exact hA
  have hB :
      (fun x : ℝ => (Real.exp (-x / 4) : ℂ)) =O[atTop]
        (fun x : ℝ => (Real.exp (-x / 4) : ℂ)) :=
    isBigO_refl _ _
  have hAweak :
      (fun x : ℝ => (Real.exp (-3 * x / 4) : ℂ)) =O[atTop]
        (fun x : ℝ => (Real.exp (-x / 4) : ℂ)) := by
    rw [isBigO_iff]
    refine ⟨1, eventually_atTop.2 ⟨0, fun x hx => ?_⟩⟩
    rw [Complex.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_of_nonneg (Real.exp_pos _).le, one_mul]
    rw [Real.exp_le_exp]
    linarith
  have hG :
      (fun x : ℝ => (Real.exp (x / 4) : ℂ) *
        (P.f (Real.exp x) - P.f₀) -
          (Real.exp (-x / 4) : ℂ)) =O[atTop]
        (fun x : ℝ => (Real.exp (-x / 4) : ℂ)) :=
    (hA'.trans hAweak).sub hB
  have transformEq :
      (fun x : ℝ =>
        positiveMellinLogQuarterTransform
          (positiveGeneratedClozelGaussianRemainder owner) x) =
        (fun x : ℝ => (Real.exp (x / 4) : ℂ) *
          (P.f (Real.exp x) - P.f₀) -
            (Real.exp (-x / 4) : ℂ)) := by
    funext x
    have Pzero : P.f₀ = 1 := by
      exact GeneratedRiemannWeakFEPairAt.generate_f₀ owner
    change (Real.exp (x / 4) : ℂ) *
        (P.f (Real.exp x) - 1 -
          (Real.exp x : ℂ) ^ (-(1 / 2 : ℂ))) = _
    rw [complexExp_cpow_neg_half, Pzero]
    have expQuarter :
        (Real.exp (x / 4) : ℂ) * (Real.exp (-x / 2) : ℂ) =
          (Real.exp (-x / 4) : ℂ) := by
      rw [← ofReal_mul, ← Real.exp_add]
      congr 1
      ring
    calc
      (Real.exp (x / 4) : ℂ) *
          (P.f (Real.exp x) - 1 -
            (Real.exp (-x / 2) : ℂ)) =
        (Real.exp (x / 4) : ℂ) * (P.f (Real.exp x) - 1) -
          (Real.exp (x / 4) : ℂ) * (Real.exp (-x / 2) : ℂ) := by ring
      _ = (Real.exp (x / 4) : ℂ) * (P.f (Real.exp x) - 1) -
          (Real.exp (-x / 4) : ℂ) := by rw [expQuarter]
  rw [transformEq]
  exact hG

theorem positiveGeneratedClozelGaussianRemainder_mem_quarterL2
    (owner : GlobalGermOwner) :
    positiveGeneratedClozelGaussianRemainder owner ∈
      positiveMellinQuarterL2Submodule := by
  let g : ℝ → ℂ := positiveMellinLogQuarterTransform
    (positiveGeneratedClozelGaussianRemainder owner)
  let H : ℝ → ℝ := fun x => ‖g x‖ ^ 2
  have hgcont : Continuous g := by
    exact continuous_positiveMellinLogQuarterTransform_gaussianRemainder owner
  have hHcont : Continuous H := by
    exact (hgcont.norm.pow 2)
  have hlocal : LocallyIntegrable H (volume : Measure ℝ) :=
    hHcont.locallyIntegrable
  have hgO : g =O[atTop]
      (fun x : ℝ => (Real.exp (-x / 4) : ℂ)) := by
    exact positiveGeneratedClozelGaussianRemainder_logQuarter_bigO owner
  have hgnorm : (fun x => ‖g x‖) =O[atTop]
      (fun x => ‖(Real.exp (-x / 4) : ℂ)‖) :=
    isBigO_norm_norm.mpr hgO
  have hHraw := hgnorm.mul hgnorm
  have hHbigO : H =O[atTop]
      (fun x : ℝ => Real.exp (-x / 2)) := by
    have leftEq :
        (fun x : ℝ => ‖g x‖ * ‖g x‖) = H := by
      funext x
      simp only [H, pow_two]
    have rightEq :
        (fun x : ℝ => ‖(Real.exp (-x / 4) : ℂ)‖ *
          ‖(Real.exp (-x / 4) : ℂ)‖) =
          (fun x : ℝ => Real.exp (-x / 2)) := by
      funext x
      rw [Complex.norm_of_nonneg (Real.exp_pos _).le]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [leftEq, rightEq] at hHraw
    exact hHraw
  have hsymm :
      (fun x : ℝ => ‖H x‖) =ᵐ[(volume : Measure ℝ)]
        (fun x : ℝ => ‖H (-x)‖) := by
    have tateFixed :
        positiveTateInvolution
            (positiveGeneratedClozelGaussianRemainder owner) =
          positiveGeneratedClozelGaussianRemainder owner := by
      funext t
      exact congrFun (positiveTateInvolution_clozelRelation owner) t
    have gSymm : ∀ x : ℝ, g (-x) = g x := by
      intro x
      have h := positiveMellinLogQuarterTransform_tate
        (positiveGeneratedClozelGaussianRemainder owner) x
      rw [tateFixed] at h
      exact h.symm
    filter_upwards [] with x
    simp only [H, Real.norm_of_nonneg (sq_nonneg _), gSymm]
  have hExp : IntegrableAtFilter
      (fun x : ℝ => Real.exp (-x / 2)) atTop (volume : Measure ℝ) := by
    rw [integrableAtFilter_atTop_iff]
    refine ⟨0, ?_⟩
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have expEq :
        (fun x : ℝ => Real.exp (-x / 2)) =
          (fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x)) := by
      funext x
      congr 1
      ring
    rw [expEq]
    exact exp_neg_integrableOn_Ioi 0
      (by norm_num : (0 : ℝ) < 1 / 2)
  have hInt : Integrable H (volume : Measure ℝ) :=
    hlocal.integrable_of_isBigO_atTop_of_norm_isNegInvariant
      hsymm hHbigO hExp
  change MemLp g (2 : ℝ≥0∞) (volume : Measure ℝ)
  rw [memLp_two_iff_integrable_sq_norm hgcont.aestronglyMeasurable]
  exact hInt

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

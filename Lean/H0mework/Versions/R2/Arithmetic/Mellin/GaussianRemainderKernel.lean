import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import H0mework.Arithmetic.Tempered.Remainder
import H0mework.Versions.R2.Arithmetic.RiemannSource.ThetaMellinContinuation

/-!
# Source-generated Gaussian remainder kernel

The generated Riemann weak functional-equation pair supplies the actual theta
kernel.  Subtracting its two canonical zero-mode asymptotics gives
`theta(t) - 1 - t⁻¹ᐟ²`.  This module identifies that function with the scalar
integer-Gaussian remainder and with Mathlib's piecewise modified FE kernel
minus the two exact pole corrections.

This is a source-owned scalar incidence.  It neither chooses an arbitrary
Schwartz test nor identifies completed scalar values with centered parameters.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization

noncomputable section

def clozelLowCorrection (t : ℝ) : ℂ :=
  (Ioc 0 1).indicator (fun _ => (1 : ℂ)) t

def clozelHighCorrection (t : ℝ) : ℂ :=
  (Ioi 1).indicator
    (fun u : ℝ => (u : ℂ) ^ (-(1 / 2 : ℂ))) t

theorem hasMellin_clozelLowCorrection {z : ℂ} (hz : 0 < z.re) :
    HasMellin clozelLowCorrection z (1 / z) := by
  have exponentLt : -1 < (z - 1).re := by
    simp only [sub_re, one_re]
    linarith
  have zNe : z ≠ 0 := by
    intro equality
    rw [equality, zero_re] at hz
    exact lt_irrefl 0 hz
  have measurable : MeasurableSet (Ioc (0 : ℝ) 1) := measurableSet_Ioc
  simp_rw [HasMellin, mellin, MellinConvergent,
    clozelLowCorrection, ← indicator_smul, IntegrableOn,
    integrable_indicator_iff measurable, smul_eq_mul,
    integral_indicator measurable, mul_one, IntegrableOn,
    Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
  rw [← IntegrableOn]
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine ⟨intervalIntegral.intervalIntegrable_cpow' exponentLt, ?_⟩
  rw [← intervalIntegral.integral_of_le zero_le_one,
    integral_cpow (Or.inl exponentLt), sub_add_cancel,
    ofReal_zero, ofReal_one, one_cpow, zero_cpow zNe, sub_zero]

theorem hasMellin_clozelHighCorrection {z : ℂ}
    (hz : z.re < (1 / 2 : ℝ)) :
    HasMellin clozelHighCorrection z
      (1 / ((1 / 2 : ℂ) - z)) := by
  have exponentLt :
      (z - 1 - (1 / 2 : ℂ)).re < -1 := by
    norm_num [Complex.div_re] at *
    linarith
  have exponentNe : z - 1 - (1 / 2 : ℂ) ≠ -1 := by
    intro equality
    have := congrArg Complex.re equality
    norm_num [Complex.div_re] at this
    linarith
  have integrablePower :
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (z - 1 - (1 / 2 : ℂ)))
        (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt exponentLt zero_lt_one
  constructor
  · unfold MellinConvergent clozelHighCorrection
    simp_rw [← indicator_smul]
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioi]
    change Integrable
      (fun t : ℝ => (t : ℂ) ^ (z - 1) •
        (t : ℂ) ^ (-(1 / 2 : ℂ)))
      ((volume.restrict (Ioi 0)).restrict (Ioi 1))
    rw [Measure.restrict_restrict_of_subset
      (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]
    apply integrablePower.congr_fun
    · intro t ht
      simp only [smul_eq_mul]
      rw [← cpow_add _ _
        (ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans ht)))]
      ring_nf
    · exact measurableSet_Ioi
  · unfold mellin clozelHighCorrection
    simp_rw [← indicator_smul]
    rw [integral_indicator measurableSet_Ioi]
    change (∫ t : ℝ,
      (t : ℂ) ^ (z - 1) • (t : ℂ) ^ (-(1 / 2 : ℂ))
        ∂((volume.restrict (Ioi 0)).restrict (Ioi 1))) = _
    rw [Measure.restrict_restrict_of_subset
      (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))]
    have integralPower := integral_Ioi_cpow_of_lt exponentLt zero_lt_one
    convert integralPower using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [smul_eq_mul]
      rw [← cpow_add _ _
        (ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans ht)))]
      ring_nf
    · rw [ofReal_one, one_cpow, neg_div]
      rw [show (1 / 2 : ℂ) - z =
        -(z - (1 / 2 : ℂ)) by ring,
        one_div_neg_eq_neg_one_div]
      congr 2
      ring

def generatedClozelGaussianRemainderKernel
    (owner : GlobalGermOwner) (t : ℝ) : ℂ :=
  (GeneratedRiemannWeakFEPairAt.generate owner).pair.f t - 1 -
    (t : ℂ) ^ (-(1 / 2 : ℂ))

theorem integral_clozelGaussian (t : ℝ) (positive : 0 < t) :
    ((∫ x : ℝ, Real.exp (-Real.pi * t * x ^ 2) : ℝ) : ℂ) =
      (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
  rw [show (fun x : ℝ => Real.exp (-Real.pi * t * x ^ 2)) =
      (fun x : ℝ => Real.exp (-(Real.pi * t) * x ^ 2)) by
        funext x
        congr 1
        ring]
  rw [integral_gaussian]
  have ratio : Real.pi / (Real.pi * t) = t⁻¹ := by
    field_simp [Real.pi_ne_zero, positive.ne']
  rw [ratio, Real.sqrt_eq_rpow,
    ← Real.rpow_neg_eq_inv_rpow,
    Complex.ofReal_cpow positive.le]
  congr 2
  norm_num

theorem generatedClozelGaussianRemainderKernel_eq_scalarRemainder
    (owner : GlobalGermOwner) (t : ℝ) (positive : 0 < t) :
    generatedClozelGaussianRemainderKernel owner t =
      ((∑' n : ℤ,
          Real.exp (-Real.pi * ((n : ℝ) + 0) ^ 2 * t) : ℝ) : ℂ) -
        1 -
        ((∫ x : ℝ, Real.exp (-Real.pi * t * x ^ 2) : ℝ) : ℂ) := by
  unfold generatedClozelGaussianRemainderKernel
  rw [GeneratedRiemannWeakFEPairAt.generate_pair]
  change ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1 -
      (t : ℂ) ^ (-(1 / 2 : ℂ)) = _
  have thetaSum :
      (∑' n : ℤ,
        Real.exp (-Real.pi * ((n : ℝ) + 0) ^ 2 * t)) =
        HurwitzZeta.evenKernel 0 t := by
    simpa using (HurwitzZeta.hasSum_int_evenKernel 0 positive).tsum_eq
  rw [thetaSum, integral_clozelGaussian t positive]

/-- The scalar Gaussian remainder is fixed by the weight-`1/2` Tate
involution.  This is the multiplicative form of the same Poisson symmetry as
the actual tempered remainder's Fourier invariance. -/
theorem generatedClozelGaussianRemainderKernel_selfReciprocal
    (owner : GlobalGermOwner) (t : ℝ) (positive : 0 < t) :
    generatedClozelGaussianRemainderKernel owner t =
      (t : ℂ) ^ (-(1 / 2 : ℂ)) *
        generatedClozelGaussianRemainderKernel owner (1 / t) := by
  unfold generatedClozelGaussianRemainderKernel
  rw [GeneratedRiemannWeakFEPairAt.generate_pair]
  change ((HurwitzZeta.evenKernel 0 t : ℝ) : ℂ) - 1 -
      (t : ℂ) ^ (-(1 / 2 : ℂ)) =
    (t : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((HurwitzZeta.evenKernel 0 (1 / t) : ℝ) : ℂ) - 1 -
        ((1 / t : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))
  have thetaFE :
      HurwitzZeta.evenKernel 0 t =
        1 / t ^ (1 / 2 : ℝ) *
          HurwitzZeta.evenKernel 0 (1 / t) := by
    simpa [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] using
      HurwitzZeta.evenKernel_functional_equation 0 t
  rw [thetaFE, ofReal_mul, ofReal_div, ofReal_one,
    Complex.ofReal_cpow positive.le]
  have tNe : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr positive.ne'
  have reciprocalCpow :
      ((1 / t : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
        (t : ℂ) ^ (1 / 2 : ℂ) := by
    calc
      _ = (((1 / t : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
        symm
        convert Complex.ofReal_cpow
          (one_div_nonneg.mpr positive.le) (-(1 / 2 : ℝ))
          using 1
        all_goals norm_num
      _ = ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        congr 1
        rw [one_div, Real.rpow_neg_eq_inv_rpow, inv_inv]
      _ = _ := by
        convert Complex.ofReal_cpow positive.le (1 / 2 : ℝ)
          using 1
        all_goals norm_num
  rw [ofReal_div, ofReal_one, Complex.cpow_neg,
    div_eq_mul_inv, one_mul, reciprocalCpow]
  have halfNe : (t : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl tNe)
  norm_num at halfNe ⊢
  field_simp [halfNe]
  ring

def generatedClozelModifiedMinusCorrections
    (owner : GlobalGermOwner) (t : ℝ) : ℂ :=
  (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t -
    clozelLowCorrection t - clozelHighCorrection t

theorem generatedClozelGaussianRemainderKernel_ae_eq_modified
    (owner : GlobalGermOwner) :
    generatedClozelGaussianRemainderKernel owner =ᵐ[volume.restrict (Ioi 0)]
      generatedClozelModifiedMinusCorrections owner := by
  filter_upwards
    [ae_restrict_mem measurableSet_Ioi,
      compl_mem_ae_iff.mpr
        (Subsingleton.measure_zero (s := ({1} : Set ℝ)) (by simp) _)]
    with t (positive : t ∈ Ioi 0) (notOne : t ≠ 1)
  unfold generatedClozelGaussianRemainderKernel
  unfold generatedClozelModifiedMinusCorrections
  unfold clozelLowCorrection clozelHighCorrection
  rw [WeakFEPair.f_modif]
  change 0 < t at positive
  rcases lt_or_gt_of_ne notOne with below | above
  · rw [Pi.add_apply,
      indicator_of_notMem (notMem_Ioi.mpr below.le),
      indicator_of_mem (mem_Ioo.mpr ⟨positive, below⟩),
      indicator_of_mem (mem_Ioc.mpr ⟨positive, below.le⟩),
      indicator_of_notMem (notMem_Ioi.mpr below.le)]
    simp [HurwitzZeta.hurwitzEvenFEPair,
      Complex.ofReal_cpow positive.le]
    ring
  · rw [Pi.add_apply,
      indicator_of_mem (mem_Ioi.mpr above),
      indicator_of_notMem (notMem_Ioo_of_ge above.le),
      indicator_of_notMem (notMem_Ioc_of_gt above),
      indicator_of_mem (mem_Ioi.mpr above)]
    simp [HurwitzZeta.hurwitzEvenFEPair]

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

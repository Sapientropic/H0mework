import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderKernel

/-! Dilation and Fourier act on the same comb-remainder source. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped InnerProductSpace
noncomputable section
local notation "Ambient" => EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius

theorem burnolMultiplicativeDilation_star (shift : ℝ) (value : BurnolL2) :
    star (burnolMultiplicativeDilation shift value) =
      burnolMultiplicativeDilation shift (star value) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp shift * x)
      volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp shift) (Real.exp_ne_zero shift))
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (burnolMultiplicativeDilation shift value),
    burnolMultiplicativeDilation_coeFn shift value,
    burnolMultiplicativeDilation_coeFn shift (star value),
    qmp.ae (Lp.coeFn_star value)] with x hstar hvalue htarget hsource
  rw [hstar, Pi.star_apply, hvalue, htarget]
  unfold burnolL2RawNormalizedDilation
  rw [hsource]
  change (starRingEnd ℂ) ((Real.exp (shift / 2) : ℂ) * value (Real.exp shift * x)) =
    (Real.exp (shift / 2) : ℂ) * (starRingEnd ℂ) (value (Real.exp shift * x))
  rw [map_mul, Complex.conj_ofReal]

/-- The same integer-comb source acts before either projection. -/
theorem burnolRemainderSourceRead_dilation (shift : ℝ) (source : BurnolL2)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolMultiplicativeDilation shift source) test =
      burnolRemainderSourceRead source (burnolRemainderSchwartzDilation (-shift) test) := by
  change (1 / 2 : ℂ) * inner ℂ (star (burnolMultiplicativeDilation shift source))
    (burnolRemainderL2Kernel test) =
      (1 / 2 : ℂ) * inner ℂ (star source)
        (burnolRemainderL2Kernel (burnolRemainderSchwartzDilation (-shift) test))
  rw [burnolMultiplicativeDilation_star, (burnolMultiplicativeDilation shift).inner_map_eq_flip,
    burnolRemainderL2Kernel_dilation, burnolMultiplicativeDilation_neg_eq_symm]

private theorem tate_star (value : BurnolL2) :
    star (burnolTateReciprocalL2 value) = burnolTateReciprocalL2 (star value) := by
  have pulled := burnolTateReciprocalRaw_ae_congr (Lp.memLp (star value))
    ((Lp.memLp value).star) (Lp.coeFn_star value)
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (burnolTateReciprocalL2 value),
    burnolTateReciprocalL2_coeFn value, burnolTateReciprocalL2_coeFn (star value), pulled]
    with x hstar hvalue htarget hsource
  rw [hstar, Pi.star_apply, hvalue, htarget, hsource]
  unfold burnolTateReciprocalRaw
  change (starRingEnd ℂ) (((|x| : ℝ) : ℂ)⁻¹ * value x⁻¹) =
    ((|x| : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) (value x⁻¹)
  rw [map_mul, map_inv₀, Complex.conj_ofReal]

private def tateLinearIsometry : BurnolL2 →ₗᵢ[ℂ] BurnolL2 where
  toLinearMap := burnolTateReciprocalL2.toLinearMap
  norm_map' := burnolTateReciprocalValue_norm

theorem burnolRemainderSourceRead_fourier (source : BurnolL2)
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead (burnolTateReciprocalL2 source) test =
      burnolRemainderSourceRead source (FourierTransform.fourier test) := by
  change (1 / 2 : ℂ) * inner ℂ (star (burnolTateReciprocalL2 source))
    (burnolRemainderL2Kernel test) =
      (1 / 2 : ℂ) * inner ℂ (star source)
        (burnolRemainderL2Kernel (FourierTransform.fourier test))
  rw [tate_star, burnolRemainderL2Kernel_fourier]
  congr 1
  have paired := tateLinearIsometry.inner_map_map (star source)
    (burnolTateReciprocalL2 (burnolRemainderL2Kernel test))
  change inner ℂ (burnolTateReciprocalL2 (star source))
    (burnolTateReciprocalL2 (burnolTateReciprocalL2 (burnolRemainderL2Kernel test))) = _ at paired
  rw [burnolTateReciprocalL2_involutive] at paired
  exact paired

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderCompact
import H0mework.Arithmetic.RemainderSource.Divisor

/-! The complete comb-remainder source is its forward divisor sum with its own reciprocal mean. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set
open scoped ArithmeticFunction
noncomputable section

theorem burnolInnerGapForward_ae_congr (left right : ℝ → ℂ) (same : left =ᵐ[volume] right) :
    burnolInnerGapForward left =ᵐ[volume] burnolInnerGapForward right := by
  have scaled (n : ℕ+) : ∀ᵐ x : ℝ ∂volume,
      left (x / (n : ℕ)) = right (x / (n : ℕ)) := by
    have positive : (0 : ℝ) < (n : ℕ) := by exact_mod_cast n.pos
    have qmp := Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
      (r := ((n : ℕ) : ℝ)⁻¹) (inv_ne_zero positive.ne')
    simpa only [smul_eq_mul, inv_mul_eq_div] using qmp.ae same
  filter_upwards [ae_all_iff.mpr scaled] with x all
  apply tsum_congr
  intro n
  rw [all n]

private theorem series_integrable (f : ℕ → ℝ → ℂ)
    (measurable : ∀ n, Measurable (f n)) (integrable : ∀ n, Integrable (f n))
    (summable : Summable (fun n => ∫ x : ℝ, ‖f n x‖)) :
    Integrable (fun x => ∑' n, f n x) := by
  refine ⟨(Measurable.tsum measurable).aestronglyMeasurable, ?_⟩
  have mass (n : ℕ) : (∫⁻ x : ℝ, ‖f n x‖ₑ) =
      ‖∫ x : ℝ, ‖f n x‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (integrable n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (f n x))]
    simp only [coe_nnnorm]
  have finite : (∑' n, ∫⁻ x : ℝ, ‖f n x‖ₑ) ≠ ⊤ := by
    simp_rw [mass]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 summable.abs)
  unfold HasFiniteIntegral
  calc
    _ ≤ ∫⁻ x : ℝ, ∑' n, ‖f n x‖ₑ := lintegral_mono fun _ => enorm_tsum_le_tsum_enorm
    _ = ∑' n, ∫⁻ x : ℝ, ‖f n x‖ₑ :=
      lintegral_tsum (fun n => (measurable n).enorm.aemeasurable)
    _ < ⊤ := lt_top_iff_ne_top.mpr finite

theorem burnolInnerGapForward_test_integrable (raw : ℝ → ℂ) (measurable : Measurable raw)
    (atZero : raw 0 = 0) (weighted : Integrable (fun x : ℝ => ‖raw x‖ / |x| ^ 3))
    (test : SchwartzMap ℝ ℂ) :
    Integrable (fun x : ℝ => test x * burnolInnerGapForward raw x) := by
  let family := MobiusSourceFourierPairing.original raw (FourierTransform.fourierInv test)
  have familyMeasurable : ∀ n, Measurable (family n) := by
    intro n
    exact (FourierTransform.fourier (FourierTransform.fourierInv test)).continuous.measurable.mul
      (measurable_const.mul (measurable.comp (measurable_id.div_const _)))
  have familyIntegrable := series_integrable family familyMeasurable
    (MobiusSourceFourierPairing.original_integrable raw measurable atZero weighted _)
    (MobiusSourceFourierPairing.summable_integral_norm_original raw measurable atZero weighted _)
  apply familyIntegrable.congr
  filter_upwards with x
  dsimp only [family, MobiusSourceFourierPairing.original]
  rw [FourierTransform.fourier_fourierInv_eq, tsum_mul_left]
  congr 1
  exact Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
    (fun n : ℕ+ => (((n : ℕ) : ℂ)⁻¹) * raw (x / (n : ℕ)))

private theorem half_integral_even (raw : ℝ → ℂ) (integrable : Integrable raw)
    (even : ∀ x, raw (-x) = raw x) :
    (1 / 2 : ℂ) * (∫ x : ℝ, raw x) = ∫ x : ℝ in Ioi 0, raw x := by
  have negative : (∫ x : ℝ in Iic 0, raw x) = ∫ x : ℝ in Ioi 0, raw x := by
    calc
      _ = ∫ x : ℝ in Iic 0, raw (-x) :=
        setIntegral_congr_fun measurableSet_Iic (fun x _ => (even x).symm)
      _ = _ := by simpa only [neg_zero] using integral_comp_neg_Iic 0 raw
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      integrable.integrableOn integrable.integrableOn, negative]
  ring

theorem burnolRemainderSourceRead_forward (source : BurnolL2) (raw : ℝ → ℂ)
    (measurable : Measurable raw) (represents : (source : ℝ → ℂ) =ᵐ[volume] raw)
    (atZero : raw 0 = 0) (even : ∀ x, raw (-x) = raw x)
    (weighted : Integrable (fun x : ℝ => ‖raw x‖ / |x| ^ 3))
    (reciprocal : IntegrableOn (fun x : ℝ => (x : ℂ)⁻¹ * raw x) (Ioi 0))
    (test : SchwartzMap ℝ ℂ) :
    burnolRemainderSourceRead source test =
      ∫ x : ℝ, test x * (burnolInnerGapForward raw x -
        ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u) := by
  let normal := ∫ u : ℝ in Ioi 0, (u : ℂ)⁻¹ * raw u
  have rawMem : MemLp raw 2 volume := (Lp.memLp source).ae_eq represents
  have kernelMem : MemLp (fun x : ℝ => coPoissonMuntzScaleRemainder test |x|) 2 volume :=
    (Lp.memLp (burnolRemainderL2Kernel test)).ae_eq (burnolRemainderL2Kernel_coeFn test)
  have thetaRead : (∫ x : ℝ, test x * burnolInnerGapForward raw x) =
      ∫ u : ℝ in Ioi 0, raw u * coPoissonMuntzThetaNonzero test u := by
    have reindex (x : ℝ) : burnolInnerGapForward raw x =
        ∑' n : ℕ, ((n + 1 : ℕ) : ℂ)⁻¹ * raw (x / (n + 1 : ℕ)) :=
      (Equiv.tsum_eq (Equiv.pnatEquivNat.symm)
        (fun n : ℕ+ => (((n : ℕ) : ℂ)⁻¹) * raw (x / (n : ℕ)))).symm
    simp_rw [reindex]
    simpa only [FourierTransform.fourier_fourierInv_eq] using
      MobiusSourceFourierPairing.integral_forward_eq_positiveTheta
        raw measurable atZero even weighted (FourierTransform.fourierInv test)
  have thetaIntegrable : IntegrableOn
      (fun u : ℝ => raw u * coPoissonMuntzThetaNonzero test u) (Ioi 0) := by
    simpa only [FourierTransform.fourier_fourierInv_eq] using
      MobiusSourceFourierPairing.positiveTheta_integrable
        raw measurable atZero even weighted (FourierTransform.fourierInv test)
  rw [burnolRemainderSourceRead_integral]
  calc
    _ = (1 / 2 : ℂ) * ∫ x : ℝ, raw x * coPoissonMuntzScaleRemainder test |x| := by
      congr 1
      apply integral_congr_ae
      filter_upwards [represents] with x hx
      rw [hx]
    _ = ∫ x : ℝ in Ioi 0, raw x * coPoissonMuntzScaleRemainder test |x| :=
      half_integral_even _ (rawMem.integrable_mul kernelMem)
        (fun x => by rw [even, abs_neg])
    _ = ∫ x : ℝ in Ioi 0, raw x * coPoissonMuntzThetaNonzero test x -
        (∫ u : ℝ, test u) * ((x : ℂ)⁻¹ * raw x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [abs_of_pos hx, coPoissonMuntzScaleRemainder_eq test hx]
      simp only [real_smul, Complex.ofReal_inv]
      ring
    _ = (∫ x : ℝ, test x * burnolInnerGapForward raw x) -
        (∫ x : ℝ, test x) * normal := by
      rw [integral_sub thetaIntegrable (reciprocal.const_mul _),
        integral_const_mul, ← thetaRead]
    _ = _ := by
      rw [← integral_mul_const]
      rw [← integral_sub (burnolInnerGapForward_test_integrable raw measurable atZero weighted test)
        (test.integrable.mul_const normal)]
      apply integral_congr_ae
      filter_upwards with x
      exact (mul_sub _ _ _).symm

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

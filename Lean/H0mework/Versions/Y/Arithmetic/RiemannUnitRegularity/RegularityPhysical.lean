import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.Gap
import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.GeneratorStrong
import H0mework.Versions.Y.Arithmetic.MellinProjection.FourierSource
import H0mework.Versions.Y.Arithmetic.MobiusSource.SourceRead

/-! The original strong physical graph generates its ordinary Fourier first moment and absolute integrability. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex Filter FourierTransform MeasureTheory Set
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

private theorem firstMoment_memLp_of_distribution
    (value moment : Lp ℂ 2 (volume : Measure ℝ))
    (generated : TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
      (value : TemperedDistribution ℝ ℂ) = (moment : TemperedDistribution ℝ ℂ)) :
    MemLp (fun x : ℝ => (x : ℂ) * value x) 2 volume := by
  have read : (fun x : ℝ => (x : ℂ) * value x) =ᵐ[volume] moment := by
    apply ae_eq_of_integral_contDiff_smul_eq
    · exact LocallyIntegrable.continuous_mul (by fun_prop)
        ((Lp.memLp value).locallyIntegrable (by norm_num))
    · exact (Lp.memLp moment).locallyIntegrable (by norm_num)
    · intro testReal testSmooth testCompact
      have compactComplex : HasCompactSupport (Complex.ofRealCLM ∘ testReal) :=
        testCompact.comp_left rfl
      let test : SchwartzMap ℝ ℂ := compactComplex.toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp testSmooth)
      have source := congrArg (fun T : TemperedDistribution ℝ ℂ => T test) generated
      rw [TemperedDistribution.smulLeftCLM_apply_apply,
        Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at source
      convert! source using 1
      apply integral_congr_ae
      filter_upwards with x
      · simp only [SchwartzMap.smulLeftCLM_apply (by fun_prop :
          (fun x : ℝ => (x : ℂ)).HasTemperateGrowth), smul_eq_mul]
        change (testReal x : ℂ) * ((x : ℂ) * value x) =
          ((x : ℂ) * (testReal x : ℂ)) * value x
        ring
  exact MemLp.ae_eq read.symm (Lp.memLp moment)

theorem burnolFourier_firstMoment_of_ordinaryDerivative
    (value derivative : Lp ℂ 2 (volume : Measure ℝ))
    (generated : TemperedDistribution.derivCLM ℂ (value : TemperedDistribution ℝ ℂ) =
      (derivative : TemperedDistribution ℝ ℂ)) :
    MemLp (fun x : ℝ => (x : ℂ) * fourierL2 value x) 2 volume := by
  let scale : ℂ := 2 * (Real.pi : ℂ) * Complex.I
  have nonzero : scale ≠ 0 := mul_ne_zero
    (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero
  apply firstMoment_memLp_of_distribution (fourierL2 value)
    (scale⁻¹ • fourierL2 derivative)
  have source := congrArg FourierTransform.fourier generated
  rw [burnolTemperedDerivative_eq_lineOne, TemperedDistribution.fourier_lineDerivOp_eq,
    Lp.fourier_toTemperedDistribution_eq, Lp.fourier_toTemperedDistribution_eq] at source
  simp only [Real.inner_apply, mul_one] at source
  change scale • TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
    (fourierL2 value : TemperedDistribution ℝ ℂ) =
    (fourierL2 derivative : TemperedDistribution ℝ ℂ) at source
  have final := congrArg (fun T : TemperedDistribution ℝ ℂ => scale⁻¹ • T) source
  rw [inv_smul_smul₀ nonzero] at final
  rw [final]
  change scale⁻¹ • (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 derivative)) =
    Lp.toTemperedDistributionCLM ℂ volume 2 (scale⁻¹ • fourierL2 derivative)
  exact (map_smul _ _ _).symm

theorem burnolFourier_firstMoment_of_strongGap
    {value velocity : BurnolL2}
    (strong : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) value)
      velocity 0) (constant : ℂ)
    (gap : ∀ᵐ x ∂volume, x ∈ Icc (-1 / 4 : ℝ) (1 / 4) → value x = constant) :
    MemLp (fun x : ℝ => (x : ℂ) * fourierL2 value x) 2 volume :=
  burnolFourier_firstMoment_of_ordinaryDerivative _ _
    (burnolOrdinaryDerivative_of_eulerGap _ _ constant gap (burnolDilationStrong_eulerDistribution strong))


private theorem integrable_firstMoment {f : ℝ → ℂ}
    (hf : MemLp f 2 volume)
    (hxf : MemLp (fun x : ℝ => (x : ℂ) * f x) 2 volume) :
    Integrable f volume := by
  have weight : MemLp (fun x : ℝ => (1 + ‖x‖)⁻¹) 2 volume := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    simpa [Real.rpow_neg, Real.rpow_two, inv_pow] using
      (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num))
  apply (integrable_norm_iff hf.1).1
  refine ((hf.norm.add hxf.norm).integrable_mul weight).congr ?_
  filter_upwards [] with x
  change (‖f x‖ + ‖(x : ℂ) * f x‖) * (1 + ‖x‖)⁻¹ = ‖f x‖
  rw [norm_mul, Complex.norm_real]
  have hx : 1 + ‖x‖ ≠ 0 := ne_of_gt (by positivity)
  field_simp

theorem burnolPhysicalStrong_firstMoment
    (value : BurnolPaAmbientCarrier) {velocity : BurnolL2}
    (strong : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2)
      (value : BurnolL2)) velocity 0) :
    MemLp (fun x : ℝ => (x : ℂ) * (value : BurnolL2) x) 2 volume := by
  let dual := evenFaceFourierEquiv burnolUnscaledCommonGapRadius value
  have dualStrong := burnolFourierOrbit_hasDerivAt _ _ strong
  have gap := burnolAmbientGap_ae dual
  have globalGap := (ae_restrict_iff'
    (measurableSet_symmetricInterval burnolUnscaledCommonGapRadius)).mp gap
  change ∀ᵐ x ∂volume, x ∈ symmetricInterval burnolUnscaledCommonGapRadius →
    fourierL2 (value : BurnolL2) x =
      burnolConstantGapCoefficient burnolUnscaledCommonGapRadius dual at globalGap
  have moment := burnolFourier_firstMoment_of_strongGap dualStrong
    (burnolConstantGapCoefficient burnolUnscaledCommonGapRadius dual) (by
      simpa only [symmetricInterval, burnolUnscaledCommonGapRadius, neg_div] using globalGap)
  have twice : fourierL2 (fourierL2 (value : BurnolL2)) = value := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp value.2.2
  simpa only [twice] using moment

theorem burnolPhysicalStrong_integrable
    (value : BurnolPaAmbientCarrier) {velocity : BurnolL2}
    (strong : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2)
      (value : BurnolL2)) velocity 0) :
    Integrable (value : BurnolL2) volume :=
  integrable_firstMoment (Lp.memLp (value : BurnolL2))
    (burnolPhysicalStrong_firstMoment value strong)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

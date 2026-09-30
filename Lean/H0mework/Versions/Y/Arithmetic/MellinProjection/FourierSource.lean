import H0mework.Versions.Y.Arithmetic.MellinProjection.Distribution

/-! Fourier-transforming the same distribution produces its canonical coordinate numerator. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set LineDeriv
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

theorem burnolTemperedDerivative_eq_lineOne (source : TemperedDistribution ℝ ℂ) :
    TemperedDistribution.derivCLM ℂ source = ∂_{(1 : ℝ)} source := by
  ext test
  rw [TemperedDistribution.derivCLM_apply_apply,
    TemperedDistribution.lineDerivOp_apply_apply]
  congr 1

theorem burnolGapTailFourier_coordinate_distribution
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    (2 * (Real.pi : ℂ) * Complex.I) •
      TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => x)
        (fourierL2 (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) :
          TemperedDistribution ℝ ℂ) =
      FourierTransform.fourier
        ((star (burnolRadiusMellinGapMoment radius coordinate.value) *
            (((2 * radius : ℝ) : ℂ)⁻¹)) • TemperedDistribution.delta (-radius) +
          ((radius : ℂ) ^ (-star coordinate.value) -
            star (burnolRadiusMellinGapMoment radius coordinate.value) *
              (((2 * radius : ℝ) : ℂ)⁻¹)) • TemperedDistribution.delta radius -
          star coordinate.value •
            (burnolRadiusMellinTailKernelL2 radius positive (coordinate.value + 1)
              (by
                simp only [Complex.add_re, Complex.one_re]
                linarith [coordinate.rightHalf]) : TemperedDistribution ℝ ℂ)) := by
  rw [← burnolGapTail_distribution_derivative radius positive coordinate,
    burnolTemperedDerivative_eq_lineOne,
    TemperedDistribution.fourier_lineDerivOp_eq]
  have actual := Lp.fourier_toTemperedDistribution_eq
    (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate)
  change FourierTransform.fourier
    (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate :
      TemperedDistribution ℝ ℂ) =
    (fourierL2 (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) :
      TemperedDistribution ℝ ℂ) at actual
  rw [actual]
  simp only [Real.inner_apply, mul_one]

theorem burnolMellinTailDerivativeRaw_integrable
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    Integrable (burnolRadiusMellinTailKernelRaw radius (coordinate.value + 1)) := by
  have exponent : (-star (coordinate.value + 1)).re < -1 := by
    simp only [neg_re, Complex.star_def, Complex.conj_re, Complex.add_re, Complex.one_re]
    linarith [coordinate.rightHalf]
  have raw := (integrableOn_Ioi_cpow_of_lt exponent positive).integrable_indicator measurableSet_Ioi
  apply raw.congr
  filter_upwards with x
  unfold burnolRadiusMellinTailKernelRaw
  by_cases inside : x ∈ Ioi radius <;> simp [inside]

def burnolMellinTailDerivativeFourierRaw
    (radius : ℝ) (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) : ℂ :=
  VectorFourier.fourierIntegral 𝐞 volume (innerₗ ℝ)
    (burnolRadiusMellinTailKernelRaw radius (coordinate.value + 1)) frequency

theorem burnolMellinTailDerivativeFourierRaw_continuous
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (burnolMellinTailDerivativeFourierRaw radius coordinate) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by fun_prop) (burnolMellinTailDerivativeRaw_integrable radius positive coordinate)

theorem burnolMellinTailDerivativeFourier_pairing
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    (∫ x : ℝ, FourierTransform.fourier test x *
        burnolRadiusMellinTailKernelRaw radius (coordinate.value + 1) x) =
      ∫ x : ℝ, test x * burnolMellinTailDerivativeFourierRaw radius coordinate x := by
  have source := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := 𝐞) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) Real.continuous_fourierChar (by fun_prop)
    (burnolMellinTailDerivativeRaw_integrable radius positive coordinate) test.integrable
  change (∫ x : ℝ, FourierTransform.fourier test x * _) = _
  rw [flip_innerₗ] at source
  simp only [SchwartzMap.fourier_coe, Real.fourier_eq] at ⊢
  unfold burnolMellinTailDerivativeFourierRaw
  simpa only [VectorFourier.fourierIntegral, innerₗ_apply_apply, smul_eq_mul, mul_comm] using source.symm

def burnolGapTailFourierNumerator
    (radius : ℝ) (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) : ℂ :=
  let c := star (burnolRadiusMellinGapMoment radius coordinate.value) *
    (((2 * radius : ℝ) : ℂ)⁻¹)
  c * (𝐞 (radius * frequency) : ℂ) +
    ((radius : ℂ) ^ (-star coordinate.value) - c) * (𝐞 (-(radius * frequency)) : ℂ) -
      star coordinate.value * burnolMellinTailDerivativeFourierRaw radius coordinate frequency

theorem burnolGapTailFourierNumerator_continuous
    (radius : ℝ) (positive : 0 < radius) (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (burnolGapTailFourierNumerator radius coordinate) := by
  have source := burnolMellinTailDerivativeFourierRaw_continuous radius positive coordinate
  unfold burnolGapTailFourierNumerator
  fun_prop

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

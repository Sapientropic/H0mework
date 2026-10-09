import H0mework.Versions.V2.Arithmetic.MellinProjection.FourierSource

/-! The actual L¹ derivative tail pays the Fourier pairing; no boundary term is removed. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set LineDeriv
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

theorem burnolGapTailFourier_coordinate_pairing
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I) *
      (∫ x : ℝ, test x * ((x : ℂ) *
        fourierL2 (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) x)) =
      (star (burnolRadiusMellinGapMoment radius coordinate.value) *
          (((2 * radius : ℝ) : ℂ)⁻¹)) * FourierTransform.fourier test (-radius) +
        ((radius : ℂ) ^ (-star coordinate.value) -
          star (burnolRadiusMellinGapMoment radius coordinate.value) *
            (((2 * radius : ℝ) : ℂ)⁻¹)) * FourierTransform.fourier test radius -
        star coordinate.value *
          ∫ x : ℝ, test x * burnolMellinTailDerivativeFourierRaw radius coordinate x := by
  have source := congrArg (fun t : TemperedDistribution ℝ ℂ => t test)
    (burnolGapTailFourier_coordinate_distribution radius positive coordinate)
  have growth : (fun x : ℝ => (x : ℂ)).HasTemperateGrowth := by fun_prop
  simp only [smul_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.fourier_apply, add_apply, sub_apply,
    TemperedDistribution.delta_apply, smul_eq_mul] at source
  rw [Lp.toTemperedDistribution_apply, Lp.toTemperedDistribution_apply] at source
  simp only [SchwartzMap.smulLeftCLM_apply_apply growth, smul_eq_mul] at source
  have tailRead :
      (∫ x : ℝ, FourierTransform.fourier test x *
        burnolRadiusMellinTailKernelL2 radius positive (coordinate.value + 1)
          (by simp only [Complex.add_re, Complex.one_re]; linarith [coordinate.rightHalf]) x) =
      ∫ x : ℝ, FourierTransform.fourier test x *
        burnolRadiusMellinTailKernelRaw radius (coordinate.value + 1) x := by
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (burnolRadiusMellinTailKernelRaw_memLp positive (coordinate.value + 1)
        (by simp only [Complex.add_re, Complex.one_re]; linarith [coordinate.rightHalf]))]
      with x raw
    change burnolRadiusMellinTailKernelL2 radius positive (coordinate.value + 1)
      (by simp only [Complex.add_re, Complex.one_re]; linarith [coordinate.rightHalf]) x = _ at raw
    rw [raw]
  rw [tailRead, burnolMellinTailDerivativeFourier_pairing radius positive coordinate test] at source
  convert source using 1
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem burnolGapTailFourier_numerator_pairing
    (radius : ℝ) (positive : 0 < radius)
    (coordinate : BurnolCompletedMellinCoordinate) (test : SchwartzMap ℝ ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I) *
      (∫ x : ℝ, test x * ((x : ℂ) *
        fourierL2 (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) x)) =
      ∫ x : ℝ, test x * burnolGapTailFourierNumerator radius coordinate x := by
  have planeI (c : ℝ) : Integrable (fun x : ℝ => test x * (𝐞 (c * x) : ℂ)) :=
    test.integrable.mul_bdd (c := 1) (by fun_prop)
      (Filter.Eventually.of_forall fun x => (Circle.norm_coe (𝐞 (c * x))).le)
  have tailI : Integrable (fun x : ℝ =>
      test x * burnolMellinTailDerivativeFourierRaw radius coordinate x) :=
    test.integrable.mul_bdd
      (burnolMellinTailDerivativeFourierRaw_continuous radius positive coordinate).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x =>
        VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ x)
  have planeRead (c : ℝ) : (∫ x : ℝ, test x * (𝐞 (c * x) : ℂ)) =
      FourierTransform.fourier test (-c) := by
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq]
    apply integral_congr_ae
    filter_upwards with x
    simp only [mul_neg, neg_neg, Circle.smul_def, smul_eq_mul, mul_comm]
  let c := star (burnolRadiusMellinGapMoment radius coordinate.value) * (((2 * radius : ℝ) : ℂ)⁻¹)
  let d := (radius : ℂ) ^ (-star coordinate.value) - c
  have expand : (fun x : ℝ => test x * burnolGapTailFourierNumerator radius coordinate x) =
      fun x => c * (test x * (𝐞 (radius * x) : ℂ)) +
        d * (test x * (𝐞 ((-radius) * x) : ℂ)) -
          star coordinate.value * (test x * burnolMellinTailDerivativeFourierRaw radius coordinate x) := by
    funext x
    unfold burnolGapTailFourierNumerator
    dsimp only [c, d]
    rw [neg_mul]
    ring
  have splitSub := integral_sub
    (((planeI radius).const_mul c).add ((planeI (-radius)).const_mul d))
    (tailI.const_mul (star coordinate.value))
  simp only [Pi.add_apply] at splitSub
  rw [expand, splitSub,
    integral_add ((planeI radius).const_mul c) ((planeI (-radius)).const_mul d),
    integral_const_mul, integral_const_mul, integral_const_mul,
    planeRead, planeRead, neg_neg]
  exact burnolGapTailFourier_coordinate_pairing radius positive coordinate test

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

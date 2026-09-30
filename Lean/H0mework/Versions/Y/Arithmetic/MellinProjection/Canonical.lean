import H0mework.Versions.Y.Arithmetic.MellinProjection.FourierPairing

/-! Distribution equality generates the actual L² Fourier representative and its nonzero-frequency traces. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex Filter FourierTransform MeasureTheory Set LineDeriv
open scoped ENNReal InnerProductSpace SchwartzMap Topology
noncomputable section

theorem burnolGapTailFourier_coordinate_ae
    (radius : ℝ) (positive : 0 < radius) (coordinate : BurnolCompletedMellinCoordinate) :
    (fun x : ℝ => (2 * (Real.pi : ℂ) * Complex.I) * ((x : ℂ) *
      fourierL2 (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) x)) =ᵐ[
        volume] burnolGapTailFourierNumerator radius coordinate := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · apply LocallyIntegrable.continuous_mul (by fun_prop)
    exact LocallyIntegrable.continuous_mul (by fun_prop)
      ((Lp.memLp (fourierL2
        (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate))).locallyIntegrable
          (by norm_num))
  · exact (burnolGapTailFourierNumerator_continuous radius positive coordinate).locallyIntegrable
  · intro testReal testSmooth testCompact
    have compactComplex : HasCompactSupport (Complex.ofRealCLM ∘ testReal) :=
      testCompact.comp_left rfl
    let test : SchwartzMap ℝ ℂ := compactComplex.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp testSmooth)
    have source := burnolGapTailFourier_numerator_pairing radius positive coordinate test
    calc
      _ = (2 * (Real.pi : ℂ) * Complex.I) *
          ∫ x : ℝ, test x * ((x : ℂ) *
            fourierL2 (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) x) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        change (testReal x : ℂ) * ((2 * (Real.pi : ℂ) * Complex.I) * ((x : ℂ) * _)) =
          (2 * (Real.pi : ℂ) * Complex.I) * ((testReal x : ℂ) * ((x : ℂ) * _))
        ring
      _ = ∫ x : ℝ, test x * burnolGapTailFourierNumerator radius coordinate x := source
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        rfl

def burnolGapTailFourierRaw
    (radius : ℝ) (coordinate : BurnolCompletedMellinCoordinate) (frequency : ℝ) : ℂ :=
  burnolGapTailFourierNumerator radius coordinate frequency /
    (2 * (Real.pi : ℂ) * Complex.I * (frequency : ℂ))

theorem burnolGapTailFourier_ae_canonical
    (radius : ℝ) (positive : 0 < radius) (coordinate : BurnolCompletedMellinCoordinate) :
    (fourierL2 (burnolRadiusAmbientCompletedMellinKernelFormula radius positive coordinate) : ℝ → ℂ)
      =ᵐ[volume] burnolGapTailFourierRaw radius coordinate := by
  have avoidZero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [burnolGapTailFourier_coordinate_ae radius positive coordinate,
    avoidZero] with x source nonzero
  unfold burnolGapTailFourierRaw
  have denominator : 2 * (Real.pi : ℂ) * Complex.I * (x : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr nonzero)
  apply (eq_div_iff denominator).mpr
  rw [← source]
  ring

theorem burnolGapTailFourierRaw_continuousAt
    (radius : ℝ) (positive : 0 < radius) (coordinate : BurnolCompletedMellinCoordinate)
    {frequency : ℝ} (nonzero : frequency ≠ 0) :
    ContinuousAt (burnolGapTailFourierRaw radius coordinate) frequency :=
  (burnolGapTailFourierNumerator_continuous radius positive coordinate).continuousAt.div
    (by fun_prop)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr nonzero))

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

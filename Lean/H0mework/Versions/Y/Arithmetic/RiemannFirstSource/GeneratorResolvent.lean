import H0mework.Versions.Y.Arithmetic.RemainderSource.ResolventBoundary

/-! The full signed source boundary generates the strong derivative of the original L² resolvent orbit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem positiveMellinQuarterRightResolventCharacter_exp (z : ℂ) (h : ℝ) :
    positiveMellinQuarterRightResolventCharacter z h = Complex.exp ((z - 1 / 4) * (h : ℂ)) := by
  unfold positiveMellinQuarterRightResolventCharacter positiveMellinQuarterRightResolventWeight
  congr 1
  rw [Complex.ofReal_neg]
  ring

theorem positiveMellinQuarterRightResolventCharacter_hasDerivAt (z : ℂ) :
    HasDerivAt (positiveMellinQuarterRightResolventCharacter z) (z - 1 / 4) 0 := by
  have realChart : HasDerivAt (fun h : ℝ => (h : ℂ)) 1 0 := by
    convert! (Complex.ofRealCLM.hasFDerivAt (x := (0 : ℝ))).hasDerivAt using 1
  have differentiated := (realChart.const_mul (z - 1 / 4)).cexp
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, one_mul] at differentiated
  have same : positiveMellinQuarterRightResolventCharacter z = fun h : ℝ => Complex.exp ((z - 1 / 4) * (h : ℂ)) := by
    funext h
    exact positiveMellinQuarterRightResolventCharacter_exp z h
  rw [same]
  exact differentiated

theorem burnolMultiplicativeDilation_zero (value : BurnolL2) : burnolMultiplicativeDilation 0 value = value := by
  apply Lp.ext
  filter_upwards [burnolMultiplicativeDilation_coeFn 0 value] with x hx
  simpa only [burnolL2RawNormalizedDilation, zero_div, Real.exp_zero, one_mul,
    Complex.ofReal_one] using hx

theorem burnolDirectRightResolventSignedBoundary_hasDerivAt (z : ℂ) (value : BurnolL2) :
    HasDerivAt (burnolDirectRightResolventSignedBoundary z value) value 0 := by
  have continuous : Continuous (burnolDirectRightResolventIntegrand z value) :=
    (positiveMellinQuarterRightResolventWeight_continuous z).smul
      ((burnolMultiplicativeDilation_stronglyContinuous value).comp (by fun_prop))
  have derivative := intervalIntegral.integral_hasDerivAt_right
    (continuous.intervalIntegrable 0 0) continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous.continuousAt
  convert! derivative using 1
  simp only [burnolDirectRightResolventIntegrand,
    positiveMellinQuarterRightResolventWeight, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    neg_zero, zero_div, burnolMultiplicativeDilation_zero, one_smul]

theorem burnolDirectRightResolventOrbit_hasDerivAt (z : ℂ) (rightQuarter : 1 / 4 < z.re) (value : BurnolL2) :
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2) (burnolDirectRightResolvent z value))
      ((z - 1 / 4) • burnolDirectRightResolvent z value + value) 0 := by
  have generated := (positiveMellinQuarterRightResolventCharacter_hasDerivAt z).smul_const (burnolDirectRightResolvent z value) |>.add
    ((positiveMellinQuarterRightResolventCharacter_hasDerivAt z).smul (burnolDirectRightResolventSignedBoundary_hasDerivAt z value))
  have zeroCharacter : positiveMellinQuarterRightResolventCharacter z 0 = 1 := by
    rw [positiveMellinQuarterRightResolventCharacter_exp]
    simp
  have zeroBoundary : burnolDirectRightResolventSignedBoundary z value 0 = 0 := by
    simp [burnolDirectRightResolventSignedBoundary]
  simp only [zeroCharacter, zeroBoundary, smul_zero, add_zero, one_smul] at generated
  convert! generated using 1
  funext h
  exact (eq_add_of_sub_eq (burnolDirectRightResolvent_sourceBoundary z rightQuarter value h)).trans (add_comm _ _)

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

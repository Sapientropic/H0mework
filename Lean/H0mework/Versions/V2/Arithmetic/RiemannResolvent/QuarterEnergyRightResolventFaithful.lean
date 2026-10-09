import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import H0mework.Versions.V2.Arithmetic.RiemannDivision.QuarterEnergyRightResolventSource
import H0mework.Versions.V2.Arithmetic.SonineCoupling.ModifiedWeakFEPoleSourceEnergy
import H0mework.Versions.V2.Arithmetic.RiemannDivision.GeneratedRiemannXiZeroLocalization

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex MeasureTheory Set Filter
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open ClozelGeneralizedDual
open SourceGeneratedComplexFeaturePerfectification
open scoped Interval

noncomputable section

theorem positiveMellinQuarterRightResolvent_eq_zero_iff
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    (value : PositiveMellinQuarterEnergy) :
    positiveMellinQuarterRightResolvent coordinate value = 0 ↔ value = 0 := by
  constructor
  · intro resolventZero
    let integrand := positiveMellinQuarterRightResolventIntegrand coordinate value
    have boundaryZero (shift : ℝ) (shiftNonnegative : 0 ≤ shift) :
        positiveMellinQuarterRightResolventBoundarySource
          coordinate value shift = 0 := by
      have boundary := positiveMellinQuarterRightResolvent_sourceBoundary
        coordinate rightQuarter value shift shiftNonnegative
      rw [resolventZero, map_zero, smul_zero, sub_zero] at boundary
      have characterNe :
          positiveMellinQuarterRightResolventCharacter coordinate shift ≠ 0 := by
        unfold positiveMellinQuarterRightResolventCharacter
          positiveMellinQuarterRightResolventWeight
        exact Complex.exp_ne_zero _
      exact (smul_eq_zero.mp boundary.symm).resolve_left characterNe
    have intervalZero (shift : ℝ) (shiftPositive : 0 < shift) :
        (∫ base : ℝ in (0 : ℝ)..shift, integrand base) = 0 := by
      rw [intervalIntegral.integral_of_le shiftPositive.le]
      exact boundaryZero shift shiftPositive.le
    let primitive : ℝ → PositiveMellinQuarterEnergy := fun shift =>
      ∫ base : ℝ in (0 : ℝ)..shift, integrand base
    have primitiveLocalZero : primitive =ᶠ[nhds (1 : ℝ)] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)]
        with shift shiftPositive
      exact intervalZero shift shiftPositive
    have primitiveDerivZero : deriv primitive 1 = 0 := by
      rw [Filter.EventuallyEq.deriv_eq primitiveLocalZero]
      simp
    have integrandContinuous : Continuous integrand :=
      positiveMellinQuarterRightResolventIntegrand_continuous coordinate value
    have primitiveDeriv : deriv primitive 1 = integrand 1 := by
      exact intervalIntegral.deriv_integral_right
        (integrandContinuous.intervalIntegrable 0 1)
        integrandContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        integrandContinuous.continuousAt
    have integrandOneZero : integrand 1 = 0 := by
      rw [← primitiveDeriv, primitiveDerivZero]
    change positiveMellinQuarterRightResolventWeight coordinate 1 •
        positiveMellinQuarterEnergyTranslation 1 value = 0 at integrandOneZero
    have weightNe :
        positiveMellinQuarterRightResolventWeight coordinate 1 ≠ 0 := by
      unfold positiveMellinQuarterRightResolventWeight
      exact Complex.exp_ne_zero _
    have translatedZero :
        positiveMellinQuarterEnergyTranslation 1 value = 0 :=
      (smul_eq_zero.mp integrandOneZero).resolve_left weightNe
    apply (positiveMellinQuarterEnergyTranslationIsometry 1).injective
    change positiveMellinQuarterEnergyTranslation 1 value =
      positiveMellinQuarterEnergyTranslation 1 0
    rw [translatedZero, map_zero]
  · intro valueZero
    subst value
    simp [positiveMellinQuarterRightResolvent,
      positiveMellinQuarterRightResolventIntegrand]

theorem positiveMellinQuarterRightResolvent_ne_zero
    (coordinate : ℂ) (rightQuarter : 1 / 4 < coordinate.re)
    {value : PositiveMellinQuarterEnergy} (valueNe : value ≠ 0) :
    positiveMellinQuarterRightResolvent coordinate value ≠ 0 := by
  exact (not_congr
    (positiveMellinQuarterRightResolvent_eq_zero_iff
      coordinate rightQuarter value)).mpr valueNe

/-- The selected modified-WeakFE source produces a genuinely occupied
right resolvent whenever its own exact coordinate is on the right half of
the strip. -/
theorem selectedModifiedWeakFEPole_rightResolvent_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    positiveMellinQuarterRightResolvent
        (selectedCoPoissonMuntzParameter observation)
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation)
          (selectedModifiedWeakFEPoleTraceTest observation nontrivial)) ≠ 0 := by
  apply positiveMellinQuarterRightResolvent_ne_zero
  · unfold selectedCoPoissonMuntzParameter
    rw [Complex.div_re]
    norm_num
    linarith
  · exact selectedModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
      observation nontrivial

/-- The same faithful resolvent producer on the conjugate-Tate sibling. -/
theorem reversalModifiedWeakFEPole_rightResolvent_ne_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (leftHalf : observation.coordinate.re < 1 / 2) :
    positiveMellinQuarterRightResolvent
        (reversalCoPoissonMuntzParameter observation)
        (quarterMellinL2Feature
          (reversalCoPoissonMuntzParameter observation)
          (reversalModifiedWeakFEPoleTraceTest observation nontrivial)) ≠ 0 := by
  apply positiveMellinQuarterRightResolvent_ne_zero
  · unfold reversalCoPoissonMuntzParameter coordinateReversal
    rw [Complex.div_re]
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    norm_num
    linarith
  · exact reversalModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
      observation nontrivial

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

import H0mework.Arithmetic.BurnolCarrier.AdditiveFullEvenL2

/-! # Nonzero Burnol additive state and its remaining Fourier mouth -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex FourierTransform MeasureTheory Set
open scoped ENNReal

noncomputable section

theorem burnolEvenAnnulus_scaled_nonzero_lattice_zero
    {x : ℝ} (nonnegative : 0 ≤ x) (n : {n : ℤ // n ≠ 0}) :
    burnolEvenAnnulusSchwartz (Real.exp x * (n.1 : ℝ)) = 0 := by
  rw [burnolEvenAnnulusSchwartz, add_apply,
    burnolAnnulus_scaled_nonzero_lattice_zero nonnegative n,
    zero_add, burnolAnnulusSchwartzReflection_apply]
  let negativeIndex : {n : ℤ // n ≠ 0} :=
    ⟨-n.1, neg_ne_zero.mpr n.2⟩
  have negativeZero :=
    burnolAnnulus_scaled_nonzero_lattice_zero nonnegative negativeIndex
  simpa only [negativeIndex, Int.cast_neg, Subtype.coe_mk, mul_neg] using
    negativeZero

theorem burnolEvenAnnulusSchwartz_integral_eq_two :
    (∫ x : ℝ, burnolEvenAnnulusSchwartz x) =
      2 * ∫ x : ℝ, burnolAnnulusSchwartz x := by
  have reflectionIntegral :
      (∫ x : ℝ, burnolAnnulusSchwartzReflection x) =
        ∫ x : ℝ, burnolAnnulusSchwartz x := by
    calc
      (∫ x : ℝ, burnolAnnulusSchwartzReflection x) =
          ∫ x : ℝ, burnolAnnulusSchwartz (-x) := by
        apply integral_congr_ae
        exact ae_of_all (volume : Measure ℝ) fun x =>
          burnolAnnulusSchwartzReflection_apply x
      _ = ∫ x : ℝ, burnolAnnulusSchwartz x :=
        integral_neg_eq_self burnolAnnulusSchwartz volume
  rw [burnolEvenAnnulusSchwartz,
    show (∫ x : ℝ,
        (burnolAnnulusSchwartz + burnolAnnulusSchwartzReflection) x) =
      ∫ x : ℝ, burnolAnnulusSchwartz x +
        burnolAnnulusSchwartzReflection x by rfl]
  rw [integral_add burnolAnnulusSchwartz.integrable
      burnolAnnulusSchwartzReflection.integrable,
    reflectionIntegral]
  ring

theorem burnolEvenAnnulusSchwartz_integral_ne_zero :
    (∫ x : ℝ, burnolEvenAnnulusSchwartz x) ≠ 0 := by
  rw [burnolEvenAnnulusSchwartz_integral_eq_two]
  exact mul_ne_zero (by norm_num) burnolAnnulusSchwartz_integral_ne_zero

theorem coPoissonLogOrbitMap_burnolEvenAnnulus_ne_zero
    {x : ℝ} (nonnegative : 0 ≤ x) :
    coPoissonLogOrbitMap burnolEvenAnnulusSchwartz x ≠ 0 := by
  rw [coPoissonLogOrbitMap_nonzero_formula]
  have sumZero : (∑' n : {n : ℤ // n ≠ 0},
      burnolEvenAnnulusSchwartz (Real.exp x * (n.1 : ℝ))) = 0 := by
    rw [show (fun n : {n : ℤ // n ≠ 0} =>
        burnolEvenAnnulusSchwartz (Real.exp x * (n.1 : ℝ))) = 0 by
      funext n
      exact burnolEvenAnnulus_scaled_nonzero_lattice_zero nonnegative n]
    exact tsum_zero
  rw [sumZero, zero_sub]
  exact mul_ne_zero
    (Complex.cpow_ne_zero_iff.mpr <|
      Or.inl (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero x)))
    (neg_ne_zero.mpr <| smul_ne_zero (Real.exp_ne_zero (-x))
      burnolEvenAnnulusSchwartz_integral_ne_zero)

theorem coPoissonLogOrbitEnergyMap_burnolEvenAnnulus_ne_zero :
    coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz ≠ 0 := by
  intro energyZero
  have energyAeZero :
      (coPoissonLogOrbitEnergyMap burnolEvenAnnulusSchwartz : ℝ → ℂ)
        =ᵐ[volume] 0 := Lp.eq_zero_iff_ae_eq_zero.mp energyZero
  have orbitAeZero : coPoissonLogOrbitMap burnolEvenAnnulusSchwartz
      =ᵐ[volume] 0 := by
    filter_upwards [coPoissonLogOrbitEnergyMap_coeFn
      burnolEvenAnnulusSchwartz, energyAeZero] with x hcoe hzero
    exact hcoe.symm.trans hzero
  have intervalMeasure : (volume : Measure ℝ) (Ioo (0 : ℝ) 1) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  obtain ⟨x, location, zero⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    intervalMeasure (ae_restrict_of_ae orbitAeZero)
  exact coPoissonLogOrbitMap_burnolEvenAnnulus_ne_zero location.1.le zero

theorem burnolAdditiveHalfDensityL2_ne_zero :
    burnolAdditiveHalfDensityL2 ≠ 0 := by
  rw [burnolAdditiveHalfDensityL2_eq_reflectedLogOrbit]
  apply smul_ne_zero (by norm_num)
  intro reflectedZero
  apply coPoissonLogOrbitEnergyMap_burnolEvenAnnulus_ne_zero
  apply reflectL2.injective
  simpa using reflectedZero

theorem burnolAdditivePositiveL2_ne_zero : burnolAdditivePositiveL2 ≠ 0 := by
  intro positiveZero
  apply burnolAdditiveHalfDensityL2_ne_zero
  apply norm_eq_zero.mp
  rw [burnolAdditiveHalfDensityL2_norm_eq_positiveL2, positiveZero,
    norm_zero]

theorem burnolAdditiveFullEvenL2_ne_zero : burnolAdditiveFullEvenL2 ≠ 0 := by
  intro fullZero
  have energy := burnolAdditiveFullEvenL2_norm_sq_eq_two_positive
  rw [fullZero, norm_zero] at energy
  have positiveNormZero : ‖burnolAdditivePositiveL2‖ = 0 := by
    nlinarith [norm_nonneg burnolAdditivePositiveL2]
  exact burnolAdditivePositiveL2_ne_zero (norm_eq_zero.mp positiveNormZero)

/-- Same-state frontier capsule: nonzero even `L²` and position landing are
closed; the unscaled radius-`1/4` Fourier-local law remains exact. -/
theorem burnolAdditiveNonzeroPositionLandingAndFourierMouth :
    burnolAdditiveFullEvenL2 ≠ 0 ∧
      burnolAdditiveFullEvenL2 ∈
        locallyConstantFace burnolUnscaledCommonGapRadius ∧
      (burnolAdditiveFullEvenL2 ∈
          evenBurnolClosedFace burnolUnscaledCommonGapRadius ↔
        fourierL2 burnolAdditiveFullEvenL2 ∈
          locallyConstantFace burnolUnscaledCommonGapRadius) :=
  ⟨burnolAdditiveFullEvenL2_ne_zero,
    burnolAdditiveFullEvenL2_mem_unscaledCommonLocallyConstantFace,
    burnolAdditiveFullEvenL2_mem_evenBurnolClosedFace_iff⟩

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

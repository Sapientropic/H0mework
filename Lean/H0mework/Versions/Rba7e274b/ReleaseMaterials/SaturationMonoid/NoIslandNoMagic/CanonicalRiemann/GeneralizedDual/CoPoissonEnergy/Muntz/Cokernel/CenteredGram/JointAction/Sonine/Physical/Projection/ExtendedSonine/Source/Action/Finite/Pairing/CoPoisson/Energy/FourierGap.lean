import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.CountGap
import H0mework.Versions.V2.Arithmetic.RiemannUnitShell.HarmonicRealization

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Energy

open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Topology
open OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson

noncomputable section

theorem step_wave_fourier_half_inner (lower upper : ℝ) (large : (1 / 2 : ℝ) < lower)
    (ordered : lower ≤ upper) (bounded : upper ≤ 4) (test : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2) test = test) (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test (fourierL2 (burnolReciprocalStepNativeWave lower upper)) = 0 := by
  have lowerPositive : 0 < lower := lt_trans (by norm_num) large
  apply half_inner_zero_of_local_constant _ test (-(Real.log (upper / lower) : ℂ)) _ supported mass
  filter_upwards [burnolReciprocalStepFourier_coeFn lower upper (lt_trans (by norm_num) large)
    ordered bounded] with x raw inside
  rw [raw]
  have small : |x| < lower := (abs_le.mpr inside).trans_lt large
  have lowerIndex : ⌊|x| / lower⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one lowerPositive).mpr small)
  have channels : burnolHarmonicStepChannels lower upper x = ∅ := by
    unfold burnolHarmonicStepChannels
    rw [lowerIndex]
    exact Finset.Ioc_eq_empty_of_le (Nat.zero_le _)
  simp only [burnolHarmonicStepWaveRaw, channels, Finset.sum_empty, zero_sub]

theorem weighted_wave_fourier_half_inner (lower upper : ℝ) (f f' : ℝ → ℂ)
    (large : (1 / 2 : ℝ) < lower) (ordered : lower ≤ upper) (bounded : upper ≤ 4)
    (regular : ContinuousOn f' (Icc lower upper)) (test : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2) test = test) (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test (fourierL2 (burnolWeightedReciprocalStepWave lower upper f f')) = 0 := by
  let read : BurnolL2 →L[ℂ] ℂ := (innerSL ℂ test).comp fourierL2.toLinearIsometry.toContinuousLinearMap
  have actual := weighted_wave_read lower upper f f' (lt_trans (by norm_num) large) regular read
  change inner ℂ test (fourierL2 (burnolWeightedReciprocalStepWave lower upper f f')) = _ at actual
  rw [actual]
  change f upper * inner ℂ test (fourierL2 (burnolReciprocalStepNativeWave lower upper)) -
    (∫ u : ℝ in Ioc lower upper, f' u * inner ℂ test (fourierL2 (burnolReciprocalStepNativeWave lower u))) = 0
  rw [step_wave_fourier_half_inner lower upper large ordered bounded test supported mass, mul_zero]
  have integralZero : (∫ u : ℝ in Ioc lower upper,
      f' u * inner ℂ test (fourierL2 (burnolReciprocalStepNativeWave lower u))) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro u inside
    rw [step_wave_fourier_half_inner lower u large inside.1.le (inside.2.trans bounded) test supported mass,
      mul_zero]
  rw [integralZero, sub_self]

theorem bandLower_large (shift : ℝ) (bounded : shift ≤ Real.log 2) : (1 / 2 : ℝ) < bandLower shift := by
  have exponential : 1 / 2 ≤ Real.exp (-shift) := by
    calc
      1 / 2 = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
      _ ≤ Real.exp (-shift) := Real.exp_le_exp.mpr (neg_le_neg bounded)
  unfold bandLower
  linarith

theorem positionWave_fourier_half_inner (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) (test : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2) test = test) (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test (fourierL2 (positionWave coordinate shift)) = 0 :=
  weighted_wave_fourier_half_inner _ _ _ _ (bandLower_large shift bounded)
    (bandLower_le_four shift nonnegative) le_rfl
    ((positionWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) test supported mass

theorem fourierWave_fourier_half_inner (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) (test : BurnolL2)
    (supported : originalPhysicalCutoff (1 / 2) test = test) (mass : (∫ x : ℝ, test x) = 0) :
    inner ℂ test (fourierL2 (fourierWave coordinate shift)) = 0 :=
  weighted_wave_fourier_half_inner _ _ _ _ (bandLower_large shift bounded)
    (bandLower_le_four shift nonnegative) le_rfl
    ((fourierWeight_deriv_continuousOn coordinate shift).mono
      (fun _ inside => (bandLower_pos shift).trans_le inside.1)) test supported mass

end
end OriginalRieszFinitePairing.CoPoisson.Energy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

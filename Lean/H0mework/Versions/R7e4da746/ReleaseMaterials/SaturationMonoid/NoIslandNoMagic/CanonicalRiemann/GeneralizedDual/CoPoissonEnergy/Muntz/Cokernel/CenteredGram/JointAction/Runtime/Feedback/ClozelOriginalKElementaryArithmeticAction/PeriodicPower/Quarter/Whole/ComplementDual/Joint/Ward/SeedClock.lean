import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PositiveUnit

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open scoped InnerProductSpace Topology
open private mean_power from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
local notation "q" => (1 / 4 : ℝ)

def collarLog (r x : ℝ) : ℂ := ((Real.log x - Real.log r : ℝ) : ℂ)

def collarWeight (coordinate : BurnolCompletedMellinCoordinate) (j : Nat) (r x : ℝ) : ℂ :=
  (x : ℂ) ^ (star coordinate.value - 1) * collarLog r x ^ j

def collarClock (coordinate : BurnolCompletedMellinCoordinate) (j : Nat) (r : ℝ) : ℂ :=
  collarLog r q ^ (j + 1) / (j + 1 : ℕ) -
    2 * GapEuler.gapMean q coordinate * ∫ x : ℝ in r..q, collarWeight coordinate j r x

theorem actual_seed_positive (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x) :
    seedRaw coordinate.value x = (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) -
      GapEuler.gapMean q coordinate := by
  rw [seedRaw, powerRaw, abs_of_pos positive, mul_sub, mean_power]

private theorem collarLog_derivative (r t : ℝ) (positive : 0 < t) :
    HasDerivAt (collarLog r) ((t : ℂ)⁻¹) t := by
  change HasDerivAt (fun t : ℝ => ((Real.log t - Real.log r : ℝ) : ℂ)) ((t : ℂ)⁻¹) t
  convert! ((Real.hasDerivAt_log positive.ne').sub_const (Real.log r)).ofReal_comp using 1
  simp only [Complex.ofReal_inv]

private theorem collar_log_integral (j : Nat) (r : ℝ) (positive : 0 < r) (ordered : r ≤ q) :
    (∫ x : ℝ in r..q, (x : ℂ)⁻¹ * collarLog r x ^ j) =
      collarLog r q ^ (j + 1) / (j + 1 : ℕ) := by
  have regular : ContinuousOn (fun x : ℝ => (x : ℂ)⁻¹ * collarLog r x ^ j) (Icc r q) := by
    have logarithm : ContinuousOn (collarLog r) (Icc r q) :=
      (Complex.continuous_ofReal.comp_continuousOn
        ((Real.continuousOn_log.mono (fun x inside => (positive.trans_le inside.1).ne')).sub continuousOn_const))
    exact (Complex.continuous_ofReal.continuousOn.inv₀ (fun x inside =>
      Complex.ofReal_ne_zero.mpr (positive.trans_le inside.1).ne')).mul (logarithm.pow j)
  have derivative (t : ℝ) (inside : t ∈ Icc r q) :
      HasDerivAt (fun x : ℝ => collarLog r x ^ (j + 1) / (j + 1 : ℕ))
        ((t : ℂ)⁻¹ * collarLog r t ^ j) t := by
    convert! ((collarLog_derivative r t (positive.trans_le inside.1)).pow (j + 1)).div_const
      ((j + 1 : ℕ) : ℂ) using 1
    simp only [Nat.add_sub_cancel]
    have nonzero : ((j + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    field_simp [nonzero]
  have evaluated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := r) (b := q) (fun t inside => derivative t (by simpa only [uIcc_of_le ordered] using inside))
    (regular.intervalIntegrable_of_Icc ordered)
  simpa only [collarLog, sub_self, Complex.ofReal_zero, zero_pow (Nat.succ_ne_zero j),
    zero_div, sub_zero] using evaluated

theorem actual_seed_collar_clock (coordinate : BurnolCompletedMellinCoordinate) (j : Nat) (r : ℝ)
    (positive : 0 < r) (ordered : r ≤ q) :
    2 * (∫ x : ℝ in r..q, collarWeight coordinate j r x * seedRaw coordinate.value x) =
      collarClock coordinate j r := by
  have logarithm : ContinuousOn (collarLog r) (Icc r q) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((Real.continuousOn_log.mono (fun x inside => (positive.trans_le inside.1).ne')).sub continuousOn_const)
  have regular : ContinuousOn (collarWeight coordinate j r) (Icc r q) := by
    have powerContinuous : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (star coordinate.value - 1)) (Icc r q) := by
      intro x inside
      exact (continuousAt_ofReal_cpow_const x _ (Or.inr (positive.trans_le inside.1).ne')).continuousWithinAt
    exact powerContinuous.mul (logarithm.pow j)
  have first : IntervalIntegrable (fun x : ℝ => (x : ℂ)⁻¹ * collarLog r x ^ j) volume r q := by
    exact ((Complex.continuous_ofReal.continuousOn.inv₀ (fun x inside =>
      Complex.ofReal_ne_zero.mpr (positive.trans_le inside.1).ne')).mul
      (logarithm.pow j)).intervalIntegrable_of_Icc ordered
  have second : IntervalIntegrable (collarWeight coordinate j r) volume r q :=
    regular.intervalIntegrable_of_Icc ordered
  have source : (∫ x : ℝ in r..q, collarWeight coordinate j r x * seedRaw coordinate.value x) =
      ∫ x : ℝ in r..q, (1 / 2 : ℂ) * ((x : ℂ)⁻¹ * collarLog r x ^ j) -
        GapEuler.gapMean q coordinate * collarWeight coordinate j r x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x inside
    rw [uIoc_of_le ordered] at inside
    have xPositive := positive.trans inside.1
    have power : (x : ℂ) ^ (star coordinate.value - 1) * (x : ℂ) ^ (-star coordinate.value) = (x : ℂ)⁻¹ := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr xPositive.ne'),
        show star coordinate.value - 1 + -star coordinate.value = (-1 : ℂ) by ring,
        Complex.cpow_neg_one]
    rw [actual_seed_positive coordinate x xPositive]
    unfold collarWeight
    linear_combination collarLog r x ^ j / 2 * power
  rw [source, intervalIntegral.integral_sub (first.const_mul _) (second.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    collar_log_integral j r positive ordered]
  unfold collarClock
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

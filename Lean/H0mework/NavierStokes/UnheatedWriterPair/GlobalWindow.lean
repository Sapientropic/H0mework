import H0mework.NavierStokes.UnheatedWriterPair.GlobalIntegral
import H0mework.NavierStokes.UnheatedWriterPair.WindowControl
import H0mework.NavierStokes.SourceUnheated.WindowJensen

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnheatedPairGlobalWindow

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedStressPairEvolution NativeUnheatedPairGlobalEvolution NativeUnheatedIntegralBilinear

noncomputable section
variable {nu : Viscosity}

theorem kernel_ac (order : ℕ) (observation clockOrigin a b : ℝ) :
    AbsolutelyContinuousOnInterval (kernelWeight order observation clockOrigin) a b := by
  have integrable := (kernelWeight_continuous (order+1) observation clockOrigin).neg.intervalIntegrable (μ := volume) a b
  apply written_ac _ _ integrable
  intro x _ y _
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time _ => kernelWeight_hasDerivAt order observation clockOrigin time)
    ((kernelWeight_continuous (order+1) observation clockOrigin).neg.intervalIntegrable x y)).symm

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (order derivative : ℕ)
    (observation clockOrigin a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b)
    (wave : IntegerWavevector) (output input : Coordinate) :
    kernelWeight derivative observation clockOrigin b • sourcePair seed (order+1) b wave output input -
      kernelWeight derivative observation clockOrigin a • sourcePair seed (order+1) a wave output input =
      (∫ time in a..b, kernelWeight derivative observation clockOrigin time • sourceTriple seed order time wave output input) -
      (∫ time in a..b, kernelWeight derivative observation clockOrigin time • sourcePair seed order time wave output input) -
      (∫ time in a..b, kernelWeight (derivative+1) observation clockOrigin time • sourcePair seed (order+1) time wave output input) := by
  have interval : uIcc a b ⊆ Icc 0 (max a b) := fun _ inside => ⟨(le_min a0 b0).trans inside.1, inside.2⟩
  have quadratic (r n : ℕ) : IntervalIntegrable (fun time => kernelWeight n observation clockOrigin time •
      sourcePair seed r time wave output input) volume a b := by
    have paid : IntegrableOn (fun time => sourcePair seed r time wave output input) (Icc 0 (max a b)) :=
      sourcePair_integrable seed r (max a b) wave output input
    exact (paid.mono_set interval).intervalIntegrable.continuousOn_smul (kernelWeight_continuous n observation clockOrigin).continuousOn
  have cubic : IntervalIntegrable (fun time => kernelWeight derivative observation clockOrigin time •
      sourceTriple seed order time wave output input) volume a b := by
    have paid : IntegrableOn (fun time => sourceTriple seed order time wave output input) (Icc 0 (max a b)) :=
      sourceTriple_integrable seed order (max a b) (a0.trans (le_max_left _ _)) wave output input
    exact (paid.mono_set interval).intervalIntegrable.continuousOn_smul (kernelWeight_continuous derivative observation clockOrigin).continuousOn
  have written := integral_of_ac_derivative
    (fun time => kernelWeight derivative observation clockOrigin time • sourcePair seed (order+1) time wave output input)
    (fun time => kernelWeight derivative observation clockOrigin time • sourceTriple seed order time wave output input -
      kernelWeight derivative observation clockOrigin time • sourcePair seed order time wave output input -
      kernelWeight (derivative+1) observation clockOrigin time • sourcePair seed (order+1) time wave output input)
    ((kernel_ac derivative observation clockOrigin a b).smul (sourcePair_ac seed order a b a0 b0 wave output input))
    ((cubic.sub (quadratic order derivative)).sub (quadratic (order+1) (derivative+1))) (by
      filter_upwards [sourcePair_hasDerivAt_ae seed order wave output input, volume.ae_ne (0 : ℝ)] with time derivativeAt nonzero
      intro inside
      have positive := lt_of_le_of_ne ((le_min a0 b0).trans inside.1) (Ne.symm nonzero)
      have actual := (kernelWeight_hasDerivAt derivative observation clockOrigin time).smul (derivativeAt positive)
      convert! actual using 1
      simp only [neg_smul, smul_sub, Complex.real_smul]
      ring)
  rwa [intervalIntegral.integral_sub (cubic.sub (quadratic order derivative)) (quadratic (order+1) (derivative+1)),
    intervalIntegral.integral_sub cubic (quadratic order derivative)] at written

theorem kernelJet_left_zero (order : ℕ) : NativeForwardWindowJets.kernelJet order (-2) = 0 := by
  have inside : Iio (-2 : ℝ) ⊆ {time | NativeForwardWindowJets.kernelJet order time = 0} := by
    intro time before
    change time < -2 at before
    by_contra nonzero
    have support := NativeUnheatedWindowJensen.kernel_support order time nonzero
    linarith [support.1]
  have closed : IsClosed {time | NativeForwardWindowJets.kernelJet order time = 0} := isClosed_eq (NativeForwardWindowJets.kernelJet_smooth order).continuous continuous_const
  have contained := closure_minimal inside closed
  rw [closure_Iio] at contained
  exact contained (show (-2 : ℝ) ∈ Iic (-2) by simp)

theorem kernelJet_right_zero (order : ℕ) : NativeForwardWindowJets.kernelJet order (-1) = 0 := by
  have inside : Ioi (-1 : ℝ) ⊆ {time | NativeForwardWindowJets.kernelJet order time = 0} := by
    intro time after
    change -1 < time at after
    by_contra nonzero
    have support := NativeUnheatedWindowJensen.kernel_support order time nonzero
    linarith [support.2]
  have closed : IsClosed {time | NativeForwardWindowJets.kernelJet order time = 0} := isClosed_eq (NativeForwardWindowJets.kernelJet_smooth order).continuous continuous_const
  have contained := closure_minimal inside closed
  rw [closure_Ioi] at contained
  exact contained (show (-1 : ℝ) ∈ Ici (-1) by simp)

theorem tail_integral (seed : GeneratedWholeRestartCurrent nu) (derivative order : ℕ) (observation : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) :
    NativeUnheatedPairWindowTail.tail seed derivative order observation wave output input =
      ∫ time in observation+1..observation+2, kernelWeight derivative observation 0 time • sourcePair seed order time wave output input := by
  have supported : (∫ shift : ℝ, NativeForwardWindowJets.kernelJet derivative shift • sourcePair seed order (observation-shift) wave output input) =
      ∫ shift in Icc (-2 : ℝ) (-1), NativeForwardWindowJets.kernelJet derivative shift • sourcePair seed order (observation-shift) wave output input := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro shift
    by_cases inside : shift ∈ Icc (-2 : ℝ) (-1)
    · rw [indicator_of_mem inside]
    · rw [indicator_of_notMem inside]
      have zero : NativeForwardWindowJets.kernelJet derivative shift = 0 := by
        by_contra nonzero
        exact inside (NativeUnheatedWindowJensen.kernel_support derivative shift nonzero)
      change NativeForwardWindowJets.kernelJet derivative shift • sourcePair seed order (observation-shift) wave output input = 0
      rw [zero, zero_smul]
  change (∫ shift : ℝ, NativeForwardWindowJets.kernelJet derivative shift • sourcePair seed order (observation-shift) wave output input) = _
  rw [supported, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ -1)]
  have changed := intervalIntegral.integral_comp_sub_left
    (f := fun time => kernelWeight derivative observation 0 time • sourcePair seed order time wave output input)
    (a := -2) (b := -1) observation
  simpa only [kernelWeight, zero_add, sub_sub_cancel, sub_neg_eq_add] using! changed

def tripleWindow (seed : GeneratedWholeRestartCurrent nu) (derivative order : ℕ) (observation : ℝ)
    (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  ∫ time in observation+1..observation+2, kernelWeight derivative observation 0 time • sourceTriple seed order time wave output input

theorem step (seed : GeneratedWholeRestartCurrent nu) (derivative order : ℕ) (observation : ℝ) (valid : -1 ≤ observation) :
    NativeUnheatedPairWindowTail.tail seed derivative order observation =
      tripleWindow seed derivative order observation - NativeUnheatedPairWindowTail.tail seed (derivative+1) (order+1) observation := by
  funext wave output input
  have written := weighted_write seed order derivative observation 0 (observation+1) (observation+2)
    (by linarith) (by linarith) wave output input
  have left : kernelWeight derivative observation 0 (observation+1) = 0 := by
    simp only [kernelWeight, zero_add, show observation-(observation+1) = -1 by ring, kernelJet_right_zero]
  have right : kernelWeight derivative observation 0 (observation+2) = 0 := by
    simp only [kernelWeight, zero_add, show observation-(observation+2) = -2 by ring, kernelJet_left_zero]
  simp only [left, right, zero_smul, sub_self] at written
  simp only [Pi.sub_apply, tripleWindow, tail_integral]
  linear_combination written

theorem expansion (seed : GeneratedWholeRestartCurrent nu) (derivative depth : ℕ) (observation : ℝ) (valid : -1 ≤ observation) :
    NativeUnheatedPairWindowTail.tail seed derivative 0 observation =
      (∑ order ∈ Finset.range depth, (-1 : ℝ)^order • tripleWindow seed (derivative+order) order observation) +
      (-1 : ℝ)^depth • NativeUnheatedPairWindowTail.tail seed (derivative+depth) depth observation := by
  induction depth with
  | zero => simp
  | succ depth previous =>
      rw [Finset.sum_range_succ, previous, step seed (derivative+depth) depth observation valid,
        smul_sub, pow_succ, mul_smul, neg_one_smul, smul_neg, ← Nat.add_assoc derivative depth 1]
      abel

theorem original_stress_expansion (seed : GeneratedWholeRestartCurrent nu) (derivative depth : ℕ) (observation : ℝ) (valid : -1 ≤ observation) :
    NativeCompleteStressCarrier.read (NativeForwardWindowJets.jet seed derivative observation).snd =
      (∑ order ∈ Finset.range depth, (-1 : ℝ)^order • tripleWindow seed (derivative+order) order observation) +
      (-1 : ℝ)^depth • NativeUnheatedPairWindowTail.tail seed (derivative+depth) depth observation := by
  rw [← NativeUnheatedPairWindowTail.tail_zero]
  exact expansion seed derivative depth observation valid

end
end SaturationMonoid.NavierStokes.NativeUnheatedPairGlobalWindow

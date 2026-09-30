import H0mework.NavierStokes.WindowEnergyTraceOperator.Time
import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTimeComparison
open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWindowTraceOperator (test)
noncomputable section
variable {nu : Viscosity}

private theorem ordered_bound (f f' : ℝ → ℝ) (C a b : ℝ) (ordered : a≤b)
    (derivative : ∀ t,HasDerivAt f (f' t) t) (bound : ∀ t∈Icc a b,|f' t|≤C*|f t|) :
    |f b|≤|f a| * Real.exp (C*(b-a)) := by
  have continuous : Continuous f := continuous_iff_continuousAt.mpr (fun t => (derivative t).continuousAt)
  have control := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (f' := f')
    (δ := ‖f a‖) (K := C) (ε := 0) continuous.continuousOn
    (fun t _ => (derivative t).hasDerivWithinAt) le_rfl
    (fun t inside => by simpa only [Real.norm_eq_abs,add_zero] using bound t ⟨inside.1,inside.2.le⟩)
    b ⟨ordered,le_rfl⟩
  simpa only [gronwallBound_ε0,Real.norm_eq_abs] using control

private theorem absolute_comparison (f f' : ℝ → ℝ) (C H : ℝ)
    (derivative : ∀ t,HasDerivAt f (f' t) t) (bound : ∀ t∈Icc 0 H,|f' t|≤C*|f t|)
    (s t : ℝ) (hs : s∈Icc 0 H) (ht : t∈Icc 0 H) : |f t|≤Real.exp (C*|t-s|)*|f s| := by
  by_cases order : s≤t
  · have paid := ordered_bound f f' C s t order derivative (fun x hx => bound x ⟨hs.1.trans hx.1,hx.2.trans ht.2⟩)
    simpa only [abs_of_nonneg (sub_nonneg.mpr order),mul_comm] using paid
  · have derivative' (x : ℝ) : HasDerivAt (fun r => f (-r)) (-f' (-x)) x := by
      convert! (derivative (-x)).comp x (hasDerivAt_neg x) using 1
      ring
    have paid := ordered_bound (fun r => f (-r)) (fun r => -f' (-r)) C (-s) (-t) (by linarith) derivative'
      (fun x hx => by
        simpa only [abs_neg] using bound (-x) ⟨by linarith [ht.1,hx.2],by linarith [hs.2,hx.1]⟩)
    simpa only [neg_neg,abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge order)),neg_sub,neg_sub_neg,mul_comm] using paid

theorem source_form_comparison (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius,∀ M : Finset IntegerWavevector,
      0∉M →FiniteModeNegClosed M →∀ s∈Icc 0 horizon,∀ t∈Icc 0 horizon,∀ v : physicalSpace M,
        pairing M v (test seed t M M (integerWaveFrequencyCube outerRadius) radius v)≤
          Real.exp (C*|t-s|)*pairing M v (test seed s M M (integerWaveFrequencyCube outerRadius) radius v) := by
  obtain ⟨temporal,C,C0,paid⟩ := NativeWindowTraceOperatorTime.source_time_bound seed horizon nonnegative 1
  obtain ⟨positive,coercive⟩ := NativeWindowTraceOperator.source_coercivity seed horizon nonnegative
  refine ⟨max temporal positive,C,C0,fun radius above outerRadius M zero closed s hs t ht v => ?_⟩
  let F:=integerWaveFrequencyCube outerRadius
  let E (time : ℝ):=pairing M v (test seed time M M F radius v)
  have energyNonnegative (time : ℝ) (inside : time∈Icc 0 horizon) : 0≤E time := by
    have mass : 0≤pairing M v v := by
      change (0 : ℝ) ≤ inner ℝ (coefficients M v) (coefficients M v)
      exact real_inner_self_nonneg
    have gradient : 0≤curlPair M v.1 v.1 := by
      unfold curlPair
      apply Finset.sum_nonneg
      intro wave _
      rw [complexCoordinateRealInner_self]
      exact complexCoordinateVectorNormSq_nonneg _
    exact (add_nonneg mass (mul_nonneg (by positivity [nu.coeff_pos]) gradient)).trans
      (coercive radius ((le_max_right _ _).trans above) M F zero closed (NativeWindowFiniteGramFourier.cube_closed outerRadius) time inside v)
  have estimate := absolute_comparison E (fun time => NativeWindowTraceOperatorTime.quadraticJet seed M F radius 1 time v)
    C horizon (fun time => NativeWindowTraceOperatorTime.actual_hasDerivAt seed M F radius time v)
    (fun time inside => (paid radius ((le_max_left _ _).trans above) outerRadius M zero closed time inside v).trans
      (mul_le_mul_of_nonneg_left (le_abs_self _) C0)) s t hs ht
  rw [abs_of_nonneg (energyNonnegative s hs),abs_of_nonneg (energyNonnegative t ht)] at estimate
  exact estimate

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTimeComparison

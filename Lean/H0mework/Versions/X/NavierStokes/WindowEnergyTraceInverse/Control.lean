import H0mework.Versions.X.NavierStokes.WindowEnergyTraceInverse.Write
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceClock.ClockInverse

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceDualEvolution
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativePhysicalFourier NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeCommonAdvectorAction
open NativeWindowTraceOperatorTime (quadraticJet)
open NativeWindowTraceAdjoint (propagated response responseRate)
noncomputable section
variable {nu : Viscosity}

theorem source_control (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius M,∀ time∈Icc 0 horizon,
      (mass seed M (integerWaveFrequencyCube outerRadius) radius time).IsInvertible ∧∀ w,
        (0≤energy seed M (integerWaveFrequencyCube outerRadius) radius time w) ∧
        pairing (modes M) (lifted seed M (integerWaveFrequencyCube outerRadius) radius time w)
          (lifted seed M (integerWaveFrequencyCube outerRadius) radius time w)+
            (nu.coeff/2)*curlPair (modes M) (lifted seed M (integerWaveFrequencyCube outerRadius) radius time w).1
              (lifted seed M (integerWaveFrequencyCube outerRadius) radius time w).1≤
                energy seed M (integerWaveFrequencyCube outerRadius) radius time w ∧
        |quadraticJet seed (modes M) (integerWaveFrequencyCube outerRadius) radius 1 time
          (lifted seed M (integerWaveFrequencyCube outerRadius) radius time w)|≤
            C*energy seed M (integerWaveFrequencyCube outerRadius) radius time w := by
  obtain ⟨inverseLow,inverted⟩ := source_invertible seed horizon nonnegative
  obtain ⟨timeLow,C,C0,paid⟩ := NativeWindowTraceOperatorTime.source_time_bound seed horizon nonnegative 1
  obtain ⟨massLow,positive⟩ := NativeWindowTraceOperator.source_coercivity seed horizon nonnegative
  refine ⟨max inverseLow (max timeLow massLow),C,C0,fun radius above outerRadius M time inside => ?_⟩
  let F:=integerWaveFrequencyCube outerRadius
  have actual:=inverted radius ((le_max_left _ _).trans above) M F (NativeWindowFiniteGramFourier.cube_closed outerRadius) time inside
  refine ⟨actual,fun w => ?_⟩
  let z:=lifted seed M F radius time w
  have restore:NativeWindowTraceOperator.test seed time (modes M) (modes M) F radius z=w := actual.self_apply_inverse _
  have positiveCost:=positive radius ((le_max_right _ _).trans ((le_max_right _ _).trans above))
    (modes M) F (modes_zero M) (modes_closed M) (NativeWindowFiniteGramFourier.cube_closed outerRadius) time inside z
  rw [restore] at positiveCost
  have cost:=paid radius ((le_max_left _ _).trans ((le_max_right _ _).trans above)) outerRadius (modes M)
    (modes_zero M) (modes_closed M) time inside z
  rw [restore] at cost
  have basic:0≤pairing (modes M) z z := by
    change (0 : ℝ) ≤ inner ℝ (coefficients (modes M) z) (coefficients (modes M) z)
    exact real_inner_self_nonneg
  have gradient:0≤curlPair (modes M) z.1 z.1 := by
    unfold curlPair
    apply Finset.sum_nonneg
    intro k _
    rw [complexCoordinateRealInner_self]
    exact complexCoordinateVectorNormSq_nonneg _
  refine ⟨?_,positiveCost,cost⟩
  exact (add_nonneg basic (mul_nonneg (by positivity [nu.coeff_pos]) gradient)).trans positiveCost

theorem transported_source_gate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius observation M,∀ start finish (ordered : start≤finish),
      0 ≤ start →finish≤horizon →∀ time∈Ioo start finish,
      let F:=integerWaveFrequencyCube outerRadius
      let w:=propagated seed observation M F radius start finish ordered
      let z:=lifted seed M F radius time (w time)
      |deriv (fun t => energy seed M F radius t (w t)) time+lyapunov seed M F radius time z|≤
        C*energy seed M F radius time (w time) := by
  obtain ⟨low,C,C0,paid⟩ := source_control seed horizon nonnegative
  refine ⟨low,C,C0,fun radius above outerRadius observation M start finish ordered start0 finishH time inside => ?_⟩
  dsimp only
  have clock:time∈Ioo 0 horizon := ⟨start0.trans_lt inside.1,inside.2.trans_le finishH⟩
  have generated:=fun t ht => (paid radius above outerRadius M t ht).1
  have derivative:=transported_energy_derivative seed observation M (integerWaveFrequencyCube outerRadius) radius
    start finish ordered horizon generated time clock inside
  rw [derivative.deriv]
  have cost:=(paid radius above outerRadius M time (Ioo_subset_Icc_self clock)).2
    (propagated seed observation M (integerWaveFrequencyCube outerRadius) radius start finish ordered time)
  simpa only [sub_add_cancel,abs_neg] using cost.2.2

theorem response_source_gate (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius observation M,∀ start finish (ordered : start≤finish),
      0 ≤ start →finish≤horizon →∀ᵐ time : ℝ,time∈Ioo start finish →
      let F:=integerWaveFrequencyCube outerRadius
      let w:=response seed observation M F radius start finish ordered
      let z:=lifted seed M F radius time (w time)
      |deriv (fun t => energy seed M F radius t (w t)) time+lyapunov seed M F radius time z-
        2*pairing (modes M) z (responseRate seed observation M F radius time)|≤C*energy seed M F radius time (w time) := by
  obtain ⟨low,C,C0,paid⟩ := source_control seed horizon nonnegative
  refine ⟨low,C,C0,fun radius above outerRadius observation M start finish ordered start0 finishH => ?_⟩
  have generated:=fun t ht => (paid radius above outerRadius M t ht).1
  filter_upwards [response_energy_derivative_ae seed observation M (integerWaveFrequencyCube outerRadius) radius
    start finish ordered start0 horizon generated] with time derivative inside
  dsimp only
  have clock:time∈Ioo 0 horizon := ⟨start0.trans_lt inside.1,inside.2.trans_le finishH⟩
  rw [(derivative clock inside).deriv]
  have cost:=(paid radius above outerRadius M time (Ioo_subset_Icc_self clock)).2
    (response seed observation M (integerWaveFrequencyCube outerRadius) radius start finish ordered time)
  convert! cost.2.2 using 1
  rw [show ∀ a b c : ℝ,(-a-b+c)+b-c= -a from fun _ _ _ => by ring,abs_neg]

theorem source_clock_comparison (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧ ∀ radius≥low,∀ outerRadius M,∀ s∈Icc 0 horizon,∀ t∈Icc 0 horizon,∀ w,
      energy seed M (integerWaveFrequencyCube outerRadius) radius t w≤
        Real.exp (C*|t-s|)*energy seed M (integerWaveFrequencyCube outerRadius) radius s w := by
  obtain ⟨inverseLow,inverted⟩ := source_invertible seed horizon nonnegative
  obtain ⟨clockLow,C,C0,paid⟩ := NativeWindowTraceInverseComparison.source_actual_inverse_comparison seed horizon nonnegative
  refine ⟨max inverseLow clockLow,C,C0,fun radius above outerRadius M s hs t ht w => ?_⟩
  have left:=inverted radius ((le_max_left _ _).trans above) M (integerWaveFrequencyCube outerRadius)
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) s hs
  have right:=inverted radius ((le_max_left _ _).trans above) M (integerWaveFrequencyCube outerRadius)
    (NativeWindowFiniteGramFourier.cube_closed outerRadius) t ht
  exact paid radius ((le_max_right _ _).trans above) outerRadius (modes M) (modes_zero M) (modes_closed M) s hs t ht
    (inverse seed M (integerWaveFrequencyCube outerRadius) radius s).toLinearMap
    (inverse seed M (integerWaveFrequencyCube outerRadius) radius t).toLinearMap
    (fun v => left.self_apply_inverse v) (fun v => right.self_apply_inverse v) w

end
end SaturationMonoid.NavierStokes.NativeWindowTraceDualEvolution

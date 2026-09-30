import H0mework.NavierStokes.WindowEnergyTraceInverse.Control

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceDualEvolution
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint NativeUnheatedIntegralBilinear
open NativeWindowTraceOperatorTime (quadraticJet)
open NativeWindowTraceAdjoint (propagated response responseRate)
noncomputable section
variable {nu : Viscosity}

private theorem product_ac {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {x : ℝ →E} {y : ℝ →F} {a b : ℝ} (first : AbsolutelyContinuousOnInterval x a b) (last : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval (fun t => (x t,y t)) a b := by
  unfold AbsolutelyContinuousOnInterval at first last ⊢
  apply squeeze_zero' (Eventually.of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg) _ (by simpa using first.add last)
  filter_upwards with intervals
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [Prod.dist_eq]
  exact max_le (le_add_of_nonneg_right dist_nonneg) (le_add_of_nonneg_left dist_nonneg)

private theorem apply_ac {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {A : ℝ →E →L[ℝ] E} {x : ℝ →E} {a b : ℝ} (operator : AbsolutelyContinuousOnInterval A a b)
    (input : AbsolutelyContinuousOnInterval x a b) : AbsolutelyContinuousOnInterval (fun t => A t (x t)) a b := by
  let B : ((E →L[ℝ] E)×E) →L[ℝ] ((E →L[ℝ] E)×E) →L[ℝ] E :=
    (ContinuousLinearMap.apply ℝ E).bilinearComp (ContinuousLinearMap.snd ℝ (E →L[ℝ] E) E)
      (ContinuousLinearMap.fst ℝ (E →L[ℝ] E) E)
  have read (x y : (E →L[ℝ] E)×E) : B x y=y.1 x.2 := rfl
  have generated:=diagonal_ac B (product_ac operator input)
  simpa only [read] using! generated

private theorem pair_ac (M : ℕ) {x y : ℝ →physicalSpace (modes M)} {a b : ℝ}
    (first : AbsolutelyContinuousOnInterval x a b) (last : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval (fun t => pairing (modes M) (x t) (y t)) a b := by
  let coefficient:=LinearMap.toContinuousLinearMap (coefficients (modes M))
  let B:=((innerSL ℝ).bilinearComp coefficient coefficient).bilinearComp
    (ContinuousLinearMap.fst ℝ (physicalSpace (modes M)) (physicalSpace (modes M)))
    (ContinuousLinearMap.snd ℝ (physicalSpace (modes M)) (physicalSpace (modes M)))
  have read (u v : physicalSpace (modes M)×physicalSpace (modes M)) : B u v=pairing (modes M) u.1 v.2 := rfl
  have generated:=diagonal_ac B (product_ac first last)
  simpa only [read] using! generated

theorem energy_ac (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (horizon a b : ℝ) (inside : uIcc a b⊆Icc 0 horizon)
    (generated : ∀ t∈Icc 0 horizon,(mass seed M F radius t).IsInvertible)
    {w : ℝ →physicalSpace (modes M)} (actual : AbsolutelyContinuousOnInterval w a b) :
    AbsolutelyContinuousOnInterval (fun t => energy seed M F radius t (w t)) a b := by
  have regular:ContDiffOn ℝ 1 (inverse seed M F radius) (uIcc a b) := by
    intro t ht
    exact ((generated t (inside ht)).contDiffAt_map_inverse.comp t
      (mass_contDiff seed M F radius).contDiffAt).contDiffWithinAt
  exact pair_ac M (apply_ac regular.absolutelyContinuousOnInterval actual) actual

def transportedRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ) : ℝ :=
  let z:=lifted seed M F radius time (propagated seed observation M F radius start finish ordered time);
  -quadraticJet seed (modes M) F radius 1 time z-lyapunov seed M F radius time z

def respondingRate (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ) (F : Finset IntegerWavevector)
    (radius : ℕ) (start finish : ℝ) (ordered : start≤finish) (time : ℝ) : ℝ :=
  let z:=lifted seed M F radius time (response seed observation M F radius start finish ordered time);
  -quadraticJet seed (modes M) F radius 1 time z-lyapunov seed M F radius time z+
    2*pairing (modes M) z (responseRate seed observation M F radius time)

theorem transported_source_write (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F,FiniteModeNegClosed F →∀ observation start finish (ordered : start≤finish),
      0 ≤ start →finish≤horizon →
      IntervalIntegrable (transportedRate seed observation M F radius start finish ordered) volume start finish ∧
      energy seed M F radius finish (propagated seed observation M F radius start finish ordered finish)-
        energy seed M F radius start (propagated seed observation M F radius start finish ordered start)=
          ∫t in start..finish,transportedRate seed observation M F radius start finish ordered t := by
  obtain ⟨low,paid⟩ := source_invertible seed horizon nonnegative
  refine ⟨low,fun radius above M F closed observation start finish ordered start0 finishH => ?_⟩
  have generated:=paid radius above M F closed
  have inside:uIcc start finish⊆Icc 0 horizon := by
    rw [uIcc_of_le ordered]
    exact Icc_subset_Icc start0 finishH
  have continuous:=energy_ac seed M F radius horizon start finish inside generated
    (NativeWindowTraceAdjoint.backward_ac seed M start finish ordered (NativeWindowTraceAdjoint.joint seed observation M F radius finish))
  have actual:∀ᵐ t : ℝ,t∈uIcc start finish →HasDerivAt
      (fun t => energy seed M F radius t (propagated seed observation M F radius start finish ordered t))
      (transportedRate seed observation M F radius start finish ordered t) t := by
    filter_upwards [(volume : Measure ℝ).ae_ne start,(volume : Measure ℝ).ae_ne finish] with t left right ht
    rw [uIcc_of_le ordered] at ht
    have clock:t∈Ioo start finish := ⟨lt_of_le_of_ne ht.1 (Ne.symm left),lt_of_le_of_ne ht.2 right⟩
    exact transported_energy_derivative seed observation M F radius start finish ordered horizon generated t
      ⟨start0.trans_lt clock.1,clock.2.trans_le finishH⟩ clock
  have normed:IntervalIntegrable (transportedRate seed observation M F radius start finish ordered) volume start finish := by
    apply (intervalIntegrable_iff').mpr
    refine ((intervalIntegrable_iff').mp continuous.intervalIntegrable_deriv).congr ?_
    filter_upwards [ae_restrict_of_ae actual,ae_restrict_mem measurableSet_uIcc] with t derivative ht
    exact (derivative ht).deriv
  exact ⟨normed,integral_of_ac_derivative _ _ continuous normed actual⟩

theorem response_source_write (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F,FiniteModeNegClosed F →∀ observation start finish (ordered : start≤finish),
      0 ≤ start →finish≤horizon →
      IntervalIntegrable (respondingRate seed observation M F radius start finish ordered) volume start finish ∧
      -energy seed M F radius start (response seed observation M F radius start finish ordered start)=
        ∫t in start..finish,respondingRate seed observation M F radius start finish ordered t := by
  obtain ⟨low,paid⟩ := source_invertible seed horizon nonnegative
  refine ⟨low,fun radius above M F closed observation start finish ordered start0 finishH => ?_⟩
  have generated:=paid radius above M F closed
  have inside:uIcc start finish⊆Icc 0 horizon := by
    rw [uIcc_of_le ordered]
    exact Icc_subset_Icc start0 finishH
  have continuous:=energy_ac seed M F radius horizon start finish inside generated
    (NativeWindowTraceAdjoint.response_ac seed observation M F radius start finish ordered)
  have actual:∀ᵐ t : ℝ,t∈uIcc start finish →HasDerivAt
      (fun t => energy seed M F radius t (response seed observation M F radius start finish ordered t))
      (respondingRate seed observation M F radius start finish ordered t) t := by
    filter_upwards [response_energy_derivative_ae seed observation M F radius start finish ordered start0 horizon generated,
      (volume : Measure ℝ).ae_ne start,(volume : Measure ℝ).ae_ne finish] with t derivative left right ht
    rw [uIcc_of_le ordered] at ht
    have clock:t∈Ioo start finish := ⟨lt_of_le_of_ne ht.1 (Ne.symm left),lt_of_le_of_ne ht.2 right⟩
    exact derivative ⟨start0.trans_lt clock.1,clock.2.trans_le finishH⟩ clock
  have normed:IntervalIntegrable (respondingRate seed observation M F radius start finish ordered) volume start finish := by
    apply (intervalIntegrable_iff').mpr
    refine ((intervalIntegrable_iff').mp continuous.intervalIntegrable_deriv).congr ?_
    filter_upwards [ae_restrict_of_ae actual,ae_restrict_mem measurableSet_uIcc] with t derivative ht
    exact (derivative ht).deriv
  have written:=integral_of_ac_derivative _ _ continuous normed actual
  rw [NativeWindowTraceAdjoint.response_terminal,energy,lifted,map_zero,zero_sub] at written
  exact ⟨normed,written⟩

end
end SaturationMonoid.NavierStokes.NativeWindowTraceDualEvolution

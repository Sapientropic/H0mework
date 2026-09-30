import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.PotentialWork
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Compensated

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeCenteredPotentialBudget
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint NativeDistributedWeightedBudget
open NativeWindowTraceDualEvolution (mass lifted energy)
open NativeCenteredResponseTensor (centered tensor)
open NativeCenteredResponsePayment (potentialWork)
open NativeCenteredResponseRate (remainingRate)
open NativeCenteredResponseClock (clockWork)
open NativeResponseTensorPayment (pairTensor)
noncomputable section
variable {nu : Viscosity}

theorem source_potential_integral_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) (eta : ℝ) (positive : 0 < eta) :
    ∃ low : ℕ,∃ K : ℝ,0 ≤ K ∧∀ radius ≥ low,∀ outerRadius ≤ radius,∀ M observation frame C,
      frame∈Icc 0 horizon →∀ (test : physicalSpace (modes M)) b (ordered : 0 ≤ b),b ≤ horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test 0 b ordered
      let z := fun t => lifted seed M F radius t (p t)
      (∫ t in (0 : ℝ)..b,Real.exp (C*t)*potentialWork seed M F radius frame t (z t)) ≤
        eta*(∫ t in (0 : ℝ)..b,Real.exp (C*t)*‖coefficients (modes M) (testAction (nu := nu) M (z t))‖^2)+
          K*(∫ t in (0 : ℝ)..b,Real.exp (C*t)*(1+NativeUnheatedSourceGradient.mass seed t)*
            energy seed M F radius t (p t)) := by
  obtain ⟨first,K,K0,point⟩ := NativeCenteredPotentialPayment.source_potential_work_paid
    seed horizon nonnegative eta positive
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  refine ⟨max first last,K,K0,fun radius above outerRadius covered M observation frame C framed test b ordered within => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let p := response seed M observation test 0 b ordered
  let z := fun t => lifted seed M F radius t (p t)
  let E := fun t => energy seed M F radius t (p t)
  let weight := fun t => Real.exp (C*t)
  let G := fun t => ‖coefficients (modes M) (testAction (nu := nu) M (z t))‖^2
  let P := fun t => potentialWork seed M F radius frame t (z t)
  let cost := fun t => weight t*(1+NativeUnheatedSourceGradient.mass seed t)*E t
  have generated := inverted radius ((le_max_right first last).trans above) M F
    (NativeWindowFiniteGramFourier.cube_closed outerRadius)
  have zc := response_lift_continuous seed M F radius observation test b ordered
    (fun t ht => generated t (Icc_subset_Icc le_rfl within ht))
  have ec := NativeWindowTraceDualEvolution.energy_ac seed M F radius horizon 0 b
    (by rw [uIcc_of_le ordered]; exact Icc_subset_Icc le_rfl within) generated
    (response_ac seed M observation test 0 b ordered)
  have ecc : ContinuousOn E (uIcc 0 b) := ec.continuousOn
  have wc : Continuous weight := by dsimp only [weight]; fun_prop
  have gc : ContinuousOn G (Icc 0 b) :=
    ((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
      ((LinearMap.toContinuousLinearMap (testAction (nu := nu) M)).continuous.comp_continuousOn zc)).norm.pow 2
  have pc := NativeCenteredResponsePayment.potential_continuousOn seed M F radius frame zc
  have pi := (wc.continuousOn.mul pc).intervalIntegrable_of_Icc (μ := volume) ordered
  have gi := (wc.continuousOn.mul gc).intervalIntegrable_of_Icc (μ := volume) ordered
  have yi : IntervalIntegrable (fun t => 1+NativeUnheatedSourceGradient.mass seed t) volume 0 b :=
    intervalIntegrable_const.add ((intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mpr
      (NativeUnheatedSourceGradient.mass_integrable seed b ordered))
  have costi : IntervalIntegrable cost volume 0 b := by
    have raw := yi.mul_continuousOn (wc.continuousOn.mul ecc)
    convert! raw using 1
    funext t
    dsimp only [cost,Pi.mul_apply]
    ring
  have paid := intervalIntegral.integral_mono_ae_restrict ordered pi
    ((gi.const_mul eta).add (costi.const_mul K)) ?_
  · rw [intervalIntegral.integral_add (gi.const_mul eta) (costi.const_mul K),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at paid
    exact paid
  · filter_upwards [ae_restrict_of_ae
        (point radius ((le_max_left first last).trans above) outerRadius covered M frame framed),
      ae_restrict_mem measurableSet_Icc] with t bound inside
    have localPaid := (le_abs_self _).trans (bound (Icc_subset_Icc le_rfl within inside) (p t))
    have scaled := mul_le_mul_of_nonneg_left localPaid (Real.exp_pos (C*t)).le
    change weight t*P t ≤ eta*(weight t*G t)+K*cost t
    dsimp only [F,p,z,E,P,G,weight,cost] at scaled ⊢
    nlinarith only [scaled]

open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)

theorem source_test_potential_paid (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C epsilon D A K : ℝ,0 ≤ C ∧0 < epsilon ∧0 ≤ D ∧0 ≤ A ∧0 ≤ K ∧
      ∀ outerRadius M observation (observation0 : 0 ≤ observation),observation+2 ≤ horizon →
      let radius := max low outerRadius
      let F := integerWaveFrequencyCube outerRadius
      let test := NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation
      let p := response stackedShortCurrent M observation test 0 (observation+2) (by linarith [observation0])
      let v := fun t => centered stackedShortCurrent M observation t
      let z := fun t => lifted stackedShortCurrent M F radius t (p t)
      let Q := fun t => tensor stackedShortCurrent M F radius observation t (p t)
      (1/2 : ℝ)*‖coefficients (modes M) test‖^2+epsilon*(butterflyGainViscosity.coeff^2/16)*
        (∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*‖coefficients (modes M)
          (testAction (nu := butterflyGainViscosity) M (z t))‖^2) ≤
      D+(∫ t in (0 : ℝ)..(observation+2),pairing (modes M)
        (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t))+
        epsilon*A*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          (∑ j : Coordinate,‖pairTensor M (v t) (NativeWindowHistorySpatialTransport.finite M j (z t))‖^2))+
        epsilon*K*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          (1+NativeUnheatedSourceGradient.mass stackedShortCurrent t)*energy stackedShortCurrent M F radius t (p t))+
        epsilon*(A/(2*butterflyGainViscosity.coeff))*‖Q 0‖^2+
        epsilon*(A/(2*butterflyGainViscosity.coeff))*(∫ t in (0 : ℝ)..(observation+2),Real.exp (C*t)*
          (2*inner ℝ (Q t) (remainingRate stackedShortCurrent M F radius observation t (p t)
            (load (nu := butterflyGainViscosity) observation M test t))+
            clockWork stackedShortCurrent M F radius observation t (p t)+C*‖Q t‖^2)) := by
  obtain ⟨first,C,epsilon,D,A,C0,ep,D0,A0,source⟩ :=
    NativeCenteredCompensated.source_test_actual_budget horizon nonnegative
  obtain ⟨last,K,K0,potential⟩ := source_potential_integral_paid stackedShortCurrent horizon nonnegative
    (butterflyGainViscosity.coeff^2/16) (by positivity [butterflyGainViscosity.coeff_pos])
  refine ⟨max first last,C,epsilon,D,A,K,C0,ep,D0,A0,K0,
    fun outerRadius M observation observation0 within => ?_⟩
  let radius := max (max first last) outerRadius
  have aboveFirst : first ≤ radius := (le_max_left first last).trans (le_max_left _ _)
  have aboveLast : last ≤ radius := (le_max_right first last).trans (le_max_left _ _)
  have covered : outerRadius ≤ radius := le_max_right _ _
  have original := source radius aboveFirst outerRadius M observation observation0 within
  have paid := potential radius aboveLast outerRadius covered M observation observation C
    ⟨observation0,by linarith⟩ (NativeDistributedSourceTest.sourceTest stackedShortCurrent M observation)
    (observation+2) (by linarith) within
  have scaled := mul_le_mul_of_nonneg_left paid ep.le
  dsimp only at original scaled ⊢
  nlinarith only [original,scaled]

end
end SaturationMonoid.NavierStokes.NativeCenteredPotentialBudget

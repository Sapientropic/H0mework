import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Green
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Initial
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceInverse.Integral

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeDistributedWeightedBudget
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint
open NativeWindowTraceDualEvolution (mass inverse lifted energy)
noncomputable section
variable {nu : Viscosity}

private theorem exponential_write {E : ℝ → ℝ} {b : ℝ}
    (actual : AbsolutelyContinuousOnInterval E 0 b) (C : ℝ) :
    (∫ t in (0 : ℝ)..b, Real.exp (C*t)*(deriv E t+C*E t)) =
      Real.exp (C*b)*E b-E 0 := by
  have regular : ContDiff ℝ 1 (fun t : ℝ => Real.exp (C*t)) :=
    (contDiff_const.mul contDiff_id).exp
  have written := regular.contDiffOn.absolutelyContinuousOnInterval.integral_deriv_mul_eq_sub actual
  have rate (t : ℝ) : deriv (fun t : ℝ => Real.exp (C*t)) t = Real.exp (C*t)*C := by
    simpa only [id_eq,mul_one] using ((hasDerivAt_id t).const_mul C).exp.deriv
  simp only [rate,mul_zero,Real.exp_zero,one_mul] at written
  convert! written using 1
  apply intervalIntegral.integral_congr
  intro t _
  ring

theorem exponential_budget {E G Q : ℝ → ℝ} {b H C a K : ℝ}
    (ordered : 0 ≤ b) (within : b ≤ H) (C0 : 0 ≤ C) (K0 : 0 ≤ K)
    (actual : AbsolutelyContinuousOnInterval E 0 b) (terminal : E b = 0)
    (graph : ContinuousOn G (Icc 0 b)) (work : ContinuousOn Q (Icc 0 b))
    (gate : ∀ t ∈ Ioo 0 b, a*G t ≤ deriv E t+Q t+C*E t+K) :
    E 0+a*(∫ t in (0 : ℝ)..b, Real.exp (C*t)*G t) ≤
      (∫ t in (0 : ℝ)..b, Real.exp (C*t)*Q t)+H*Real.exp (C*H)*K := by
  have ec : Continuous (fun t : ℝ => Real.exp (C*t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have gc := ec.continuousOn.mul graph
  have qc := ec.continuousOn.mul work
  rw [← uIcc_of_le ordered] at gc qc
  have Ei := actual.intervalIntegrable_deriv.add (actual.continuousOn.intervalIntegrable.const_mul C)
  have Ei' := Ei.continuousOn_mul ec.continuousOn
  have Ki := intervalIntegrable_const (μ := volume) (a := (0 : ℝ)) (b := b) (c := Real.exp (C*H)*K)
  have scaled := intervalIntegral.integral_mono_ae_restrict ordered (gc.intervalIntegrable.const_mul a)
    ((Ei'.add qc.intervalIntegrable).add Ki) ?_
  · rw [intervalIntegral.integral_add (Ei'.add qc.intervalIntegrable) Ki,
      intervalIntegral.integral_add Ei' qc.intervalIntegrable,
      intervalIntegral.integral_const_mul,exponential_write actual C,terminal,
      mul_zero,zero_sub,intervalIntegral.integral_const] at scaled
    have length := mul_le_mul_of_nonneg_right within
      (mul_nonneg (Real.exp_pos (C*H)).le K0)
    simp only [sub_zero,smul_eq_mul,Pi.mul_apply] at scaled
    nlinarith only [scaled,length]
  · filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne 0),
      ae_restrict_of_ae ((volume : Measure ℝ).ae_ne b)] with t ht left right
    have inside : t ∈ Ioo 0 b := ⟨lt_of_le_of_ne ht.1 (Ne.symm left),lt_of_le_of_ne ht.2 right⟩
    have paid := mul_le_mul_of_nonneg_left (gate t inside) (Real.exp_pos (C*t)).le
    have cap := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (ht.2.trans within) C0)) K0
    simp only [Pi.mul_apply]
    nlinarith only [paid,cap]

theorem response_lift_continuous (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (b : ℝ) (ordered : 0 ≤ b)
    (generated : ∀ t ∈ Icc 0 b, (mass seed M F radius t).IsInvertible) :
    ContinuousOn (fun t => lifted seed M F radius t
      (response seed M observation test 0 b ordered t)) (Icc 0 b) := by
  have ic : ContinuousOn (inverse seed M F radius) (Icc 0 b) :=
    fun t ht => (NativeWindowTraceDualEvolution.inverse_differentiableAt seed M F radius t
      (generated t ht)).continuousAt.continuousWithinAt
  exact ic.clm_apply (response_continuous seed M observation test 0 b ordered)

theorem convection_continuous (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) {b : ℝ}
    {z : ℝ → physicalSpace (modes M)} (zc : ContinuousOn z (Icc 0 b)) :
    ContinuousOn (fun t => NativeDistributedLyapunov.convectionWork seed M F radius t (z t))
      (Icc 0 b) := by
  let read := LinearMap.toContinuousLinearMap (coefficients (modes M))
  let L := LinearMap.toContinuousLinearMap (testAction (nu := nu) M)
  have left := read.continuous.comp_continuousOn
    ((NativeWindowTraceDualEvolution.mass_contDiff seed M F radius).continuous.continuousOn.clm_apply zc)
  have right := read.continuous.comp_continuousOn
    (((NativeWindowTraceAdjoint.forward_continuous seed M).continuousOn.clm_apply zc).add
      ((L.continuous.comp_continuousOn zc).const_smul nu.coeff))
  have paid := (left.inner (𝕜 := ℝ) right).const_mul (2 : ℝ)
  convert! paid using 1
  funext t
  change 2*pairing (modes M) (mass seed M F radius t (z t)) _ =
    2*pairing (modes M) (mass seed M F radius t (z t))
      (NativeWindowTraceAdjoint.forward seed M t (z t)+nu.coeff • testAction (nu := nu) M (z t))
  rw [NativeDistributedLyapunov.forward_split]
  congr 2
  dsimp only [testAction]
  module

def kernelBudget (nu : Viscosity) (horizon C : ℝ) : ℝ :=
  horizon*Real.exp (C*horizon)*(2/nu.coeff^2)*NativeWindowFiniteStressUniform.kernelBound 0 ^ 2

theorem kernelBudget_nonnegative (nu : Viscosity) {horizon : ℝ} (nonnegative : 0 ≤ horizon) (C : ℝ) :
    0 ≤ kernelBudget nu horizon C := by unfold kernelBudget; positivity

theorem source_weighted_graph (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ radius ≥ low, ∀ outerRadius M observation (test : physicalSpace (modes M)),
      ∀ b (ordered : 0 ≤ b), b ≤ horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test 0 b ordered
      let z := fun t => lifted seed M F radius t (p t)
      energy seed M F radius 0 (p 0)+
        (nu.coeff^2/2)*(∫ t in (0 : ℝ)..b,
          Real.exp (C*t)*‖coefficients (modes M) (testAction (nu := nu) M (z t))‖^2) ≤
        (∫ t in (0 : ℝ)..b,
          Real.exp (C*t)*NativeDistributedLyapunov.convectionWork seed M F radius t (z t))+
          kernelBudget nu horizon C*‖coefficients (modes M) test‖^2 := by
  obtain ⟨first,C,C0,gate⟩ := source_response_graph_gate seed horizon nonnegative
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  let k := NativeWindowFiniteStressUniform.kernelBound 0
  refine ⟨max first last,C,C0,
    fun radius above outerRadius M observation test b ordered within => ?_⟩
  let F := integerWaveFrequencyCube outerRadius
  let p := response seed M observation test 0 b ordered
  let z := fun t => lifted seed M F radius t (p t)
  have generated := inverted radius ((le_max_right first last).trans above) M F
    (NativeWindowFiniteGramFourier.cube_closed outerRadius)
  have ec := NativeWindowTraceDualEvolution.energy_ac seed M F radius horizon 0 b
    (by rw [uIcc_of_le ordered]; exact Icc_subset_Icc le_rfl within) generated
    (response_ac seed M observation test 0 b ordered)
  have zc := response_lift_continuous seed M F radius observation test b ordered
    (fun t ht => generated t (Icc_subset_Icc le_rfl within ht))
  have gc := ((LinearMap.toContinuousLinearMap (coefficients (modes M))).continuous.comp_continuousOn
    ((LinearMap.toContinuousLinearMap (testAction (nu := nu) M)).continuous.comp_continuousOn zc)).norm.pow 2
  have qc := convection_continuous seed M F radius zc
  have terminal : energy seed M F radius b (p b) = 0 := by
    simp only [p,response_terminal,energy,lifted,map_zero]
  have paid := exponential_budget (E := fun t => energy seed M F radius t (p t))
    (G := fun t => ‖coefficients (modes M) (testAction (nu := nu) M (z t))‖^2)
    (Q := fun t => NativeDistributedLyapunov.convectionWork seed M F radius t (z t))
    (a := nu.coeff^2/2) (K := (2/nu.coeff^2)*k^2*‖coefficients (modes M) test‖^2)
    ordered within C0 (by positivity) ec terminal gc qc ?_
  · dsimp only [F,p,z] at paid ⊢
    convert! paid using 1
    dsimp only [kernelBudget,k]
    ring
  · intro t inside
    have bound := gate radius ((le_max_left first last).trans above) outerRadius M observation test
      0 b ordered t inside ⟨inside.1,inside.2.trans_le within⟩
    have kernel := NativeWindowFiniteStressUniform.kernel_bounded 0 (observation-t)
    simp only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero,Real.norm_eq_abs] at kernel
    have square : NativeForwardWindowSource.kernel (observation-t)^2 ≤ k^2 := by
      exact sq_le_sq.mpr (by simpa only [k,abs_of_pos (NativeWindowFiniteStressUniform.kernelBound_positive 0)] using kernel)
    have scaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left square (by positivity : 0 ≤ 2/nu.coeff^2))
      (sq_nonneg ‖coefficients (modes M) test‖)
    dsimp only [F,p,z] at *
    linarith only [bound,scaled]

open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
open NativeWindowTraceAdjoint (value)

theorem source_weighted_window (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ, ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ radius ≥ low, ∀ outerRadius M observation (observation0 : 0 ≤ observation), observation+2 ≤ horizon →
      ∀ test : physicalSpace (modes M),
      let F := integerWaveFrequencyCube outerRadius
      let p := response stackedShortCurrent M observation test 0 (observation+2) (by linarith [observation0])
      let z := fun t => lifted stackedShortCurrent M F radius t (p t)
      pairing (modes M) (window stackedShortCurrent M observation)
        (testAction (nu := butterflyGainViscosity) M test)+
          epsilon*(butterflyGainViscosity.coeff^2/2)*
            (∫ t in (0 : ℝ)..(observation+2), Real.exp (C*t)*
              ‖coefficients (modes M) (testAction (nu := butterflyGainViscosity) M (z t))‖^2) ≤
        D+epsilon*kernelBudget butterflyGainViscosity horizon C*‖coefficients (modes M) test‖^2+
          (∫ t in (0 : ℝ)..(observation+2),
            pairing (modes M) (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t))+
          epsilon*(∫ t in (0 : ℝ)..(observation+2),
            Real.exp (C*t)*NativeDistributedLyapunov.convectionWork stackedShortCurrent M F radius t (z t)) := by
  obtain ⟨first,C,C0,graph⟩ := source_weighted_graph stackedShortCurrent horizon nonnegative
  obtain ⟨last,D,D0,initial⟩ := source_initial_pair_paid horizon nonnegative epsilon positive
  refine ⟨max first last,C,D,C0,D0,fun radius above outerRadius M observation observation0 within test => ?_⟩
  have ordered : 0 ≤ observation+2 := by linarith
  have paid := graph radius ((le_max_left first last).trans above) outerRadius M observation test
    (observation+2) ordered within
  have start := initial radius ((le_max_right first last).trans above) outerRadius M
    (response stackedShortCurrent M observation test 0 (observation+2) ordered 0)
  have signed := (le_abs_self _).trans start
  have green := window_source_green stackedShortCurrent M observation observation0 test
  have scaled := mul_le_mul_of_nonneg_left paid positive.le
  dsimp only at paid signed scaled ⊢
  nlinarith only [signed,green,scaled]

end
end SaturationMonoid.NavierStokes.NativeDistributedWeightedBudget

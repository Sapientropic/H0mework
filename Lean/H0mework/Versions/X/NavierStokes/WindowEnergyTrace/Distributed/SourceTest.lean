import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Mean

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeDistributedSourceTest
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowDistributedAdjoint NativeDistributedWeightedBudget
open NativeWindowTraceDualEvolution (lifted energy)
open NativeDistributedHistoryPayment (centeredWork)
open RationalVorticityEvaluator.ButterflyStackedSourceCurrent (stackedShortCurrent)
open RationalVorticityEvaluator (butterflyGainViscosity)
noncomputable section
variable {nu : Viscosity}

def sourceTest (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ) :
    physicalSpace (modes M) := testAction (nu := nu) M (window seed M observation)

theorem source_pair (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ) :
    pairing (modes M) (window seed M observation)
      (testAction (nu := nu) M (sourceTest seed M observation)) =
        ‖coefficients (modes M) (sourceTest seed M observation)‖^2 := by
  rw [testAction_symmetric]
  change inner ℝ (coefficients (modes M) (sourceTest seed M observation))
    (coefficients (modes M) (sourceTest seed M observation)) = _
  exact real_inner_self_eq_norm_sq _

theorem centered_continuous (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (frame : ℝ) {b : ℝ}
    {z : ℝ → physicalSpace (modes M)} (zc : ContinuousOn z (Icc 0 b)) :
    ContinuousOn (fun t => centeredWork seed M F radius frame t (z t)) (Icc 0 b) := by
  let read := LinearMap.toContinuousLinearMap (coefficients (modes M))
  have left := read.continuous.comp_continuousOn
    ((NativeWindowTraceDualEvolution.mass_contDiff seed M F radius).continuous.continuousOn.clm_apply zc)
  have right := read.continuous.comp_continuousOn
    (((NativeWindowTraceAdjoint.forward_continuous seed M).continuousOn.clm_apply zc).sub
      ((NativeWindowHistoryMeanAction.frozen nu M
        (NativeWindowHistoryMeanAction.meanValue seed M frame)).continuous.comp_continuousOn zc))
  exact (left.inner (𝕜 := ℝ) right).const_mul (2 : ℝ)

theorem source_centered_weighted_graph (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ radius ≥ low, ∀ outerRadius M observation frame, frame ∈ Icc 0 horizon →
      ∀ (test : physicalSpace (modes M)) b (ordered : 0 ≤ b), b ≤ horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response seed M observation test 0 b ordered
      let z := fun t => lifted seed M F radius t (p t)
      energy seed M F radius 0 (p 0)+
        (nu.coeff^2/4)*(∫ t in (0 : ℝ)..b,
          Real.exp (C*t)*‖coefficients (modes M) (testAction (nu := nu) M (z t))‖^2) ≤
        (∫ t in (0 : ℝ)..b, Real.exp (C*t)*centeredWork seed M F radius frame t (z t))+
          kernelBudget nu horizon C*‖coefficients (modes M) test‖^2 := by
  obtain ⟨first,C,C0,gate⟩ := NativeDistributedHistoryPayment.source_centered_response_graph_gate
    seed horizon nonnegative
  obtain ⟨last,inverted⟩ := NativeWindowTraceDualEvolution.source_invertible seed horizon nonnegative
  let k := NativeWindowFiniteStressUniform.kernelBound 0
  refine ⟨max first last,C,C0,fun radius above outerRadius M observation frame framed test b ordered within => ?_⟩
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
  have qc := centered_continuous seed M F radius frame zc
  have terminal : energy seed M F radius b (p b) = 0 := by
    simp only [p,response_terminal,energy,lifted,map_zero]
  have paid := exponential_budget (E := fun t => energy seed M F radius t (p t))
    (G := fun t => ‖coefficients (modes M) (testAction (nu := nu) M (z t))‖^2)
    (Q := fun t => centeredWork seed M F radius frame t (z t))
    (a := nu.coeff^2/4) (K := (2/nu.coeff^2)*k^2*‖coefficients (modes M) test‖^2)
    ordered within C0 (by positivity) ec terminal gc qc ?_
  · dsimp only [F,p,z] at paid ⊢
    convert! paid using 1
    dsimp only [kernelBudget,k]
    ring
  · intro t inside
    have bound := gate radius ((le_max_left first last).trans above) outerRadius M observation frame framed test
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

theorem source_test_budget (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ, ∃ C epsilon D : ℝ, 0 ≤ C ∧ 0 < epsilon ∧ 0 ≤ D ∧
      ∀ radius ≥ low, ∀ outerRadius M observation (observation0 : 0 ≤ observation),
      observation+2 ≤ horizon →
      let F := integerWaveFrequencyCube outerRadius
      let p := response stackedShortCurrent M observation (sourceTest stackedShortCurrent M observation)
        0 (observation+2) (by linarith [observation0])
      let z := fun t => lifted stackedShortCurrent M F radius t (p t)
      (1/2 : ℝ)*‖coefficients (modes M) (sourceTest stackedShortCurrent M observation)‖^2+
        epsilon*(butterflyGainViscosity.coeff^2/4)*
          (∫ t in (0 : ℝ)..(observation+2), Real.exp (C*t)*
            ‖coefficients (modes M) (testAction (nu := butterflyGainViscosity) M (z t))‖^2) ≤
        D+(∫ t in (0 : ℝ)..(observation+2),
          pairing (modes M) (NativeWindowStageNineSource.forcing stackedShortCurrent M t) (p t))+
        epsilon*(∫ t in (0 : ℝ)..(observation+2), Real.exp (C*t)*
          centeredWork stackedShortCurrent M F radius observation t (z t)) := by
  obtain ⟨first,C,C0,graph⟩ := source_centered_weighted_graph stackedShortCurrent horizon nonnegative
  let B := kernelBudget butterflyGainViscosity horizon C
  have B0 : 0 ≤ B := kernelBudget_nonnegative butterflyGainViscosity nonnegative C
  let epsilon := 1/(4*(B+1))
  have positive : 0 < epsilon := by dsimp only [epsilon]; positivity
  have absorb : epsilon*B ≤ (1/2 : ℝ) := by
    have written : epsilon*(4*(B+1))=1 := by
      dsimp only [epsilon]
      exact div_mul_cancel₀ _ (by positivity : 4*(B+1)≠0)
    nlinarith only [written,positive,B0]
  obtain ⟨last,D,D0,initial⟩ := source_initial_pair_paid horizon nonnegative epsilon positive
  refine ⟨max first last,C,epsilon,D,C0,positive,D0,
    fun radius above outerRadius M observation observation0 within => ?_⟩
  let test := sourceTest stackedShortCurrent M observation
  have ordered : 0 ≤ observation+2 := by linarith
  have paid := graph radius ((le_max_left first last).trans above) outerRadius M observation observation
    ⟨observation0,by linarith⟩ test
    (observation+2) ordered within
  have start := initial radius ((le_max_right first last).trans above) outerRadius M
    (response stackedShortCurrent M observation test 0 (observation+2) ordered 0)
  have signed := (le_abs_self _).trans start
  have green := window_source_green stackedShortCurrent M observation observation0 test
  change pairing (modes M) (window stackedShortCurrent M observation)
    (testAction (nu := butterflyGainViscosity) M (sourceTest stackedShortCurrent M observation)) = _ at green
  rw [source_pair] at green
  have scaled := mul_le_mul_of_nonneg_left paid positive.le
  have kernel := mul_le_mul_of_nonneg_right absorb (sq_nonneg ‖coefficients (modes M) test‖)
  dsimp only [test,B] at paid signed scaled kernel green ⊢
  nlinarith only [green,signed,scaled,kernel]

end
end SaturationMonoid.NavierStokes.NativeDistributedSourceTest

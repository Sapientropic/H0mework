import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Evolution
import H0mework.Versions.X.NavierStokes.WindowEnergyAugmented.GradientSource

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowTraceCorrection
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeFiniteActionResolvent NativeWholeH1Mixed NativeWholeResolvent
open NativeWindowStressOseenTest (evaluate)
open NativeWindowStressOseenSource (load)
open NativeWindowAugmentedGradient (derivative)
open NativeWindowAugmentedGradientSource (palinRead palinstrophyWindow)
open NativeWindowAugmentedTestProduct NativeUnheatedStressProduct NativeCommonAdvectorAction
open NativeWindowAugmentedCoercivity (productCap)
open NativeWindowStressHeatSource (physical jetRead product_integrable productAverage)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceEnergy (correction crossWork)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def testForm (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (value : physicalSpace M) : ℝ :=
  ∑ i : Coordinate,inner ℝ (correction seed F radius observation) (physical (evaluate M F i value*evaluate M F i value))

theorem testForm_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (value : physicalSpace M) (zero : 0∉M) (closedM : FiniteModeNegClosed M)
    (closedF : FiniteModeNegClosed F) (delta : ℝ) (nonnegative : 0≤delta)
    (small : ∀ i,‖NativeWindowPressureStrainHistory.correction seed F radius observation i i‖≤delta) :
    |testForm seed observation M F radius value|≤9*delta*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
  have traceBound : ‖correction seed F radius observation‖≤3*delta :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => small i).trans_eq (by simp))
  have row (i : Coordinate) : |inner ℝ (correction seed F radius observation)
      (physical (evaluate M F i value*evaluate M F i value))|≤
        3*delta*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    apply (abs_real_inner_le_norm _ _).trans
    have tested := (product_bound M F value zero closedM closedF i i).trans
      (mul_le_mul_of_nonneg_left (projected_gradient_le M F value) (by positivity))
    exact (mul_le_mul traceBound tested (norm_nonneg _) (by positivity)).trans_eq (by unfold productCap; ring)
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => row i).trans_eq (by simp; ring))

theorem source_test_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M F : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →FiniteModeNegClosed F →
      ∀ time∈Icc 0 horizon,∀ value : physicalSpace M,
        |testForm seed time M F radius value|≤(nu.coeff/2)*curlPair M value.1 value.1 := by
  let delta := nu.coeff*(2*Real.pi)^2/(18*(productCap+1))
  have deltaPos : 0<delta := by dsimp only [delta,productCap]; positivity [nu.coeff_pos]
  obtain ⟨low,paid⟩ := NativeWindowJointNormalForm.correctionJet_small seed 0 horizon nonnegative delta deltaPos
  refine ⟨low,fun radius above M F zero closedM closedF time inside value => ?_⟩
  have small (i : Coordinate) : ‖NativeWindowPressureStrainHistory.correction seed F radius time i i‖≤delta := by
    simpa only [NativeWindowJointNormalForm.correctionJet_zero] using (paid radius above F time inside i i).le
  have bound := testForm_bound seed time M F radius value zero closedM closedF delta deltaPos.le small
  have G0 : 0≤gradientMass (complexSharpSupportProjection M value.1) := tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative _)
  have fraction : 9*delta*productCap≤(nu.coeff/2)*(2*Real.pi)^2 := by
    have denominator : 18*(productCap+1)>0 := by unfold productCap; positivity
    have same : delta*(18*(productCap+1))=nu.coeff*(2*Real.pi)^2 := div_mul_cancel₀ _ denominator.ne'
    nlinarith only [same,deltaPos]
  have cost := mul_le_mul_of_nonneg_right fraction G0
  rw [mul_assoc (nu.coeff/2),← curl_original M value zero] at cost
  exact bound.trans cost

def read (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) : C(Torus,ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (correction seed F radius observation)).comp physical

def sample (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) : ℝ :=
  ∑ j : Coordinate,∑ i : Coordinate,read seed observation F radius
    (jetRead F j 1 i (NativeUnifiedCompleteSource.source seed time)*jetRead F j 1 i (NativeUnifiedCompleteSource.source seed time))

theorem sample_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (radius L : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes L) (time : ℝ) (nonnegative : 0≤time) :
    (∑ j : Coordinate,testForm seed observation (modes L) F radius
      (derivative (modes L) (modes_zero L) (modes_closed L) j (load L seed time)))=sample seed observation F radius time := by
  simp only [testForm,NativeWindowAugmentedGradientSource.gradient_load seed L time nonnegative F cover,
    sample,read,ContinuousLinearMap.comp_apply,innerSL_apply_apply]

theorem sample_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    Integrable (fun shift => sample seed time F radius (time-shift)) averageMeasure :=
  integrable_finsetSum Finset.univ fun j _ => integrable_finsetSum Finset.univ fun i _ =>
    (read seed time F radius).integrable_comp (product_integrable seed time (jetRead F j 1 i) (jetRead F j 1 i))

theorem sample_average (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F : Finset IntegerWavevector) (radius : ℕ) :
    (∫ shift,sample seed time F radius (time-shift) ∂averageMeasure)=crossWork seed F radius time := by
  have paid (j i : Coordinate) := (read seed time F radius).integrable_comp
    (product_integrable seed time (jetRead F j 1 i) (jetRead F j 1 i))
  unfold sample
  rw [integral_finsetSum Finset.univ (fun j _ => integrable_finsetSum Finset.univ (fun i _ => paid j i))]
  simp_rw [integral_finsetSum Finset.univ (fun i _ => paid _ i)]
  have row (j i : Coordinate) : (∫ shift,read seed time F radius
      (jetRead F j 1 i (NativeUnifiedCompleteSource.source seed (time-shift))*
        jetRead F j 1 i (NativeUnifiedCompleteSource.source seed (time-shift))) ∂averageMeasure)=
      read seed time F radius (productAverage seed time (jetRead F j 1 i) (jetRead F j 1 i)) :=
    (read seed time F radius).integral_comp_comm (product_integrable seed time _ _)
  simp only [row]
  rw [Finset.sum_comm]
  simp only [← map_sum]
  rfl

theorem source_cross_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ L : ℕ,∀ F : Finset IntegerWavevector,FiniteModeNegClosed F →
      (∀ k∈F,k≠0 →k∈modes L) →∀ time∈Icc 0 horizon,
        |crossWork seed F radius time|≤(nu.coeff/2)*palinstrophyWindow seed L time := by
  obtain ⟨low,paid⟩ := source_test_bound seed horizon nonnegative
  refine ⟨low,fun radius above L F closed cover time inside => ?_⟩
  have point : ∀ᵐ shift ∂averageMeasure,|sample seed time F radius (time-shift)|≤
      (nu.coeff/2)*‖palinRead nu L (NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift))‖^2 := by
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    rw [← sample_original seed time F radius L cover (time-shift) (by linarith [inside.1])]
    have bound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ =>
      paid radius above (modes L) F (modes_zero L) (modes_closed L) closed time inside
        (derivative (modes L) (modes_zero L) (modes_closed L) j (load L seed (time-shift)))
    apply (Finset.abs_sum_le_sum_abs _ _).trans (bound.trans_eq ?_)
    rw [← Finset.mul_sum,NativeWindowAugmentedGradient.palinstrophy_original (nu := nu),
      NativeWindowAugmentedGradientSource.palinRead_original]
  have integrated := integral_mono_ae (sample_integrable seed time F radius).norm
    ((NativeWindowAugmentedGradientSource.palinstrophy_integrable seed L time).const_mul (nu.coeff/2)) point
  rw [integral_const_mul] at integrated
  rw [← sample_average]
  exact (norm_integral_le_integral_norm _).trans integrated

theorem heat_graph_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ L : ℕ,∀ F : Finset IntegerWavevector,FiniteModeNegClosed F →
      (∀ k∈F,k≠0 →k∈modes L) →∀ time∈Icc 0 horizon,
        NativeWindowTraceEnergy.heatWork seed F radius time-2*nu.coeff^2*palinstrophyWindow seed L time≤
          -nu.coeff*NativeWindowTraceEnergy.dirichlet seed F radius time-
            (nu.coeff/2)*NativeWindowStressHeatSource.dirichlet seed time F-nu.coeff^2*palinstrophyWindow seed L time := by
  obtain ⟨low,paid⟩ := source_cross_bound seed horizon nonnegative
  refine ⟨low,fun radius above L F closed cover time inside => ?_⟩
  have small := paid radius above L F closed cover time inside
  have scaled := mul_le_mul_of_nonneg_left ((neg_le_abs _).trans small) (show 0≤2*nu.coeff from by positivity [nu.coeff_pos])
  have gradient := mul_le_mul_of_nonneg_left (NativeWindowTraceGradient.source_gradient_bound seed time F closed)
    (show 0≤nu.coeff/2 from by positivity [nu.coeff_pos])
  rw [NativeWindowTraceEnergy.heatWork_identity seed F radius time closed]
  nlinarith only [scaled,gradient]

theorem eventual_heat_graph_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ F : Finset IntegerWavevector,FiniteModeNegClosed F →∀ᶠ L : ℕ in atTop,∀ time∈Icc 0 horizon,
      NativeWindowTraceEnergy.heatWork seed F radius time-2*nu.coeff^2*palinstrophyWindow seed L time≤
        -nu.coeff*NativeWindowTraceEnergy.dirichlet seed F radius time-
          (nu.coeff/2)*NativeWindowStressHeatSource.dirichlet seed time F-nu.coeff^2*palinstrophyWindow seed L time := by
  obtain ⟨low,paid⟩ := heat_graph_coercivity seed horizon nonnegative
  refine ⟨low,fun radius above F closed => ?_⟩
  filter_upwards [NativeWindowStressOseenSource.cover_eventually F] with L cover time inside
  exact paid radius above L F closed cover time inside

theorem eventual_source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) : ∃ low : ℕ,∀ radius≥low,∀ F : Finset IntegerWavevector,
      FiniteModeNegClosed F →∀ᶠ L : ℕ in atTop,∀ time∈Icc 0 horizon,
        deriv (NativeWindowTraceEnergy.energy seed F radius) time-2*nu.coeff^2*palinstrophyWindow seed L time≤
          -nu.coeff*NativeWindowTraceEnergy.dirichlet seed F radius time-
            (nu.coeff/2)*NativeWindowStressHeatSource.dirichlet seed time F-nu.coeff^2*palinstrophyWindow seed L time+
              NativeWindowTraceEnergy.lowAdvWork seed F radius time+NativeWindowTraceEnergy.convectionWork seed F radius time+
                NativeWindowTraceEnergy.lowPressureWork seed F radius time+NativeWindowTraceEnergy.energy seed F radius time+epsilon := by
  obtain ⟨space,spatial⟩ := eventual_heat_graph_coercivity seed horizon nonnegative
  obtain ⟨temporal,paid⟩ := NativeWindowTraceEnergy.timeWork_uniform seed horizon nonnegative epsilon positive
  refine ⟨max space temporal,fun radius above F closed => ?_⟩
  filter_upwards [spatial radius ((le_max_left _ _).trans above) F closed] with L bounded time inside
  have heat := bounded time inside
  have clock := paid radius ((le_max_right _ _).trans above) F time inside
  have signed := neg_le_abs (NativeWindowTraceEnergy.timeWork seed F radius time)
  rw [(NativeWindowTraceEnergy.energy_generator seed F radius time inside.1 closed).deriv]
  linarith only [heat,clock,signed]

end
end SaturationMonoid.NavierStokes.NativeWindowTraceCorrection

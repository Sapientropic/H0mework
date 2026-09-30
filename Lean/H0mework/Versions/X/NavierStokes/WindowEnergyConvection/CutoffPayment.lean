import H0mework.Versions.X.NavierStokes.WindowEnergyConvection.CutoffTrace
import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Correction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffPayment
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
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
open NativeWindowConvectionCutoffTrace (relative correction crossWork timeWork energy)
open NativeWindowFiniteGramFourier (cube_closed)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

theorem timeWork_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) : ∃ low : ℕ,∀ radius ≥ low,∀ cutoff ≥ low,∀ time,time∈Icc 0 horizon →
      |timeWork seed (integerWaveFrequencyCube cutoff) radius time|≤energy seed (integerWaveFrequencyCube cutoff) radius time+epsilon := by
  obtain ⟨low,small⟩ := NativeWindowConvectionCutoffNormalForm.correctionJet_small seed 1 horizon nonnegative (Real.sqrt (2*epsilon)/3) (by positivity)
  refine ⟨low,fun radius above cutoff covered time inside => ?_⟩
  have bound : ‖∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.correctionJet seed (integerWaveFrequencyCube cutoff) radius 1 time i i‖≤Real.sqrt (2*epsilon) :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => (small radius above cutoff covered time inside i i).le).trans_eq (by simp; ring))
  have square := pow_le_pow_left₀ (norm_nonneg _) bound 2
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2*epsilon)] at square
  apply (abs_real_inner_le_norm _ _).trans
  unfold energy
  nlinarith only [square,sq_nonneg (‖relative seed (integerWaveFrequencyCube cutoff) radius time‖-
    ‖∑ i : Coordinate,NativeWindowConvectionCutoffNormalForm.correctionJet seed (integerWaveFrequencyCube cutoff) radius 1 time i i‖)]

def testForm (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (value : physicalSpace M) : ℝ :=
  ∑ i : Coordinate,inner ℝ (correction seed F radius observation) (physical (evaluate M F i value*evaluate M F i value))

theorem testForm_bound (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (value : physicalSpace M) (zero : 0∉M) (closedM : FiniteModeNegClosed M)
    (closedF : FiniteModeNegClosed F) (delta : ℝ) (nonnegative : 0 ≤ delta)
    (small : ∀ i,‖NativeWindowConvectionCutoffNormalForm.correction seed F radius observation i i‖≤delta) :
    |testForm seed observation M F radius value|≤9*delta*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
  have traceBound : ‖correction seed F radius observation‖≤3*delta :=
    (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => small i).trans_eq (by simp))
  have row (i : Coordinate) : |inner ℝ (correction seed F radius observation)
      (physical (evaluate M F i value*evaluate M F i value))|≤3*delta*productCap*gradientMass (complexSharpSupportProjection M value.1) := by
    apply (abs_real_inner_le_norm _ _).trans
    have tested := (product_bound M F value zero closedM closedF i i).trans
      (mul_le_mul_of_nonneg_left (projected_gradient_le M F value) (by positivity))
    exact (mul_le_mul traceBound tested (norm_nonneg _) (by positivity)).trans_eq (by unfold productCap; ring)
  exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => row i).trans_eq (by simp; ring))

theorem source_test_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ radius ≥ low,∀ cutoff ≥ low,∀ M : Finset IntegerWavevector,0∉M →FiniteModeNegClosed M →
      ∀ time∈Icc 0 horizon,∀ value : physicalSpace M,
        |testForm seed time M (integerWaveFrequencyCube cutoff) radius value|≤(nu.coeff/2)*curlPair M value.1 value.1 := by
  let delta := nu.coeff*(2*Real.pi)^2/(18*(productCap+1))
  have deltaPos : 0 < delta := by dsimp only [delta,productCap]; positivity [nu.coeff_pos]
  obtain ⟨low,paid⟩ := NativeWindowConvectionCutoffNormalForm.correctionJet_small seed 0 horizon nonnegative delta deltaPos
  refine ⟨low,fun radius above cutoff covered M zero closedM time inside value => ?_⟩
  have small (i : Coordinate) : ‖NativeWindowConvectionCutoffNormalForm.correction seed (integerWaveFrequencyCube cutoff) radius time i i‖≤delta := by
    simpa only [NativeWindowConvectionCutoffNormalForm.correctionJet_zero] using (paid radius above cutoff covered time inside i i).le
  have bound := testForm_bound seed time M (integerWaveFrequencyCube cutoff) radius value zero closedM (cube_closed cutoff) delta deltaPos.le small
  have G0 : 0 ≤ gradientMass (complexSharpSupportProjection M value.1) := tsum_nonneg (NativeUnheatedStressProduct.density_nonnegative _)
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
    (radius L : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes L) (time : ℝ) (nonnegative : 0 ≤ time) :
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
  have paid (j i : Coordinate) := (read seed time F radius).integrable_comp (product_integrable seed time (jetRead F j 1 i) (jetRead F j 1 i))
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

theorem source_cross_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∀ radius ≥ low,∀ cutoff ≥ low,∀ L : ℕ,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes L) →∀ time∈Icc 0 horizon,
        |crossWork seed (integerWaveFrequencyCube cutoff) radius time|≤(nu.coeff/2)*palinstrophyWindow seed L time := by
  obtain ⟨low,paid⟩ := source_test_bound seed horizon nonnegative
  refine ⟨low,fun radius above cutoff covered L cover time inside => ?_⟩
  have point : ∀ᵐ shift ∂averageMeasure,|sample seed time (integerWaveFrequencyCube cutoff) radius (time-shift)|≤
      (nu.coeff/2)*‖palinRead nu L (NativeUnheatedSourceQuadraticApprox.physicalSource seed (time-shift))‖^2 := by
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    rw [← sample_original seed time (integerWaveFrequencyCube cutoff) radius L cover (time-shift) (by linarith [inside.1])]
    have bound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun j _ =>
      paid radius above cutoff covered (modes L) (modes_zero L) (modes_closed L) time inside
        (derivative (modes L) (modes_zero L) (modes_closed L) j (load L seed (time-shift)))
    apply (Finset.abs_sum_le_sum_abs _ _).trans (bound.trans_eq ?_)
    rw [← Finset.mul_sum,NativeWindowAugmentedGradient.palinstrophy_original (nu := nu),NativeWindowAugmentedGradientSource.palinRead_original]
  have integrated := integral_mono_ae (sample_integrable seed time (integerWaveFrequencyCube cutoff) radius).norm
    ((NativeWindowAugmentedGradientSource.palinstrophy_integrable seed L time).const_mul (nu.coeff/2)) point
  rw [integral_const_mul] at integrated
  rw [← sample_average]
  exact (norm_integral_le_integral_norm _).trans integrated

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) : ∃ low : ℕ,∀ radius ≥ low,∀ cutoff ≥ low,∀ L : ℕ,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes L) →∀ time∈Icc 0 horizon,
        deriv (energy seed (integerWaveFrequencyCube cutoff) radius) time-2*nu.coeff^2*palinstrophyWindow seed L time≤
          -nu.coeff*NativeWindowConvectionCutoffTrace.dirichlet seed (integerWaveFrequencyCube cutoff) radius time-
            (nu.coeff/2)*NativeWindowStressHeatSource.dirichlet seed time (integerWaveFrequencyCube cutoff)-nu.coeff^2*palinstrophyWindow seed L time+
              NativeWindowConvectionCutoffTrace.lowAdvWork seed (integerWaveFrequencyCube cutoff) radius time+
              NativeWindowConvectionCutoffTrace.strainWork seed (integerWaveFrequencyCube cutoff) radius time+
              NativeWindowConvectionCutoffTrace.lowPressureWork seed (integerWaveFrequencyCube cutoff) radius time+
              energy seed (integerWaveFrequencyCube cutoff) radius time+epsilon := by
  obtain ⟨space,spatial⟩ := source_cross_bound seed horizon nonnegative
  obtain ⟨clock,temporal⟩ := timeWork_uniform seed horizon nonnegative epsilon positive
  refine ⟨max space clock,fun radius above cutoff covered L cover time inside => ?_⟩
  have small := spatial radius ((le_max_left _ _).trans above) cutoff ((le_max_left _ _).trans covered) L cover time inside
  have scaled := mul_le_mul_of_nonneg_left ((neg_le_abs _).trans small) (show 0 ≤ 2*nu.coeff from by positivity [nu.coeff_pos])
  have gradient := mul_le_mul_of_nonneg_left
    (NativeWindowTraceGradient.source_gradient_bound seed time (integerWaveFrequencyCube cutoff) (cube_closed cutoff))
      (show 0 ≤ nu.coeff/2 from by positivity [nu.coeff_pos])
  have timePaid := temporal radius ((le_max_right _ _).trans above) cutoff ((le_max_right _ _).trans covered) time inside
  have signed := neg_le_abs (timeWork seed (integerWaveFrequencyCube cutoff) radius time)
  rw [(NativeWindowConvectionCutoffTrace.energy_generator seed (integerWaveFrequencyCube cutoff) radius time inside.1 (cube_closed cutoff)).deriv,
    NativeWindowConvectionCutoffTrace.heatWork_identity seed (integerWaveFrequencyCube cutoff) radius time (cube_closed cutoff)]
  nlinarith only [scaled,gradient,timePaid,signed]

theorem original_energy_le (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    NativeWindowTraceEnergy.energy seed F radius time≤2*energy seed F radius time+
      ‖∑ i : Coordinate,NativeWindowConvectionCutoffAction.primitiveField seed F 0 time i i‖^2 := by
  have identity := NativeWindowConvectionCutoffTrace.old_trace_difference seed F radius time
  have same : NativeWindowTraceEnergy.relative seed F radius time=relative seed F radius time-
      ∑ i : Coordinate,NativeWindowConvectionCutoffAction.primitiveField seed F 0 time i i := by rw [identity]; abel
  have bounded := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (relative seed F radius time)
    (∑ i : Coordinate,NativeWindowConvectionCutoffAction.primitiveField seed F 0 time i i)) 2
  rw [NativeWindowTraceEnergy.energy,same]
  unfold energy
  nlinarith only [bounded,sq_nonneg (‖relative seed F radius time‖-
    ‖∑ i : Coordinate,NativeWindowConvectionCutoffAction.primitiveField seed F 0 time i i‖)]

theorem original_energy_uniform (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) : ∃ low : ℕ,∀ cutoff ≥ low,∀ radius : ℕ,∀ time,time∈Icc 0 horizon →
      NativeWindowTraceEnergy.energy seed (integerWaveFrequencyCube cutoff) radius time≤
        2*energy seed (integerWaveFrequencyCube cutoff) radius time+epsilon := by
  obtain ⟨low,paid⟩ := NativeWindowConvectionCutoffWindow.primitive_small seed 0 horizon nonnegative (Real.sqrt epsilon/3) (by positivity)
  refine ⟨low,fun cutoff above radius time inside => (original_energy_le seed _ radius time).trans ?_⟩
  apply add_le_add_right
  have normBound : ‖∑ i : Coordinate,NativeWindowConvectionCutoffAction.primitiveField seed (integerWaveFrequencyCube cutoff) 0 time i i‖≤Real.sqrt epsilon := by
    have row (i : Coordinate) : ‖NativeWindowConvectionCutoffAction.primitiveField seed (integerWaveFrequencyCube cutoff) 0 time i i‖≤Real.sqrt epsilon/3 := by
      rw [NativeWindowConvectionCutoffAction.primitiveField_norm]
      exact (paid cutoff above time inside i i).le
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ => row i).trans_eq (by simp; ring))
  have squared := pow_le_pow_left₀ (norm_nonneg _) normBound 2
  simpa only [Real.sq_sqrt positive.le] using squared

end
end SaturationMonoid.NavierStokes.NativeWindowConvectionCutoffPayment

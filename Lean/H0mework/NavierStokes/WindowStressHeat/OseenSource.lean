import H0mework.NavierStokes.WindowStressHeat.OseenTest

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowStressOseenSource
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWindowOperatorGreen NativeConvectionFlux
open NativeWholeH1Mixed NativeWholeH1Approximation NativeUnheatedSourceQuadraticApprox
noncomputable section
variable {nu : Viscosity}

def load (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : physicalSpace (modes radius) :=
  restrict radius (physicalSource seed time)

def advector (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : ComplexVorticityHilbertState :=
  curlLift (modes radius) (load radius seed time).1

theorem advector_reality (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    FiniteStateFourierReality (advector radius seed time) :=
  curlLift_reality (modes radius) (modes_closed radius) _ (physical_reality (fun {_} member => modes_closed radius _ member) _)

theorem advector_supported (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (outside : wave ∉ modes radius) : advector radius seed time wave = 0 := by
  simp only [advector,curlLift,finiteComplexVorticityState_apply,if_neg outside]

theorem advector_velocity (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    wholeBiotSavartVelocityState (advector radius seed time) = (load radius seed time).1 := by
  apply lp.ext
  funext wave
  rw [wholeBiotSavartVelocityState_apply]
  by_cases member : wave ∈ modes radius
  · exact curlLift_reads (modes radius) (modes_zero radius) _ (physical_transverse _) wave member
  · rw [finiteStateVelocityCoefficient,advector_supported radius seed time wave member,physical_supported _ wave member]
    simp [biotSavartVelocityCoefficient]

def K (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) : Module.End ℝ (physicalSpace (modes radius)) :=
  convection (modes radius) (modes_zero radius) (modes_closed radius) nu (advector radius seed time) (advector_reality radius seed time)

theorem action_row (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) :
    (K radius seed time (load radius seed time)).1 wave = if wave ∈ modes radius then
      NativeTimeJetCarrier.projectedDivergenceCLM wave (NativeHigherTimeJets.mixedFlux (load radius seed time).1 (load radius seed time).1 wave)
    else 0 := by
  by_cases member : wave ∈ modes radius
  · rw [if_pos member]
    have split := congrArg (fun action : Module.End ℝ (physicalSpace (modes radius)) =>
      (action (load radius seed time)).1 wave)
      (operator_split (modes radius) (modes_zero radius) (modes_closed radius) nu
        (advector radius seed time) (advector_reality radius seed time))
    change frozenOperator (modes radius) nu (advector radius seed time) (load radius seed time).1 wave =
      -nu.coeff • (laplacian (modes radius) (modes_zero radius) (modes_closed radius) nu (load radius seed time)).1 wave+
        (K radius seed time (load radius seed time)).1 wave at split
    rw [laplacian_row,operator_stress_row (modes radius) nu (advector radius seed time) (load radius seed time).1
      (advector_supported radius seed time) (physical_supported _) (physical_transverse _) wave member
        (fun zero => modes_zero radius (zero ▸ member)),advector_velocity] at split
    simp only [smul_smul] at split
    have recovered := congrArg (fun value : ComplexCoordinateVector => value+(nu.coeff*integerWaveViscousMultiplier wave) • (load radius seed time).1 wave) split
    simp only [sub_add_cancel,neg_mul,neg_smul] at recovered
    convert! recovered.symm using 1
    abel
  · rw [if_neg member]
    exact physical_supported _ wave member

theorem action_original (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (wave : IntegerWavevector) (coordinate : Coordinate) (member : wave ∈ modes radius) :
    (K radius seed time (load radius seed time)).1 wave coordinate =
      NativeUnheatedTriadRows.decode wave coordinate (value radius seed time) := by
  rw [action_row,if_pos member,NativeWindowStressOseenApprox.projected_action_row,project_whole]
  rfl

theorem source_commutator (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (observation time : ℝ)
    (F : Finset IntegerWavevector) :
    let T := NativeWindowStressOseenTest.operator seed observation (modes radius) F
    let U := load radius seed time
    2*pairing (modes radius) (K radius seed time U) (T U) =
      pairing (modes radius) U (T (K radius seed time U)-K radius seed time (T U)) :=
  NativeWindowStressOseenTest.convection_work seed observation (modes radius) F (modes_zero radius) (modes_closed radius)
    (advector radius seed time) (advector_reality radius seed time) (load radius seed time)

theorem evaluate_load (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (cover : ∀ wave ∈ F, wave ≠ 0 → wave ∈ modes radius) (coordinate : Coordinate) :
    NativeWindowStressOseenTest.evaluate (modes radius) F coordinate (load radius seed time) =
      NativeWindowStressHeatTime.field seed F coordinate time := by
  rw [NativeWindowStressOseenTest.evaluate_apply,NativeWindowStressHeatTime.field,NativeWindowStressHeatBalance.read_apply]
  apply Finset.sum_congr rfl
  intro wave member
  apply congrArg (NativeWindowStressHeatBalance.basis wave)
  rw [show NativeUnheatedTriadRows.decode wave coordinate (NativeUnheatedGlobalNegativeOne.state seed time) =
      NativeEndpointVelocityCarrier.wholeVelocity (NativeUnifiedCompleteSource.source seed time).fst wave coordinate from
    NativeUnheatedTriadRows.velocity_original seed time wave coordinate]
  by_cases zero : wave = 0
  · simp only [zero,physical_supported _ 0 (modes_zero radius),Pi.zero_apply,NativeEndpointVelocityCarrier.wholeVelocity_zero]
  · change (restrict radius (physicalSource seed time)).1 wave coordinate = _
    rw [restrict_row,if_pos (cover wave member zero),physicalSource,dif_pos nonnegative]
    rfl

theorem evaluate_action (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F : Finset IntegerWavevector) (cover : ∀ wave ∈ F, wave ≠ 0 → wave ∈ modes radius) (coordinate : Coordinate) :
    NativeWindowStressOseenTest.evaluate (modes radius) F coordinate (K radius seed time (load radius seed time)) =
      NativeWindowStressHeatTime.read F coordinate (value radius seed time) := by
  rw [NativeWindowStressOseenTest.evaluate_apply,NativeWindowStressHeatBalance.read_apply]
  apply Finset.sum_congr rfl
  intro wave member
  apply congrArg (NativeWindowStressHeatBalance.basis wave)
  by_cases zero : wave = 0
  · simp only [zero,physical_supported _ 0 (modes_zero radius),Pi.zero_apply,
      NativeUnheatedTriadRows.decode_apply,NativeEndpointVelocityCarrier.wholeVelocity_zero,smul_zero]
  · exact action_original radius seed time wave coordinate (cover wave member zero)

theorem pair_original (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (cover : ∀ wave ∈ F, wave ≠ 0 → wave ∈ modes radius) (output input : Coordinate) :
    NativeWindowStressOseenApprox.pair radius seed time F output input =
      NativeWindowStressOseenTest.evaluate (modes radius) F output (K radius seed time (load radius seed time))*
        NativeWindowStressOseenTest.evaluate (modes radius) F input (load radius seed time)+
      NativeWindowStressOseenTest.evaluate (modes radius) F input (K radius seed time (load radius seed time))*
        NativeWindowStressOseenTest.evaluate (modes radius) F output (load radius seed time) := by
  rw [evaluate_action radius seed time F cover output,evaluate_action radius seed time F cover input,
    evaluate_load radius seed time nonnegative F cover input,evaluate_load radius seed time nonnegative F cover output]
  simp only [NativeWindowStressOseenApprox.pair,NativeWindowStressOseenApprox.pairRead_apply,NativeWindowStressHeatTime.field_original]

def instant (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (time : ℝ) : ℝ := ∑ output : Coordinate, ∑ input : Coordinate,
  NativeWindowStressOseenTest.mean (NativeWindowFiniteGramFourier.stress seed observation F output input*
    NativeWindowStressOseenApprox.pair radius seed time F output input)

theorem instant_commutator (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (observation time : ℝ) (nonnegative : 0 ≤ time)
    (F : Finset IntegerWavevector) (cover : ∀ wave ∈ F, wave ≠ 0 → wave ∈ modes radius) :
    instant radius seed observation F time =
      let T := NativeWindowStressOseenTest.operator seed observation (modes radius) F
      let U := load radius seed time
      pairing (modes radius) U (T (K radius seed time U)-K radius seed time (T U)) := by
  rw [← source_commutator]
  have same : instant radius seed observation F time =
      NativeWindowStressOseenTest.form seed observation (modes radius) F (K radius seed time (load radius seed time)) (load radius seed time)+
        NativeWindowStressOseenTest.form seed observation (modes radius) F (load radius seed time) (K radius seed time (load radius seed time)) := by
    simp only [instant,pair_original radius seed time nonnegative F cover,mul_add,map_add,Finset.sum_add_distrib,
      NativeWindowStressOseenTest.form_apply]
    congr 1
    · apply Finset.sum_congr rfl
      intro output _
      apply Finset.sum_congr rfl
      intro input _
      apply congrArg NativeWindowStressOseenTest.mean
      ring
    · apply Finset.sum_congr rfl
      intro output _
      apply Finset.sum_congr rfl
      intro input _
      apply congrArg NativeWindowStressOseenTest.mean
      ring
  rw [NativeWindowStressOseenTest.form_symmetric seed observation (modes radius) F
    (load radius seed time) (K radius seed time (load radius seed time))] at same
  rw [← NativeWindowStressOseenTest.operator_pairing] at same
  linarith [same]

open Filter Set MeasureTheory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget

theorem cover_eventually (F : Finset IntegerWavevector) :
    ∀ᶠ radius : ℕ in atTop, ∀ wave ∈ F, wave ≠ 0 → wave ∈ modes radius := by
  filter_upwards [(tendsto_atTop.1 integerWaveFrequencyCube_tendsto_atTop) F] with radius covered wave member nonzero
  exact Finset.mem_erase.mpr ⟨nonzero,covered member⟩

theorem pair_integrable (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector)
    (output input : Coordinate) (a b : ℝ) (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    IntervalIntegrable (fun time => NativeWindowStressOseenApprox.pair radius seed time F output input) volume a b := by
  have source : IntegrableOn (NativeUnheatedSourceGradient.mass seed) (Set.uIcc a b) (volume : Measure ℝ) :=
    (show IntegrableOn (NativeUnheatedSourceGradient.mass seed) (Icc 0 (max a b)) (volume : Measure ℝ) from
      NativeUnheatedSourceGradient.mass_integrable seed (max a b) (a0.trans (le_max_left _ _))).mono_set
      (fun _ inside => ⟨(le_min a0 b0).trans inside.1,inside.2⟩)
  have paid : IntegrableOn (fun time => NativeWindowStressOseenApprox.pair radius seed time F output input)
      (uIcc a b) (volume : Measure ℝ) :=
    (source.const_mul (NativeWindowStressOseenApprox.cap seed F output input)).mono'
      (NativeWindowStressOseenApprox.pair_measurable radius seed F output input).restrict (by
        filter_upwards [ae_restrict_of_ae (NativeWindowStressOseenApprox.pair_bound_ae seed F output input),
          ae_restrict_mem measurableSet_uIcc] with time bound inside
        exact bound ((le_min a0 b0).trans inside.1) radius)
  exact paid.intervalIntegrable

open NativePhysicalFourier NativeUnheatedStressPairEvolution
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem work_integral (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (F : Finset IntegerWavevector) : NativeWindowStressOseenApprox.work radius seed observation F =
      ∫ time in observation+1..observation+2, kernelWeight 0 observation 0 time*instant radius seed observation F time := by
  let S (output input : Coordinate) := NativeWindowFiniteGramFourier.stress seed observation F output input
  let test (output input : Coordinate) : C(Torus,ℝ) →L[ℝ] ℝ :=
    (innerSL ℝ (NativeWindowStressHeatSource.physical (S output input))).comp NativeWindowStressHeatSource.physical
  have read (output input : Coordinate) (field : C(Torus,ℝ)) : test output input field =
      NativeWindowStressOseenTest.mean (S output input*field) := by
    change inner ℝ (NativeWindowStressHeatSource.physical (S output input)) (NativeWindowStressHeatSource.physical field) = _
    rw [NativeWindowStressHeatSource.physical_inner,NativeWindowStressOseenTest.mean_apply]
    rfl
  have q (output input : Coordinate) := (pair_integrable radius seed F output input (observation+1) (observation+2)
    (by linarith) (by linarith)).continuousOn_smul (kernelWeight_continuous 0 observation 0).continuousOn
  have scalar (output input : Coordinate) : IntervalIntegrable (fun time => kernelWeight 0 observation 0 time*
      NativeWindowStressOseenTest.mean (S output input*NativeWindowStressOseenApprox.pair radius seed time F output input))
      volume (observation+1) (observation+2) := by
    have mapped : IntervalIntegrable (fun time => test output input
        (kernelWeight 0 observation 0 time • NativeWindowStressOseenApprox.pair radius seed time F output input))
        volume (observation+1) (observation+2) :=
      ⟨(test output input).integrable_comp (q output input).1,(test output input).integrable_comp (q output input).2⟩
    simpa only [read,mul_smul_comm,map_smul,smul_eq_mul] using mapped
  have row (output input : Coordinate) : inner ℝ
      (NativeWindowStressHeatBalance.sigma seed F output input observation)
      (NativeWindowStressHeatSource.physical (NativeWindowStressOseenApprox.window radius seed observation F output input)) =
      ∫ time in observation+1..observation+2, kernelWeight 0 observation 0 time*
        NativeWindowStressOseenTest.mean (S output input*NativeWindowStressOseenApprox.pair radius seed time F output input) := by
    simp only [NativeWindowStressHeatBalance.sigma,NativeWindowStressOseenApprox.window,map_neg,inner_neg_neg]
    change test output input (∫ time in observation+1..observation+2, _) = _
    rw [← (test output input).intervalIntegral_comp_comm (q output input)]
    simp only [read,mul_smul_comm,map_smul,smul_eq_mul]
  have total (output : Coordinate) : IntervalIntegrable (fun time => ∑ input : Coordinate,
      kernelWeight 0 observation 0 time*NativeWindowStressOseenTest.mean
        (S output input*NativeWindowStressOseenApprox.pair radius seed time F output input))
      volume (observation+1) (observation+2) := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun input _ => scalar output input)
  simp only [NativeWindowStressOseenApprox.work,row,instant,Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum (fun output _ => total output)]
  apply Finset.sum_congr rfl
  intro output _
  exact (intervalIntegral.integral_finsetSum (fun input _ => scalar output input)).symm

def commutatorWork (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector) : ℝ :=
  ∫ time in observation+1..observation+2, kernelWeight 0 observation 0 time*
    let T := NativeWindowStressOseenTest.operator seed observation (modes radius) F
    let U := load radius seed time
    pairing (modes radius) U (T (K radius seed time U)-K radius seed time (T U))

theorem work_commutator (radius : ℕ) (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (F : Finset IntegerWavevector) (cover : ∀ wave ∈ F, wave ≠ 0 → wave ∈ modes radius) :
    NativeWindowStressOseenApprox.work radius seed observation F = commutatorWork radius seed observation F := by
  rw [work_integral radius seed observation nonnegative F,commutatorWork]
  apply intervalIntegral.integral_congr
  intro time inside
  have positive : 0 ≤ time := by
    rw [Set.uIcc_of_le (by linarith : observation+1 ≤ observation+2)] at inside
    linarith [inside.1]
  dsimp only
  rw [instant_commutator radius seed observation time positive F cover]

theorem actual_work_limit (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0 ≤ observation)
    (F : Finset IntegerWavevector) : Tendsto (fun radius => commutatorWork radius seed observation F) atTop
      (𝓝 (NativeWindowStressHeatBalance.nonlinearWork seed observation F)) := by
  apply (NativeWindowStressOseenApprox.work_tendsto seed observation nonnegative F).congr'
  filter_upwards [cover_eventually F] with radius cover
  exact work_commutator radius seed observation nonnegative F cover

end
end SaturationMonoid.NavierStokes.NativeWindowStressOseenSource
